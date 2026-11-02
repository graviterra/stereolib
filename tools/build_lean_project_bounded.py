#!/usr/bin/env python3
"""Build a selected Lean dependency closure serially.

Run --check first, and execute builds only inside an enforced aggregate memory limit.
This helper does not establish that limit and does not certify chemistry or proof completeness.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).absolute().parent))
import lean_source
from lean_source import imports as lean_imports


IMPORT = re.compile(r"^(?:public\s+)?import\s+(.+?)\s*$")
LEAN_DIAGNOSTIC = re.compile(
    r"^(?:warning|error): (?P<path>[^:]+\.lean):(?P<line>\d+):(?P<column>\d+): (?P<message>.+)$"
)
PROGRESS_VERSION = 2
LEAN_NUM_THREADS = "1"
BUILD_COMMAND = ("lake", "--wfail", "build")
BUILD_CONTEXT_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.lean")


def module_name(source: Path) -> str:
    return ".".join(source.with_suffix("").parts)


def tracked_sources(project_root: Path) -> list[Path]:
    result = subprocess.run(
        ["git", "-C", str(project_root), "ls-files", "TetraStereo.lean", "TetraStereo/*.lean"],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    )
    sources = [Path(line) for line in result.stdout.splitlines() if line]
    if not sources:
        raise ValueError("no tracked TetraStereo Lean modules found")
    missing = [str(source) for source in sources if not (project_root / source).is_file()]
    if missing:
        raise ValueError(f"tracked Lean modules are missing: {', '.join(missing)}")
    return sources


def local_imports(project_root: Path, source: Path, local_modules: set[str]) -> set[str]:
    names = lean_imports((project_root / source).read_text(encoding="utf-8"))
    missing = [name for name in names if
               (name == "TetraStereo" or name.startswith("TetraStereo.")) and name not in local_modules]
    if missing:
        raise ValueError(f"missing local imports in {source}: {', '.join(missing)}")
    return set(names) & local_modules


def topological_plan(project_root: Path, sources: Iterable[Path]) -> list[Path]:
    source_by_module = {module_name(source): source for source in sources}
    dependencies = {
        module: local_imports(project_root, source, set(source_by_module))
        for module, source in source_by_module.items()
    }
    state: dict[str, int] = {}
    plan: list[Path] = []

    def visit(module: str, ancestry: tuple[str, ...]) -> None:
        status = state.get(module, 0)
        if status == 2:
            return
        if status == 1:
            cycle = " -> ".join((*ancestry, module))
            raise ValueError(f"local Lean import cycle: {cycle}")
        state[module] = 1
        for dependency in sorted(dependencies[module]):
            visit(dependency, (*ancestry, module))
        state[module] = 2
        plan.append(source_by_module[module])

    for module in sorted(source_by_module):
        visit(module, ())
    if len(plan) != len(source_by_module) or len(set(plan)) != len(plan):
        raise ValueError("bounded build plan is not an exact source partition")
    return plan


def checkpoint_prefix(plan: list[Path], through_module: str | None) -> list[Path]:
    """Return the dependency-safe plan prefix ending at ``through_module``."""
    if through_module is None:
        return plan
    for index, source in enumerate(plan):
        if module_name(source) == through_module:
            return plan[: index + 1]
    raise ValueError(f"checkpoint module is not in the bounded build plan: {through_module}")


def dependency_plan(
    project_root: Path, plan: list[Path], requested: list[str]
) -> list[Path]:
    """Select the exact local dependency closure, preserving topological order."""
    sources = {module_name(source): source for source in plan}
    selected: set[str] = set()

    def visit(module: str) -> None:
        if module not in sources:
            raise ValueError(f"requested module is not in the bounded build plan: {module}")
        if module in selected:
            return
        selected.add(module)
        for dependency in local_imports(project_root, sources[module], set(sources)):
            visit(dependency)

    for module in requested:
        visit(module)
    return [source for source in plan if module_name(source) in selected]


def build_context_fingerprint(project_root: Path) -> str:
    """Hash every non-source input that can change a bounded Lake build."""
    digest = hashlib.sha256()
    digest.update(f"progress-version:{PROGRESS_VERSION}\n".encode("ascii"))
    digest.update(f"lean-threads:{LEAN_NUM_THREADS}\n".encode("ascii"))
    for argument in BUILD_COMMAND:
        digest.update(b"build-argument\0")
        digest.update(argument.encode("utf-8"))
        digest.update(b"\0")
    builder = Path(__file__)
    digest.update(b"builder\0")
    digest.update(builder.read_bytes())
    digest.update(Path(lean_source.__file__).read_bytes())
    for relative in BUILD_CONTEXT_FILES:
        path = project_root / relative
        digest.update(b"context-file\0")
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
    return digest.hexdigest()


def transitive_fingerprints(
    project_root: Path, plan: list[Path], context_fingerprint: str
) -> dict[str, str]:
    """Hash each source together with the fingerprints of all local direct imports."""
    source_by_module = {module_name(source): source for source in plan}
    local_modules = set(source_by_module)
    fingerprints: dict[str, str] = {}
    for source in plan:
        module = module_name(source)
        digest = hashlib.sha256()
        digest.update(context_fingerprint.encode("ascii"))
        digest.update((project_root / source).read_bytes())
        for dependency in sorted(local_imports(project_root, source, local_modules)):
            digest.update(dependency.encode("utf-8"))
            digest.update(fingerprints[dependency].encode("ascii"))
        fingerprints[module] = digest.hexdigest()
    return fingerprints


def module_artifacts(project_root: Path, source: Path) -> tuple[Path, Path]:
    artifact = project_root / ".lake" / "build" / "lib" / "lean" / source.with_suffix("")
    return artifact.with_suffix(".olean"), artifact.with_suffix(".ilean")


def cache_hit(
    project_root: Path,
    source: Path,
    completed: dict[str, str],
    module: str,
    fingerprint: str,
) -> bool:
    return completed.get(module) == fingerprint and all(
        artifact.is_file() for artifact in module_artifacts(project_root, source)
    )


def load_progress(path: Path) -> dict[str, str]:
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {}
    if not isinstance(document, dict) or document.get("version") != PROGRESS_VERSION:
        return {}
    completed = document.get("completed")
    if not isinstance(completed, dict):
        return {}
    return {
        module: fingerprint
        for module, fingerprint in completed.items()
        if isinstance(module, str) and isinstance(fingerprint, str)
    }


def save_progress(path: Path, completed: dict[str, str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(".tmp")
    temporary.write_text(
        json.dumps({"version": PROGRESS_VERSION, "completed": completed}, sort_keys=True),
        encoding="utf-8",
    )
    temporary.replace(path)


def workflow_escape(value: str) -> str:
    return value.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def emit_failure_annotations(output: str) -> None:
    for line in output.splitlines():
        match = LEAN_DIAGNOSTIC.match(line)
        if match is None:
            continue
        message = workflow_escape(match.group("message"))
        path = workflow_escape(match.group("path"))
        print(
            f"::error file={path},line={match.group('line')},"
            f"col={match.group('column')}::{message}",
            flush=True,
        )


def run_lake_module(project_root: Path, source: Path) -> subprocess.CompletedProcess[str]:
    """Build one module while capping the Lean compiler's internal worker pool."""
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = LEAN_NUM_THREADS
    return subprocess.run(
        [*BUILD_COMMAND, str(source)],
        cwd=project_root,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=environment,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate and print the plan without invoking Lake",
    )
    parser.add_argument(
        "--project-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
    )
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument(
        "--through-module",
        metavar="MODULE",
        help="stop after this module and persist a resumable dependency-safe checkpoint",
    )
    selection.add_argument(
        "--module", action="append", metavar="MODULE",
        help="build only this module and its local dependencies; repeat for several modules",
    )
    arguments = parser.parse_args()
    if not arguments.check and not (arguments.module or arguments.through_module):
        parser.error("execution requires an explicit --module or --through-module selection")

    project_root = arguments.project_root.resolve()
    try:
        plan = topological_plan(project_root, tracked_sources(project_root))
        selected_plan = (
            dependency_plan(project_root, plan, arguments.module)
            if arguments.module else checkpoint_prefix(plan, arguments.through_module)
        )
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"bounded Lean build: {error}", file=sys.stderr)
        return 2

    try:
        context_fingerprint = build_context_fingerprint(project_root)
        fingerprints = transitive_fingerprints(project_root, plan, context_fingerprint)
    except OSError as error:
        print(f"bounded Lean build: cannot fingerprint build context: {error}", file=sys.stderr)
        return 2
    if len(fingerprints) != len(plan):
        print("bounded Lean build: fingerprint ledger is incomplete", file=sys.stderr)
        return 2
    print(f"bounded Lean build: exact topological plan contains {len(plan)} modules", flush=True)
    if arguments.through_module is not None:
        print(
            "bounded Lean build: checkpoint ends at "
            f"[{len(selected_plan)}/{len(plan)}] {arguments.through_module}",
            flush=True,
        )
    if arguments.module:
        print(f"bounded Lean build: dependency selection contains {len(selected_plan)} modules", flush=True)
    if arguments.check:
        if arguments.module:
            for source in selected_plan:
                print(f"  {module_name(source)}")
        return 0
    progress_path = project_root / ".lake" / "bounded-release-progress.json"
    completed = load_progress(progress_path)
    for index, source in enumerate(selected_plan, start=1):
        module = module_name(source)
        fingerprint = fingerprints[module]
        if cache_hit(project_root, source, completed, module, fingerprint):
            print(
                f"bounded Lean build: [{index}/{len(plan)}] cached {source}",
                flush=True,
            )
            continue
        print(f"bounded Lean build: [{index}/{len(plan)}] {source}", flush=True)
        result = run_lake_module(project_root, source)
        print(result.stdout, end="", flush=True)
        if result.returncode != 0:
            emit_failure_annotations(result.stdout)
            return result.returncode
        missing_artifacts = [
            str(path.relative_to(project_root))
            for path in module_artifacts(project_root, source)
            if not path.is_file()
        ]
        if missing_artifacts:
            print(
                "bounded Lean build: Lake succeeded without expected artifacts: "
                + ", ".join(missing_artifacts),
                file=sys.stderr,
            )
            return 2
        completed[module] = fingerprint
        save_progress(progress_path, completed)
    print(
        f"bounded Lean build: completed [{len(selected_plan)}/{len(plan)}] modules",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
