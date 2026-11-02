#!/usr/bin/env python3
"""Regression contract for the bounded Lean build launcher."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = REPO_ROOT / "tools" / "build_lean_project_bounded.py"


def load_builder():
    spec = importlib.util.spec_from_file_location("build_lean_project_bounded", SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class BoundedLeanBuildResourceContractTest(unittest.TestCase):
    def test_dependency_plan_includes_shared_transitive_dependencies_only(self) -> None:
        builder = load_builder()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            files = {
                "TetraStereo/Shared.lean": "import Mathlib\n",
                "TetraStereo/Left.lean": "import TetraStereo.Shared\n",
                "TetraStereo/Right.lean": "import TetraStereo.Shared\n",
                "TetraStereo/Unrelated.lean": "",
                "TetraStereo/Target.lean": "import TetraStereo.Left\nimport TetraStereo.Right\n",
            }
            for name, content in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            plan = builder.topological_plan(root, map(Path, files))
            selected = builder.dependency_plan(root, plan, ["TetraStereo.Target", "TetraStereo.Left"])
            self.assertEqual(set(selected), set(map(Path, files)) - {Path("TetraStereo/Unrelated.lean")})
            self.assertLess(selected.index(Path("TetraStereo/Shared.lean")), selected.index(Path("TetraStereo/Left.lean")))
            self.assertLess(selected.index(Path("TetraStereo/Right.lean")), selected.index(Path("TetraStereo/Target.lean")))

    def test_dependency_plan_rejects_unknown_module(self) -> None:
        builder = load_builder()
        with self.assertRaisesRegex(ValueError, "requested module is not in"):
            builder.dependency_plan(Path("/unused"), [], ["TetraStereo.Missing"])

    def test_module_and_checkpoint_selections_are_mutually_exclusive(self) -> None:
        result = subprocess.run(
            ["python3", str(SCRIPT), "--check", "--module", "TetraStereo.A", "--through-module", "TetraStereo.B"],
            capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn("not allowed with argument", result.stderr)

    def test_checkpoint_prefix_is_dependency_safe_and_inclusive(self) -> None:
        builder = load_builder()
        plan = [
            Path("TetraStereo/Dependency.lean"),
            Path("TetraStereo/Checkpoint.lean"),
            Path("TetraStereo/Tail.lean"),
        ]

        self.assertEqual(
            builder.checkpoint_prefix(plan, "TetraStereo.Checkpoint"),
            plan[:2],
        )
        self.assertIs(builder.checkpoint_prefix(plan, None), plan)

    def test_checkpoint_prefix_rejects_unknown_module(self) -> None:
        builder = load_builder()
        with self.assertRaisesRegex(ValueError, "checkpoint module is not in"):
            builder.checkpoint_prefix(
                [Path("TetraStereo/Only.lean")], "TetraStereo.Missing"
            )

    def test_module_build_forces_one_lean_worker_and_one_project_module(self) -> None:
        builder = load_builder()
        completed = subprocess.CompletedProcess([], 0, stdout="")
        with patch.dict(os.environ, {"PATH": "/test/bin", "LEAN_NUM_THREADS": "32"}, clear=True):
            with patch.object(builder.subprocess, "run", return_value=completed) as run:
                builder.run_lake_module(Path("/project"), Path("TetraStereo/Example.lean"))

        command = run.call_args.args[0]
        environment = run.call_args.kwargs["env"]
        self.assertEqual(command, ["lake", "--wfail", "build", "TetraStereo/Example.lean"])
        self.assertEqual(environment["LEAN_NUM_THREADS"], "1")
        self.assertEqual(environment["PATH"], "/test/bin")

    def test_build_context_invalidates_configuration_builder_and_arguments(self) -> None:
        builder = load_builder()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for relative in builder.BUILD_CONTEXT_FILES:
                (root / relative).write_text(f"{relative}: initial\n", encoding="utf-8")
            replacement_builder = root / "bounded-builder.py"
            replacement_builder.write_text("# version one\n", encoding="utf-8")
            with patch.object(builder, "__file__", str(replacement_builder)):
                baseline = builder.build_context_fingerprint(root)
                (root / "lakefile.lean").write_text("changed\n", encoding="utf-8")
                configured = builder.build_context_fingerprint(root)
                (root / "lakefile.lean").write_text(
                    "lakefile.lean: initial\n", encoding="utf-8"
                )
                replacement_builder.write_text("# version two\n", encoding="utf-8")
                scripted = builder.build_context_fingerprint(root)
                with patch.object(builder, "BUILD_COMMAND", (*builder.BUILD_COMMAND, "--trace")):
                    argued = builder.build_context_fingerprint(root)

        self.assertNotEqual(baseline, configured)
        self.assertNotEqual(baseline, scripted)
        self.assertNotEqual(scripted, argued)

    def test_cache_hit_requires_both_current_module_artifacts(self) -> None:
        builder = load_builder()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = Path("TetraStereo/Example.lean")
            module = builder.module_name(source)
            fingerprint = "current"
            completed = {module: fingerprint}
            olean, ilean = builder.module_artifacts(root, source)
            olean.parent.mkdir(parents=True)

            self.assertFalse(
                builder.cache_hit(root, source, completed, module, fingerprint)
            )
            olean.write_bytes(b"olean")
            self.assertFalse(
                builder.cache_hit(root, source, completed, module, fingerprint)
            )
            ilean.write_bytes(b"ilean")
            self.assertTrue(
                builder.cache_hit(root, source, completed, module, fingerprint)
            )
            self.assertFalse(
                builder.cache_hit(root, source, completed, module, "stale")
            )


if __name__ == "__main__":
    unittest.main()
