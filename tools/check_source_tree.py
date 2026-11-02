#!/usr/bin/env python3
"""Static source-distribution checks. Does not invoke Lean or Lake."""
from __future__ import annotations

import ast
from collections import Counter
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

from lean_source import imports

ROOT_FILES = {
    '.gitignore', 'README.md', 'BUILDING.md', 'CONTRIBUTING.md', 'CODE_OF_CONDUCT.md',
    'SECURITY.md', 'LICENSE', 'CITATION.cff', 'TetraStereo.lean',
    'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'source-modules.json',
}
TOOLS = {'build_lean_project_bounded.py', 'lean_source.py', 'check_source_tree.py'}
ASSET_FILES = {'assets/stereolib-banner.svg', 'assets/two-reference-fixture.svg'}
MODULE_NAME = re.compile(r"TetraStereo(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def allowed(path: str) -> bool:
    parts = PurePosixPath(path).parts
    if not parts or '..' in parts or path.startswith('/'):
        return False
    return (
        path in ROOT_FILES
        or path in ASSET_FILES
        or (parts[0] == 'TetraStereo' and path.endswith('.lean'))
        or (len(parts) == 2 and parts[0] == 'tools' and parts[1] in TOOLS)
        or (len(parts) == 2 and parts[0] == 'tests' and parts[1].startswith('test_')
            and parts[1].endswith('.py'))
        or (len(parts) == 3 and parts[:2] in
            (('.github', 'workflows'), ('.github', 'ISSUE_TEMPLATE')) and path.endswith('.yml'))
    )


def missing_imports(sources: dict[str, str]) -> list[tuple[str, str]]:
    missing = []
    for module, text in sources.items():
        for dependency in imports(text):
            if (dependency == 'TetraStereo' or dependency.startswith('TetraStereo.')):
                if dependency not in sources:
                    missing.append((module, dependency))
    return missing


def inventory_errors(text: str, source_modules: set[str]) -> list[str]:
    """Check the public module inventory against source modules, excluding the umbrella."""
    try:
        document = json.loads(text)
    except json.JSONDecodeError as error:
        return [f'Invalid source-modules.json: {error}']
    if not isinstance(document, dict) or set(document) != {'version', 'modules'}:
        return ['Invalid source-modules.json: expected only version and modules fields']
    version = document['version']
    if not isinstance(version, int) or isinstance(version, bool) or version != 1:
        return ['Invalid source-modules.json: version must be the integer 1']
    modules = document['modules']
    if not isinstance(modules, list) or not modules:
        return ['Invalid source-modules.json: modules must be a nonempty array']
    if any(not isinstance(module, str) or MODULE_NAME.fullmatch(module) is None
           for module in modules):
        return ['Invalid source-modules.json: modules must contain public TetraStereo.* names']
    duplicates = sorted(module for module, count in Counter(modules).items() if count > 1)
    if duplicates:
        return [f'Duplicate inventory module: {module}' for module in duplicates]
    expected = set(modules)
    actual = source_modules - {'TetraStereo'}
    return (
        [f'Missing inventory module: {module}' for module in sorted(expected - actual)]
        + [f'Unexpected source module: {module}' for module in sorted(actual - expected)]
    )


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    entries = subprocess.check_output(['git', '-C', str(root), 'ls-files', '-s', '-z'])
    errors = []
    sources = {}
    paths = []
    inventory_text = None
    for entry in entries.split(b'\0'):
        if not entry:
            continue
        metadata, raw_path = entry.split(b'\t', 1)
        mode, _, stage = metadata.split()
        path = raw_path.decode('utf-8')
        paths.append(path)
        full = root / path
        if mode not in (b'100644', b'100755') or stage != b'0' or full.is_symlink():
            errors.append(f'Unsupported file mode/stage: {path}')
            continue
        if not allowed(path):
            errors.append(f'Outside source-distribution allowlist: {path}')
            continue
        try:
            text = full.read_text(encoding='utf-8')
        except (OSError, UnicodeError) as error:
            errors.append(f'Cannot read tracked file: {path}: {error}')
            continue
        if path == 'source-modules.json':
            inventory_text = text
        elif path.endswith('.lean') and path != 'lakefile.lean':
            sources[path[:-5].replace('/', '.')] = text
        elif path.endswith('.py'):
            ast.parse(text, filename=path)
        elif path.endswith('.md'):
            for link in re.findall(r'\]\(([^)]+)\)', text):
                if re.match(r'[a-zA-Z][a-zA-Z0-9+.-]*:', link) or link.startswith('#'):
                    continue
                target = link.split('#', 1)[0]
                if target and not (full.parent / target).exists():
                    errors.append(f'Broken document link: {path} -> {link}')
    if not sources:
        errors.append('No tracked Lean modules')
    if inventory_text is None:
        errors.append('Missing tracked source-modules.json inventory')
    else:
        errors.extend(inventory_errors(inventory_text, set(sources)))
    errors.extend(f'Missing import: {module} -> {dependency}'
                  for module, dependency in missing_imports(sources))
    if errors:
        print('\n'.join(errors))
        return 1
    print(f'Source checks passed: {len(paths)} files, {len(sources)} Lean modules; no Lean build run.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
