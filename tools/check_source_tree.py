#!/usr/bin/env python3
"""Static source-distribution checks. Does not invoke Lean or Lake."""
from __future__ import annotations

import ast
from collections import Counter
import json
import hashlib
from pathlib import Path, PurePosixPath
import re
import subprocess

from lean_source import imports

ROOT_FILES = {
    '.gitignore', 'README.md', 'BUILDING.md', 'CONTRIBUTING.md', 'CODE_OF_CONDUCT.md',
    'SECURITY.md', 'RING_STATUS.md', 'LICENSE', 'CITATION.cff', 'TetraStereo.lean',
    'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'source-modules.json',
}
TOOLS = {'build_lean_project_bounded.py', 'lean_source.py', 'check_source_tree.py'}
ASSET_FILES = {'assets/stereolib-banner.svg', 'assets/two-reference-fixture.svg'}
AUXILIARY_FILES = {
    'docs/ring-evaluator.md',
    'tools/centres10/Centres10.java',
    'tools/centres10/analyze.lean',
    'tools/centres10/release-1.0.json',
    'tools/centres10/run_pinned.py',
    'tools/centres10/setup.sh',
    'validation/ring-chronology/Alkoxyaziridine.lean',
    'validation/ring-chronology/AntipodalCyclohexanes.lean',
    'validation/ring-chronology/AtomicMetricStore.lean',
    'validation/ring-chronology/AtomicNeighborClass.lean',
    'validation/ring-chronology/AuditReport.lean',
    'validation/ring-chronology/AutomaticRefusal.lean',
    'validation/ring-chronology/BridgeheadTopology.lean',
    'validation/ring-chronology/CentresAuxiliaryDistance.java',
    'validation/ring-chronology/CentresEvaluation.lean',
    'validation/ring-chronology/CentresFusedLigands.java',
    'validation/ring-chronology/CentresOriginMetricSpiro.java',
    'validation/ring-chronology/CentresOxaziridineRoot.java',
    'validation/ring-chronology/CentresProbe.java',
    'validation/ring-chronology/CentresPublishedMetric.java',
    'validation/ring-chronology/CentresRule1bReroot.java',
    'validation/ring-chronology/CentresSiteMetrics.java',
    'validation/ring-chronology/CentresSpiroCasing.lean',
    'validation/ring-chronology/CentresSpiroSource.lean',
    'validation/ring-chronology/ChemicalRules.lean',
    'validation/ring-chronology/ConstitutionalSpheres.lean',
    'validation/ring-chronology/CrossParentAllHands.spt',
    'validation/ring-chronology/DecalinJunctions.lean',
    'validation/ring-chronology/DeepMarkedSource.lean',
    'validation/ring-chronology/DiaziridineCarbon.lean',
    'validation/ring-chronology/DimethylChloroaziridine.lean',
    'validation/ring-chronology/DiphosphaneSignedWidths.mol',
    'validation/ring-chronology/DiphosphaneSignedWidths.spt',
    'validation/ring-chronology/DiscoveredReports.lean',
    'validation/ring-chronology/DistortedLigandTie.lean',
    'validation/ring-chronology/EmitReport.lean',
    'validation/ring-chronology/EqualDistanceSource.lean',
    'validation/ring-chronology/ExportInputs.lean',
    'validation/ring-chronology/Figure14AllOut.mol',
    'validation/ring-chronology/Figure14Frozen.lean',
    'validation/ring-chronology/Figure14Jmol.spt',
    'validation/ring-chronology/Figure14Parity.lean',
    'validation/ring-chronology/FigureEightScores.lean',
    'validation/ring-chronology/FiniteExchange.lean',
    'validation/ring-chronology/FullPathReport.lean',
    'validation/ring-chronology/FullPathSpiro.lean',
    'validation/ring-chronology/FusedCarbinol.lean',
    'validation/ring-chronology/GlobalLigandComparison.lean',
    'validation/ring-chronology/GraphDerivationIndependence.lean',
    'validation/ring-chronology/GroupedCentreReport.lean',
    'validation/ring-chronology/GroupedChemicalControls.lean',
    'validation/ring-chronology/GroupedStereo.lean',
    'validation/ring-chronology/HansonFigureEight.lean',
    'validation/ring-chronology/ImplicitBondOrder.lean',
    'validation/ring-chronology/IsotopeAssignment.lean',
    'validation/ring-chronology/LayeredPhosphorusBranches.lean',
    'validation/ring-chronology/LayeredPhosphorusBranches.spt',
    'validation/ring-chronology/LigandExchange.lean',
    'validation/ring-chronology/LocalRuleCoverage.lean',
    'validation/ring-chronology/NumericPairReport.lean',
    'validation/ring-chronology/OccurrenceStereo.lean',
    'validation/ring-chronology/OriginMetricRaw.lean',
    'validation/ring-chronology/OriginMetricSpiro.lean',
    'validation/ring-chronology/OriginMetricSpiro.mol',
    'validation/ring-chronology/OriginMetricSpiro.spt',
    'validation/ring-chronology/OriginOrderDomain.lean',
    'validation/ring-chronology/OriginTripleStore.lean',
    'validation/ring-chronology/OriginTwinStore.lean',
    'validation/ring-chronology/OriginTwinVS084.lean',
    'validation/ring-chronology/OriginVS279.lean',
    'validation/ring-chronology/OxaziridineAuxiliary.lean',
    'validation/ring-chronology/OxaziridineRootFrames.lean',
    'validation/ring-chronology/PairedCyclopropylDonors.mol',
    'validation/ring-chronology/Perhydrotriphenylene.lean',
    'validation/ring-chronology/PhosphaneOxirane.lean',
    'validation/ring-chronology/PlanarOxiraneHydrogen.lean',
    'validation/ring-chronology/PyramidalPhosphaneOxirane.mol',
    'validation/ring-chronology/PyramidalPhosphaneOxirane.spt',
    'validation/ring-chronology/RankedReferences.lean',
    'validation/ring-chronology/RawRenumbering.lean',
    'validation/ring-chronology/RecursivePromotions.lean',
    'validation/ring-chronology/ReferenceDerivations.lean',
    'validation/ring-chronology/ReferenceSelectionCut.lean',
    'validation/ring-chronology/ReferenceVoteRing.lean',
    'validation/ring-chronology/ResidualMarkedCage.lean',
    'validation/ring-chronology/ResidualMarkedPairs.lean',
    'validation/ring-chronology/ResidualPhosphorusBranches.lean',
    'validation/ring-chronology/ResidualPhosphorusBranches.mol',
    'validation/ring-chronology/ResidualPhosphorusBranches.spt',
    'validation/ring-chronology/RingGeometryForcing.lean',
    'validation/ring-chronology/RootReturns.lean',
    'validation/ring-chronology/Rule2RealMass.lean',
    'validation/ring-chronology/Rule4aPublicSource.lean',
    'validation/ring-chronology/Rule4bCrossParent.lean',
    'validation/ring-chronology/Rule4bCrossParent.mol',
    'validation/ring-chronology/Rule4bCrossParent.spt',
    'validation/ring-chronology/SourceComparisonAgreement.lean',
    'validation/ring-chronology/SparseTwinReport.lean',
    'validation/ring-chronology/SphereQueue.lean',
    'validation/ring-chronology/SpiroOxaziridine.lean',
    'validation/ring-chronology/StereoReferenceSwap.lean',
    'validation/ring-chronology/StibaneInventory.lean',
    'validation/ring-chronology/UnitClasses.lean',
    'validation/ring-chronology/VS242PublicReport.lean',
    'validation/ring-chronology/VS300SingleAdmission.lean',
    'validation/ring-chronology/centres-rule1b-distance.patch',
    'validation/ring-chronology/check_decalin_rule5.py',
    'validation/ring-chronology/check_equal_distance_source.py',
    'validation/ring-chronology/check_figure14_regeneration.py',
    'validation/ring-chronology/check_fused_jmol.py',
    'validation/ring-chronology/check_paired_cyclopropyl_donors.py',
    'validation/ring-chronology/check_promotion_topology.py',
    'validation/ring-chronology/check_site_metrics.py',
    'validation/ring-chronology/check_vs242_cross_band.py',
    'validation/ring-chronology/check_vs242_gate_patterns.py',
    'validation/ring-chronology/check_vs265_three_depths.py',
    'validation/ring-chronology/check_vs300_bond_order.py',
    'validation/ring-chronology/expected.txt',
    'validation/ring-chronology/figure8_geometry.py',
    'validation/ring-chronology/figure8_orbit_replay.py',
    'validation/ring-chronology/figure8_stereoisomers.py',
    'validation/ring-chronology/generate_deep_marked_source.py',
    'validation/ring-chronology/hanson_figure8_sdf.py',
    'validation/ring-chronology/mirror-root.req',
    'validation/ring-chronology/original-root.req',
    'validation/ring-chronology/published_metric_screen.py',
    'validation/ring-chronology/replay-centres.sh',
    'validation/ring-chronology/rule1b_reroot.py',
    'validation/ring-chronology/test_pinned_runner.py',
    'validation/ring-chronology/vs242_branch_words.py',
}

EMBEDDED_INPUTS = {
    'TetraStereo/Engine/CentresRing.lean': (
        'tools/centres10/run_pinned.py', 'tools/centres10/release-1.0.json',
    ),
}
MODULE_NAME = re.compile(r"TetraStereo(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def allowed(path: str) -> bool:
    parts = PurePosixPath(path).parts
    if not parts or '..' in parts or path.startswith('/'):
        return False
    return (
        path in ROOT_FILES
        or path in AUXILIARY_FILES
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


def embedded_input_errors(root: Path, tracked: set[str]) -> list[str]:
    """Verify the reviewed embedded runtime assets and their build-key fingerprints."""
    errors = []
    for source, assets in EMBEDDED_INPUTS.items():
        if source not in tracked:
            continue
        text = (root / source).read_text(encoding='utf-8')
        for asset in assets:
            target = root / asset
            if asset not in tracked or target.is_symlink() or not target.is_file():
                errors.append(f'Missing tracked embedded input: {source} -> {asset}')
                continue
            relative = '../../' + asset
            if f'include_str "{relative}"' not in text:
                errors.append(f'Missing reviewed include_str binding: {source} -> {asset}')
            digest = hashlib.sha256(target.read_bytes()).hexdigest()
            if f'-- {target.name} SHA-256 {digest}\n' not in text:
                errors.append(f'Stale embedded input fingerprint: {source} -> {asset}')
    return errors


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    entries = subprocess.check_output(['git', '-C', str(root), 'ls-files', '-s', '-z'])
    errors = []
    sources = {}
    auxiliary_sources = {}
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
            if path == 'TetraStereo.lean' or path.startswith('TetraStereo/'):
                sources[path[:-5].replace('/', '.')] = text
            else:
                auxiliary_sources[path] = text
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
    for path, text in auxiliary_sources.items():
        for dependency in imports(text):
            if (dependency == 'TetraStereo' or dependency.startswith('TetraStereo.')) and dependency not in sources:
                errors.append(f'Missing auxiliary import: {path} -> {dependency}')
    errors.extend(embedded_input_errors(root, set(paths)))
    if errors:
        print('\n'.join(errors))
        return 1
    print(f'Source checks passed: {len(paths)} files, {len(sources)} Lean modules; no Lean build run.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
