# Evaluating tetrahedral rings

The existing grouped API freezes completed auxiliaries during each promotion trial and uses
parent-by-parent Rule 4b traversal. Its rebuilt zero-mass counterpart has an equality theorem
for the complete recursive state and report. A reachable cross-parent witness now shows that
this grouped traversal differs from full-path whole-sphere ordering.
[Counterexample](../validation/ring-chronology/Rule4bCrossParent.lean)

The public `Engine.ringMolecularReportFromRaw?` now uses
[`RingHydrogenReport.fromRaw?`](../TetraStereo/Engine/RingHydrogenReport.lean). It completes
ordinary hydrogens, supplies selected pyramidal frames and requires agreement of the whole
requested report over every admitted orientation of unplaced P–H bonds. Each reading has its
own recursive molecular source derivation, including deeper auxiliary assignments. Request
order, repeats and completed refusals are preserved. The domain theorem explicitly requires
placement admission and agreement; it is not an unconditional success theorem.
[Source equivalence](../TetraStereo/Engine/RingHydrogenReport.lean) ·
[Domain characterization](../TetraStereo/Engine/RingHydrogenReportDomain.lean)

The full-path source theorem and the newer population/inventory connections characterize their
named local priorities and publication rules. The earlier hydrogen/phosphorus failure controls
are repaired. Independent chemical fidelity remains open, including the Rule 1b distance choice
at rerooted auxiliaries described below.

The accumulated-reference regenerated profile and pinned Centres 1.0 adapter remain separately
named procedures. Agreement with any one procedure does not establish agreement with another.

## Lean entry points

Import the selected module rather than building the whole library.

| Task | Entry point | Source |
| --- | --- | --- |
| Admit and evaluate requested zero-based raw atom IDs | `Engine.ringMolecularReportFromRaw?` | [Hydrogen-consensus raw API](../TetraStereo/Engine/RingHydrogenReport.lean) |
| Evaluate requested typed atoms | `Engine.ringMolecularReportForAtoms?` | [Public API](../TetraStereo/Engine/PublicAPI.lean) |
| Evaluate every detected centre / every carbon | `Engine.ringMolecularReport?`, `ringMolecularCarbonReport?` | [Hydrogen-consensus report](../TetraStereo/Engine/RingHydrogenReport.lean) |
| Obtain raw graph / admitted report equivalence | `Engine.ringMolecularReportFromRawExact`, `ringMolecularReportExact` | [Public theorem aliases](../TetraStereo/Engine/PublicAPI.lean) |
| Evaluate the underlying full-path report | `RingFullPathReport.forAtoms?` | [Full-path report](../TetraStereo/Engine/RingFullPathReport.lean) |
| Evaluate the compatible grouped procedure | `Engine.ringGroupedMolecularReport?` | [Public API](../TetraStereo/Engine/PublicAPI.lean) |
| Evaluate the rebuilt zero-duplicate-mass report | `RingRebuiltStereo.report?` | [Rebuilt report](../TetraStereo/Engine/RingRebuiltStereo.lean) |
| Select highest-ranked Rule 4b occurrence references | `RingReferenceVotes.molecular?` | [Reference selector](../TetraStereo/Engine/RingReferenceVotes.lean) |
| Check a sufficient Rule 6 refusal cut | `RingPromotionCut.refusal?` | [Cut certificate](../TetraStereo/Engine/RingPromotionCut.lean) |
| Admit raw or SMILES input and coordinates | `LocalizedChemicalRing.admitRawSpatial?`, `admitSmilesSpatial?` | [Public ring API](../TetraStereo/Engine/LocalizedChemicalRingPublic.lean) |
| Evaluate the regenerated profile | `LocalizedChemicalRing.analyze .accumulatedReferencesRegenerated` | [Public ring API](../TetraStereo/Engine/LocalizedChemicalRingPublic.lean) |
| Evaluate one detected centre | `LocalizedChemicalRing.centerOutcome` | [Centre projection](../TetraStereo/Engine/LocalizedChemicalRingCenterProjection.lean) |
| Obtain unique exact source meaning from admitted coordinates | `existsUnique_exactSourceMeaning_of_coordinates` | [Exact certificate](../TetraStereo/Engine/LocalizedChemicalRingExactCertificate.lean) |
| Evaluate a matched frozen-auxiliary control | `LocalizedChemicalRing.frozenCenterOutcome` | [Frozen execution](../TetraStereo/Engine/LocalizedChemicalRingFrozenExecution.lean) |
| Run or replay pinned Centres | `CentresRing.analyze`, `CentresRing.checkReceipt` | [Centres API](../TetraStereo/Engine/CentresRing.lean) |
| Check recursive molecular comparisons and publications | `CentresRing.Molecular.checkSourceReceipt` | [Molecular derivation](../TetraStereo/Engine/CentresRingDerived.lean) |
| Derive casing from original and reflected priority readings | `CentresRing.MirrorCasing.analyze`, `check` | [Mirror API](../TetraStereo/Engine/CentresRingMirror.lean) |

Import `TetraStereo.Engine.PublicAPI` for the `Engine` aliases. The raw call has the form
`Engine.ringMolecularReportFromRaw? molecule coordinates [0, 2, 0]`. IDs are zero-based;
request order and repeats are preserved. Outer `none` includes structural or coordinate failure,
out-of-range IDs, failed admission of a placement and disagreement between placement reports.
A successful row `(id, none)` records an agreed completed refusal. Agreement is checked over the
whole request, so changing the requested inventory can change whether a request is decided.

The public API materializes ordinary H atoms and explores unplaced P–H orientations. The written
placement and signature theorems relate these readings to finite representatives of the admitted
geometries. Making a uniquely fixed completion explicit preserves the requested result under
the materialization theorem's hypotheses. On hydrogen-complete admitted input, valid IDs and the
stated full/nondegenerate coordinate hypotheses yield a unique report.
[Materialization and totality](../TetraStereo/Engine/RingHydrogenReport.lean) ·
[Written readings](../TetraStereo/Engine/RingWrittenHydrogenReadings.lean) ·
[Placement signatures](../TetraStereo/Engine/RingPlacementSignatures.lean)

Bond-list permutation preserves the literal raw response through this pipeline, including failure
and invalid IDs. The presentation theorem additionally permits stored neighbor order to change
between independently admitted inputs satisfying its graph/coordinate conditions. Import
`PublicAPI` for `ringMolecularReportRawBondOrder`, `ringMolecularReportBondOrder` and
`ringMolecularReportPresentation`. [Presentation proof](../TetraStereo/Engine/RingBondRecordOrder.lean)

The older `Engine.ringGroupedMolecularReport?`, `ringGroupedCarbonReport?`, and their correctness
aliases retain their earlier grouped behavior. They are compatibility entry points, not aliases
for the new full-path molecular report.

These inputs are finite, single-bond, constant-charge molecules with explicit structural
admission. The physical theorems require calibrated nondegenerate coordinates at detected
centres. `coordinatesAdmitted` supplies a separate gate; structural admission alone is insufficient.
Supply coordinates in the raw input's atom order; the public hydrogen pipeline constructs its completed readings. The separately named SMILES/parser interfaces have their own expanded atom order. Refusal is a report entry with
no descriptor; admission, execution or transcript failures are errors.

The exact certificate covers source-priority letters, casing and refusal at every detected root,
under its hypotheses. The [chronology theorem](../TetraStereo/Engine/LocalizedChemicalRingChronologyCertificate.lean)
requires a changed downstream auxiliary reading when frozen and regenerated outcomes differ.
The frozen control freezes auxiliary observations while retaining the underlying comparator,
root discovery, geometry and readback. It is a diagnostic control, not a substitute for Centres.

## Replaying frozen-auxiliary controls

Prepare only the selected fixture's dependencies using [BUILDING.md](../BUILDING.md), inspecting
the bounded helper's `--check` plan first. Run the fixture under an enforced aggregate memory
scope as well. For example, after those dependencies are prepared:

```sh
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 \
  lake env lean --run validation/ring-chronology/ReferenceVoteRing.lean
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 \
  lake env lean --run validation/ring-chronology/ReferenceVoteRing.lean --grouped
```

The [48-atom fixture](../validation/ring-chronology/ReferenceVoteRing.lean) defaults to rebuilt
evaluation. It checks that nine geometric reference occurrences select S by five to four,
and R on reflection. The `--grouped` replay checks the same references with grouped publication.
The [unequal-rank control](../validation/ring-chronology/ReferenceSelectionCut.lean) checks that
junior R occurrences do not outvote a senior S occurrence, and exercises the refusal cut.
The [Figure 14 control](../validation/ring-chronology/Figure14Frozen.lean) checks explicit
absence at both bridgeheads on the all-out and in/out configurations. These are scoped controls;
they do not prove chemical completeness. These commands were documented without a fresh public
compilation during publication.

After preparing the selected full-path dependencies, the report fixture can be run in the same
bounded scope:

```sh
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 \
  lake env lean --run validation/ring-chronology/FullPathReport.lean
```

It checks R/S and refusal on two five-atom spiro inputs, and R/S, R/S and refusal on the three
ring carbons of 1-chloro-2-fluorocyclopropane, including deeper auxiliary publication.
The [cross-parent control](../validation/ring-chronology/Rule4bCrossParent.lean) separately checks
the reachable grouped/full-path discrepancy on its shared molecular file.

## Chemical counterexamples

The earlier public full-path profile failed two admitted chemical controls. The current raw API
repairs both. At the substituted carbon of 1-bromo-1-fluorocyclopropane, the tested zero, partial
and fully explicit H spellings now refuse. The all-explicit phosphorus/oxirane control now gives
carbon s/s and phosphorus R/S then S/R. These regression results do not establish universal
chemical completeness. [Public audit](../validation/ring-chronology/LocalRuleCoverage.lean) ·
[Hydrogen semantics](https://iupac.qmul.ac.uk/BlueBook/P9.html#92010201) ·
[Pyramidal phosphorus](https://iupac.qmul.ac.uk/BlueBook/P9.html#93030401)

After bounded preparation of the selected dependencies, replay with:

```sh
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 \
  lake env lean --run validation/ring-chronology/LocalRuleCoverage.lean --require-conformance
```

The strict flag checks the expected chemical outcomes. Other modes include `--inventory-report`
and `--signed-parent-widths`; the latter checks the mirror-related diphosphane control. The
pinned Jmol phosphorus replay uses
[PyramidalPhosphaneOxirane.spt](../validation/ring-chronology/PyramidalPhosphaneOxirane.spt) and
requires `PHOSPHANE_PASS sRS sSR`. Program agreement is separate from the chemical criterion.

## Rerooted Rule 1b distance

The public convention measures ring-duplicate origins from the original root. The alternative
`Engine.ringActiveOriginReportFromRaw?` measures from each active focus on the retained digraph.
On the admitted hydrogen-complete 13-atom spiro witness, the public API returns R/S and the
alternative S/R. Four auxiliary hands change, reversing one carbon-arm ordering at atom 0.
Pinned Centres with the same policy switch reproduces the reversal; Jmol returns the public R/S
on these synthetic coordinates. Which convention the chemical sources prescribe remains open.
[Raw witness](../validation/ring-chronology/OriginMetricSpiro.lean) ·
[Geometry](../validation/ring-chronology/OriginMetricSpiro.mol) ·
[Alternative evaluator](../TetraStereo/Engine/RingOriginMetricReport.lean)

After bounded dependency preparation, run `OriginMetricSpiro.lean` in the same enforced memory
scope used above, with no argument, `mirror`, or `trace`. The trace checks changed stored hands
and the ligand orders. The separate
[Centres replay](../validation/ring-chronology/CentresOriginMetricSpiro.java) uses the pinned
Centres core and the `CentresProbe`, `CentresOxaziridineRoot` and `CentresAuxiliaryDistance`
adapters. The [Jmol script](../validation/ring-chronology/OriginMetricSpiro.spt) reads the same
molecular file. The broader digest-checked `rule1b_reroot.py` replay requires Python 3, the pinned
Centres classes, a JDK and the Eclipse JDT batch compiler used by the setup script.

Lean proves sphere-store and raw-report equality on sufficient graph domains, including graphs
where deleting one edge leaves a forest. `ringOriginOrderCheckFromRaw?` checks a stronger
closure-origin order condition without computing descriptors. A failed sufficient criterion is
not evidence of differing descriptors. An actual raw mismatch has a causal witness at an auxiliary
occurrence with identical incoming stores and different local publications.
[Order check](../TetraStereo/Engine/RingOriginOrderRawCheck.lean) ·
[Causal theorem](../TetraStereo/Engine/RingOriginCausal.lean)

## Python and Jmol source controls

The Python controls require Python 3, a JDK providing `java` and `javac` with Java source-file
launch support, and the pinned binary, source archive and authors' dataset below. Run from the
public repository root. These are external Jmol replays and diagnostic source interventions;
they do not run Lean. The scripts verify input hashes and compile diagnostic overlays in
temporary directories. Preserve both Python scripts together because the VS300 script imports
the Figure 14 helper. The binary and source archive are Jmol 14.29.17 Maven artifacts; the
molecular data is from the pinned authors' CIP Validation Suite revision.

```sh
mkdir -p tmp/figure14-jmol-replay tmp/ring-chemical-rules
curl -fsSL https://repo.maven.apache.org/maven2/net/sourceforge/jmol/jmol/14.29.17/jmol-14.29.17.jar \
  -o tmp/figure14-jmol-replay/jmol.jar
curl -fsSL https://repo.maven.apache.org/maven2/net/sourceforge/jmol/jmol/14.29.17/jmol-14.29.17-sources.jar \
  -o tmp/figure14-jmol-replay/sources.jar
curl -fsSL https://raw.githubusercontent.com/CIPValidationSuite/ValidationSuite/6b9f9db46dadc6749da8234b05164e1e0fb413b9/compounds_3d.sdf \
  -o tmp/ring-chemical-rules/compounds_3d.sdf
python3 validation/ring-chronology/check_figure14_regeneration.py
python3 validation/ring-chronology/check_vs300_bond_order.py
```

The first script checks assignment/reassignment, cubane and Figure 14 interventions. The second
checks stock and diagnostic VS300 bond-record permutations, including a constructed single-bond
derivative. Its optional `--export-single-bond NEW_DIR` writes the four derivative molfiles into
a new directory for the separate [Lean admission and equality certificate](../validation/ring-chronology/VS300SingleAdmission.lean).
Published VS300 has multiple bonds and is outside the single-bond theorem domain. The derivative
has admitted graph/coordinates but no published target label; equality under bond-record order
does not determine its absolute descriptor. The controls isolate behavior of the pinned release,
not all implementations of auxiliary reassignment.
[Figure 14 script](../validation/ring-chronology/check_figure14_regeneration.py) ·
[VS300 script](../validation/ring-chronology/check_vs300_bond_order.py)

## Installing and running Centres

Use the pinned Lean toolchain and [bounded build instructions](../BUILDING.md). Inspect a selected
module's dependency plan before building it. For example, select
`TetraStereo.Engine.CentresRingMirror` for the two-geometry API. Compilation and runtime commands
must execute in an enforced aggregate memory scope; a per-process limit is insufficient.

The [setup script](../tools/centres10/setup.sh) needs a local Centres Git checkout containing
commit `aaed608ee1d917fcd5f72964d9ca6227bd790804`, the digest-matching Guava 13.0 JAR,
Python 3, a JVM, and the Eclipse JDT batch compiler at the path specified in the script.
It compiles and verifies the pinned classes into `.cache/centres10`.

```sh
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 \
  bash tools/centres10/setup.sh /path/to/centres /path/to/guava-13.0.jar
```

The [CLI](../tools/centres10/analyze.lean) accepts JSON with `smiles`, `positions` (triples), and
optional `centers` (zero-based atom indices). Decimal coordinates become exact rationals.
By default all detected centres are configured. A duplicate-free ordered subset changes both
the requested report and the configurations supplying auxiliary descriptors.

After preparing the selected Lean dependencies, run each command inside the same enforced
memory scope, for example by prefixing it with the `systemd-run` options above:

```sh
lake env lean --run tools/centres10/analyze.lean input.json
lake env lean --run tools/centres10/analyze.lean input.json --save report.json
lake env lean --run tools/centres10/analyze.lean input.json --verify report.json
lake env lean --run tools/centres10/analyze.lean input.json --save-molecular source.json
lake env lean --run tools/centres10/analyze.lean input.json --verify-molecular source.json
lake env lean --run tools/centres10/analyze.lean input.json --mirror
lake env lean --run tools/centres10/analyze.lean input.json --verify-mirror original.json reflected.json
```

Saving requires a new file. Offline replay needs no Java. Receipts bind the pinned release,
molecular request, ordered centre inventory and handedness. Basic replay treats signed comparison
values as observations; molecular verification additionally derives and checks supported recursive
comparisons and auxiliary publications. A receipt alone does not authenticate its origin.
The live runner verifies compiled-class and dependency digests. These checks still rely on the
local launcher, toolchain, JVM and operating system.

## Controls and proof frontier

The [fluorospiro construction](../TetraStereo/Examples/CentresRingSpiroCasing.lean) exhibits an
atom-renumbering change from `S` to `s` in the pinned release, and a lowercase reflection conflict.
Its original and reflected spatial priority readings instead give uppercase `S` and `R`.
The [comparison-agreement construction](../TetraStereo/Examples/RingSourceComparisonAgreement.lean)
checks independent molecular witnesses for the affected comparisons and auxiliary publications.
The published dioxaspiro example is a separate coordinate control; the
[source checker](../TetraStereo/Engine/CentresSpiroSource.lean) handles its annotated centre.
These examples do not establish universal correctness of every priority order or recursive label.

The [grouped stereo machinery](../TetraStereo/Engine/RingGroupedStereo.lean) assembles molecular
child profiles with stage-specific priorities. The [comparison agreement interface](../TetraStereo/Engine/RingComparisonAgreement.lean)
connects independent two-geometry molecular evidence to signed rule answers and visible auxiliary
values. Coverage and agreement remain explicit proof obligations. The rebuilt whole-state and report theorem establishes equality for the grouped procedure.
The public full-path molecular report has its separate recursive source theorem and can disagree with
grouped Rule 4b traversal. The repaired public hydrogen-consensus profile still needs independent chemical justification of comparisons, reference selection, centre coverage and promotion decisions, including the rerooted Rule 1b choice above. At the original root, `RingRootReturn.rootByCount` skips Rule 6
when the root has fewer than three origin-zero duplicates. Its publication equals the grouped result
for every atom on admitted coordinates. [Evaluator and proof](../TetraStereo/Engine/RingRootReturn.lean) ·
[Molecular controls](../validation/ring-chronology/RootReturns.lean). See [ring status](../RING_STATUS.md) for the scoped theorem boundary.

The report validation driver `AuditReport.lean` imports the module generated by
`EmitReport.lean`. Generate that module first and place it on the Lean search path for audit.
The release regressions use numbered molecular records from the pinned Centres validation suite.
Supply the upstream fixture when running the full regression driver.
[Validation suite](https://github.com/SiMolecule/centres/blob/aaed608ee1d917fcd5f72964d9ca6227bd790804/core/src/test/resources/com/simolecule/centres/validate.smi)
· [Upstream licence](https://github.com/SiMolecule/centres/blob/aaed608ee1d917fcd5f72964d9ca6227bd790804/LICENSE)
