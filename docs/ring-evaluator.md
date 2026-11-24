# Evaluating tetrahedral rings

The baseline ring report keeps completed auxiliary assignments fixed during each Rule 6
promotion trial. It first attempts a constitutional ranking, then publishes occurrence-addressed
auxiliaries by whole spheres from farthest to nearest. The rebuilt evaluator uses zero mass for
ring duplicates throughout its recursive constitutional and stereo sorts. Its complete state
and report equal the grouped procedure on admitted coordinates.
[Rebuilt evaluator and proofs](../TetraStereo/Engine/RingRebuiltStereo.lean)

The separately named accumulated-reference profile regenerates child observations for a new
context. The pinned Centres 1.0 adapter replays the 2018 procedure's mutable references and
auxiliary publication schedule. Agreement with one procedure does not establish agreement
with another or universal IUPAC fidelity.

## Lean entry points

Import the selected module rather than building the whole library.

| Task | Entry point | Source |
| --- | --- | --- |
| Evaluate the frozen-auxiliary baseline | `Engine.ringGroupedMolecularReport?` | [Public API](../TetraStereo/Engine/PublicAPI.lean) |
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

These inputs are finite, single-bond, constant-charge molecules with explicit structural
admission. The physical theorems require calibrated nondegenerate coordinates at detected
centres. `coordinatesAdmitted` supplies a separate gate; structural admission alone is insufficient.
Coordinates use the public parser's hydrogen-expanded atom order. Refusal is a report entry with
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
values. Coverage and agreement remain explicit proof obligations. The rebuilt whole-state and report theorem closes the earlier integration step for this
named procedure. Independent chemical justification of its comparisons, reference selection and
promotion decisions remains open, as does the universal graph-to-locality bridge for the Rule 6
closure-count shortcut. A passing receipt does not supply those proofs. See [ring status](../RING_STATUS.md) for the scoped theorem boundary.

The report validation driver `AuditReport.lean` imports the module generated by
`EmitReport.lean`. Generate that module first and place it on the Lean search path for audit.
The release regressions use numbered molecular records from the pinned Centres validation suite.
Supply the upstream fixture when running the full regression driver.
[Validation suite](https://github.com/SiMolecule/centres/blob/aaed608ee1d917fcd5f72964d9ca6227bd790804/core/src/test/resources/com/simolecule/centres/validate.smi)
· [Upstream licence](https://github.com/SiMolecule/centres/blob/aaed608ee1d917fcd5f72964d9ca6227bd790804/LICENSE)
