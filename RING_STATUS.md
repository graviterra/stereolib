# Ring source status — 22 November 2026

The ring programme now has an explicit executable development profile and an independent
source-model connection to its detected-centre report. This is a scoped source update, not a
claim of full CIP correctness, chemical completion or release readiness.

## Established connections

- **Public engine:** [`accumulatedReferencesRegenerated`](TetraStereo/Engine/LocalizedChemicalRingPublic.lean)
  executes the cached evaluator and equals the prepared report, preserving refusal entries.
  It is an opt-in profile; the default evaluator is unchanged. The
  [physical admission bridge](TetraStereo/Engine/LocalizedChemicalRingPhysicalCertificate.lean)
  can derive the required calibration evidence when its coordinate checks pass.
- **Independent source and actual report:** the
  [source-model construction](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedSourceModel.lean)
  and [existence package](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedSourceModelExistence.lean)
  establish a unique independent accumulated-reference profile agreeing with the actual
  detected-centre report, including refusals.
- **All-root cancellation:** the
  [all-root cancellation/report package](TetraStereo/OneCenter/LocalizedChemicalRingAllRootCancellationReport.lean)
  proves cancellation equality with the actual consensus/step at every final root, including
  two-pair outcomes. The [selected-resolution proof](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedRootSelectedResolution.lean)
  discharges the earlier resolution premises.
- **Concrete exact result:** the
  [DoubleC3 physical report](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport.lean)
  derives auxiliary `R`/`S`, exact final lowercase `s`, and actual report membership. Its
  [source model](TetraStereo/OneCenter/LocalizedChemicalRingJointPreparedDoubleC3SourceModel.lean)
  has an inhabited unique value.
- **Physical classification:** root-key equality has an independent
  [physical-transport characterization](TetraStereo/OneCenter/LocalizedChemicalRingRootPhysicalKeyClasses.lean).
  [Transitive roots](TetraStereo/OneCenter/LocalizedChemicalRingRootTransitiveReport.lean)
  and [nontransitive roots with at most one moving class](TetraStereo/OneCenter/LocalizedChemicalRingRootSingleMovingClass.lean)
  have exact report-level success/refusal criteria. The
  [two-moving-pairs theorem](TetraStereo/OneCenter/LocalizedChemicalRingRootTwoMovingPairs.lean)
  localizes nontransitive refusals without odd symmetry to two moving pairs.
- **Exact two-pair entries:** the [pairing parity theorem](TetraStereo/OneCenter/LocalizedChemicalRingPairingParity.lean)
  identifies the parity of a four-ligand priority order with its action on the three pairings.
  [`report_iff_pairingDescriptor`](TetraStereo/OneCenter/LocalizedChemicalRingTwoPairReport.lean#L230)
  then gives the exact two-pair report entry, including refusal, absolute letter and casing.
  Its criterion reads independently specified contextual source priorities on both geometries;
  no fallback output, desired descriptor or successful promotion is supplied as an assumption.
  Without odd boundary symmetry, success requires matching promotion parities between the two
  classes on both geometries. After success, a parity change under reflection gives lowercase;
  unchanged parity gives uppercase. The calibrated original frame supplies the absolute letter
  together with the original priority parity. Odd-boundary roots refuse.
- **All-root outcomes:** [`existsUnique_allRoot_outcomes`](TetraStereo/OneCenter/LocalizedChemicalRingTwoPairReport.lean#L353)
  combines transitive, single-moving-class and two-pair cases into exact success/refusal criteria
  at every detected root, using one unique source profile. The root frames and source model are
  derived. This is an outcome classification for the named procedure; it does not yet supply
  the complete chemical interpretation of successful letters and casing in every class.

## Domain and remaining work

The generic ring results concern finite inputs with single bonds and constant formal charge,
raw/certified structure agreement, stereochemical admissibility and localized covalent support.
Rings and stereochemically dependent non-root centres are allowed. Physical results additionally
require calibrated coordinates/configuration at every detected centre. Structural admission
alone does not establish this calibration. Auxiliary cancellation statements retain their stated
tied-branch scope; each linked declaration gives its exact hypotheses.

The [exact public certificate](TetraStereo/Engine/LocalizedChemicalRingExactCertificate.lean)
now supplies source-priority letters, casing and refusal criteria at every detected root under
the stated domain hypotheses. This closes the earlier public-interface integration gap. The
[chronology certificate](TetraStereo/Engine/LocalizedChemicalRingChronologyCertificate.lean)
connects frozen disagreements to changed downstream auxiliary readings.

Independent chemical fidelity remains open: contextual reference lifetime, regeneration,
publication schedules and recursive priority meanings must be justified against the intended
chemical procedure. Exactness for the named source model does not establish normative adoption.

The [grouped comparison machinery](TetraStereo/Engine/RingGroupedStereo.lean) builds stage-specific
molecular profiles. The [comparison agreement interface](TetraStereo/Engine/RingComparisonAgreement.lean)
relates independently derived two-geometry comparisons and auxiliary values to source observations.
Its coverage and agreement hypotheses remain explicit; universal comparison coverage is not claimed.

For a pair of ligands tied on constitutional rules at a reachable scheduled occurrence,
`scheduled_frontier` now proves that the grouped evaluator returns a molecularly determined
rule and signed score on each geometry. The [17-atom control](validation/ring-chronology/GroupedStereo.lean)
gives Rule 5 scores of +2 and −2. Exchanging two coordinates moves the decision to Rule 4b,
with −1 on both geometries. A whole-centre proof must combine the twelve directed comparisons
into a consistent ranking or justify promotion or refusal, then show how that decision enters
the molecular report. [Scheduled pair theorem](TetraStereo/Engine/RingGroupedStereo.lean)

## Runtime and coordinate controls

The separate [Centres API](TetraStereo/Engine/CentresRing.lean) runs the pinned 2018 release and
checks its chronological report. Molecular and mirror APIs strengthen this with independent
comparison/publication derivations and spatial casing. The
[fluorospiro counterexample](TetraStereo/Examples/CentresRingSpiroCasing.lean) demonstrates `S`/`s`
under atom renumbering and a lowercase reflection conflict. The
[comparison witness](TetraStereo/Examples/RingSourceComparisonAgreement.lean) independently
checks the affected molecular comparisons and publications. The published dioxaspiro input is a
separate annotated coordinate control, supported by the
[source checker](TetraStereo/Engine/CentresSpiroSource.lean). Configured-centre inventories are part
of the input: changing them can change auxiliary availability.

The [frozen evaluator](TetraStereo/Engine/LocalizedChemicalRingFrozenExecution.lean) is a matched
control for auxiliary regeneration, not a claim of equivalence with the pinned release.
See [setup and entry points](docs/ring-evaluator.md) for executable and offline routes, receipt
limitations and the distinction between structural and coordinate admission.

## Verification boundary

The earlier preserved original-source checkpoints cover **74 distinct source files and 422
kernel guards**. The subsequent two-module checkpoint adds **eight kernel-only guards** for pairing
parity, exact two-pair entries and exhaustive root outcomes. The two public source files are
byte-identical to those accepted source snapshots; review verified the current and frozen source
and compiled-artifact hashes and the saved successful bounded-build receipts.

Those receipts describe the original-source build environment, not a fresh compilation against
the public distribution's dependencies. Earlier small public-route smoke checks passed, but no
fresh Lean compilation or full-library build was run for this publication. Publication checks
are static only.

The inventory contains **4,364 maintained Lean modules**, up from 4,131 in the preceding
public revision. The package contains **4,365 Lean source files** including the umbrella.
Runtime and validation drivers are listed separately from the package inventory. Module counts,
source-model proofs, runtime examples and chemical source approval are different kinds of evidence.
The universal theorem and full chemical approval remain open. See the [README](README.md) for
existing acyclic results, collaboration guidance and safe source checks.
