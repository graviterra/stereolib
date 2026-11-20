# Ring source status — 20 November 2026

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

The two-pair outcome and casing obligation is closed for the named procedure under these
hypotheses. The remaining scientific obligations are:

1. **Exact chemical letters and casing across the other physical classes:** the all-root
   result classifies success/refusal. Complete independent absolute-priority and mirror-response
   meanings for successful descriptors still need to be joined across the remaining classes.
2. **Normative nested-reference fidelity:** existence and uniqueness for accumulated references
   and regenerated contexts do not establish that this policy is prescribed by IUPAC. A fidelity
   argument must cover nested reference lifetime, regeneration, scheduling and final applicability,
   as well as letters, casing and refusals. Policy-sensitive examples establish that policy choice
   matters; they do not select the chemically correct policy.

The public engine already equals the prepared report. Its
[`SourceMeaning`](TetraStereo/Engine/LocalizedChemicalRingPublic.lean#L211) interface still
exposes the earlier physical casing clause under pairwise proper distinguishability; packaging
the new two-pair and all-root outcome theorems in that interface remains integration work.
Standalone certificate export for this ring profile also remains open.

A separate 21-atom spiro candidate remains unverified: a run lasting about fifteen minutes did
not yield an accepted completed result. It supplies no additional correctness claim.

## Verification boundary

The earlier preserved original-source checkpoints cover **74 distinct source files and 422
kernel guards**. The new two-module checkpoint adds **eight kernel-only guards** for pairing
parity, exact two-pair entries and exhaustive root outcomes. The two public source files are
byte-identical to those accepted source snapshots; review verified the current and frozen source
and compiled-artifact hashes and the saved successful bounded-build receipts.

Those receipts describe the original-source build environment, not a fresh compilation against
the public distribution's dependencies. Earlier small public-route smoke checks passed, but no
fresh Lean compilation or full-library build was run for this publication. Publication checks
are static only.

The inventory now contains **4,131 maintained Lean modules**, up from 3,714; including the
umbrella, there are **4,132 Lean source files** in total. Module counts,
source-model proofs, runtime examples and chemical source approval are different kinds of evidence.
The universal theorem and full chemical approval remain open. See the [README](README.md) for
existing acyclic results, collaboration guidance and safe source checks.
