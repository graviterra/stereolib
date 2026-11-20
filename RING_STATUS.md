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
  discharges the earlier resolution premises. This equality is already closed; the remaining
  two-pair question concerns an independent physical interpretation of the outcome.
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
  proves that the remaining nontransitive refusals without odd symmetry necessarily have
  two moving pairs. It does not say every two-pair root refuses.

## Domain and remaining work

The generic ring results concern finite inputs with single bonds and constant formal charge,
raw/certified structure agreement, stereochemical admissibility and localized covalent support.
Rings and stereochemically dependent non-root centres are allowed. Physical results additionally
require calibrated coordinates/configuration at every detected centre. Structural admission
alone does not establish this calibration. Auxiliary cancellation statements retain their stated
tied-branch scope; each linked declaration gives its exact hypotheses.

Three obligations remain:

1. **Two-pair orientation:** define cross-class orientation independently of fallback outputs,
   and prove exact success/refusal for both original and reflected geometries. Equal readings
   within each pair do not settle agreement between the pairs.
2. **Letters and casing beyond pairwise proper distinguishability:** current broader physical
   results classify existence/refusal. Independent absolute-priority and mirror-response
   meanings still need to determine exact successful letters and casing outside that domain.
3. **Normative nested-reference fidelity:** existence and uniqueness for accumulated references
   and regenerated contexts do not establish that this policy is prescribed by IUPAC. A fidelity
   argument must cover nested reference lifetime, regeneration, scheduling and final applicability,
   as well as letters, casing and refusals. Policy-sensitive examples establish that policy choice
   matters; they do not select the chemically correct policy.

A separate 21-atom spiro candidate remains unverified: a run lasting about fifteen minutes did
not yield an accepted completed result. It supplies no additional correctness claim.

## Verification boundary

The preserved original-source checkpoint covers **74 distinct source files and 422 kernel guards**;
static identity checks confirmed that checkpoint remains intact. Those figures describe the
original-source evidence, not a fresh compilation of this transformed public export. Earlier
small public-route smoke checks passed, but no fresh Lean compilation or full-library build was
run for this publication. Publication checks are static only.

The inventory now contains **4,129 maintained Lean modules**, up from 3,714; including the
umbrella, there are **4,130 Lean source files** in total. Module counts,
source-model proofs, runtime examples and chemical source approval are different kinds of evidence.
The universal theorem and full chemical approval remain open. See the [README](README.md) for
existing acyclic results, collaboration guidance and safe source checks.
