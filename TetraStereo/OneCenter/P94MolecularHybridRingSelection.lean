import TetraStereo.OneCenter.P94MolecularAuthoritativeRingSelection

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularHybridRingSelection

open CoordinateRing
open CoordinateTwistInOut
open P94MolecularRingCycleScheduler
open P94MolecularBicyclicFramework
open P94MolecularCompleteInOutRequestScheduler
open P94CarbohydrateFiveRingTwist
open P94MolecularAuthoritativeRingSelection

/-!
# Hybrid automatic/authoritative P-94 ring selection

The exhaustive graph scheduler already exposes exactly when a chordless molecular carrier overlaps
a different admitted carrier.  An isolated carrier therefore needs no external cycle-basis choice:
its scheduled P-94 requests are selected automatically.  Only an overlapping carrier crosses the
explicit nomenclature-authority boundary.

This module builds those two finite authorities, proves the external one is restricted to the
ambiguous subdomain, and takes their exact union.  The merged authority is then substituted into
the established four-branch molecule report without weakening its membership or multiplicity
theorems.
-/

def ringInputUnit : AutomaticCoordinateRingInput → P94ConformationUnit
  | .envelope unit | .sixRing unit | .halfChair unit | .crown unit | .tub unit => unit

def AutomaticRingInputOverlapAmbiguous
    (molecule : RawMolecule) (input : AutomaticCoordinateRingInput) : Prop :=
  P94RingCarrierOverlapAmbiguous molecule (ringInputUnit input).atoms.toFinset

noncomputable instance automaticRingInputOverlapAmbiguousDecidable
    (molecule : RawMolecule) (input : AutomaticCoordinateRingInput) :
    Decidable (AutomaticRingInputOverlapAmbiguous molecule input) :=
  Classical.propDecidable _

/-! ## Automatic selection outside the ambiguity boundary -/

noncomputable def unambiguousRingAuthority : IndependentP94RingSelectionAuthority where
  Applies := fun molecule input =>
    input ∈ scheduledAutomaticCoordinateRingInputs molecule ∧
      ¬AutomaticRingInputOverlapAmbiguous molecule input
  inputs := fun molecule =>
    (scheduledAutomaticCoordinateRingInputs molecule).filter fun input =>
      ¬AutomaticRingInputOverlapAmbiguous molecule input
  mem_inputs_iff := by
    intro molecule input
    simp
  applies_scheduled := fun _ _ applies => applies.1

theorem unambiguousRingAuthority_applies_iff
    (molecule : RawMolecule) (input : AutomaticCoordinateRingInput) :
    unambiguousRingAuthority.Applies molecule input ↔
      input ∈ scheduledAutomaticCoordinateRingInputs molecule ∧
        ¬AutomaticRingInputOverlapAmbiguous molecule input :=
  Iff.rfl

/-! ## Externally selected ambiguous carriers only -/

structure IndependentAmbiguousP94RingSelectionAuthority where
  authority : IndependentP94RingSelectionAuthority
  applies_ambiguous : ∀ molecule input, authority.Applies molecule input →
    AutomaticRingInputOverlapAmbiguous molecule input

theorem ambiguousRingAuthority_applies_ambiguous
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (molecule : RawMolecule) (input : AutomaticCoordinateRingInput)
    (applies : external.authority.Applies molecule input) :
    AutomaticRingInputOverlapAmbiguous molecule input :=
  external.applies_ambiguous molecule input applies

noncomputable def unionRingAuthorities
    (left right : IndependentP94RingSelectionAuthority) :
    IndependentP94RingSelectionAuthority where
  Applies := fun molecule input => left.Applies molecule input ∨ right.Applies molecule input
  inputs := fun molecule => left.inputs molecule ∪ right.inputs molecule
  mem_inputs_iff := by
    intro molecule input
    simp only [Finset.mem_union, left.mem_inputs_iff, right.mem_inputs_iff]
  applies_scheduled := by
    intro molecule input applies
    rcases applies with leftApplies | rightApplies
    · exact left.applies_scheduled molecule input leftApplies
    · exact right.applies_scheduled molecule input rightApplies

noncomputable def hybridRingAuthority
    (external : IndependentAmbiguousP94RingSelectionAuthority) :
    IndependentP94RingSelectionAuthority :=
  unionRingAuthorities unambiguousRingAuthority external.authority

theorem hybridRingAuthority_applies_iff
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (molecule : RawMolecule) (input : AutomaticCoordinateRingInput) :
    (hybridRingAuthority external).Applies molecule input ↔
      (input ∈ scheduledAutomaticCoordinateRingInputs molecule ∧
        ¬AutomaticRingInputOverlapAmbiguous molecule input) ∨
      external.authority.Applies molecule input :=
  Iff.rfl

/-! ## Exact complete report under the hybrid authority -/

abbrev IndependentMolecularAssignmentWithHybridRings
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) : Prop :=
  IndependentMolecularAssignmentWithAuthoritativeRings premises molecule plan
    (hybridRingAuthority external) carbohydrateAuthority assignment

noncomputable def molecularAssignmentsWithHybridRings
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    List P94ConformationAssignment :=
  molecularAssignmentsWithAuthoritativeRings premises certified plan
    (hybridRingAuthority external) carbohydrateAuthority

theorem molecularAssignmentsWithHybridRings_mem_iff_independent
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    assignment ∈ molecularAssignmentsWithHybridRings premises certified plan
        external carbohydrateAuthority ↔
      IndependentMolecularAssignmentWithHybridRings premises
        certified.result.parsed plan external carbohydrateAuthority assignment :=
  molecularAssignmentsWithAuthoritativeRings_mem_iff_independent premises certified plan
    (hybridRingAuthority external) carbohydrateAuthority assignment

theorem molecularAssignmentsWithHybridRings_nodup
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (molecularAssignmentsWithHybridRings premises certified plan
      external carbohydrateAuthority).Nodup :=
  molecularAssignmentsWithAuthoritativeRings_nodup premises certified plan
    (hybridRingAuthority external) carbohydrateAuthority

theorem molecularAssignmentWithHybridRings_count_eq_one_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (molecularAssignmentsWithHybridRings premises certified plan
        external carbohydrateAuthority) = 1 ↔
      IndependentMolecularAssignmentWithHybridRings premises certified.result.parsed plan
        external carbohydrateAuthority assignment :=
  molecularAssignmentWithAuthoritativeRings_count_eq_one_iff premises certified plan
    (hybridRingAuthority external) carbohydrateAuthority assignment

theorem molecularAssignmentWithHybridRings_count_eq_zero_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (molecularAssignmentsWithHybridRings premises certified plan
        external carbohydrateAuthority) = 0 ↔
      ¬IndependentMolecularAssignmentWithHybridRings premises certified.result.parsed plan
        external carbohydrateAuthority assignment :=
  molecularAssignmentWithAuthoritativeRings_count_eq_zero_iff premises certified plan
    (hybridRingAuthority external) carbohydrateAuthority assignment

end BlueBookP94.P94MolecularHybridRingSelection
end TetraStereo.OneCenter
