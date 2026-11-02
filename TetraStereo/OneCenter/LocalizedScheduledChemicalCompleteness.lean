import TetraStereo.OneCenter.LocalizedTetrahedralChemicalCompleteness
import TetraStereo.OneCenter.LocalizedOrdinaryMonocyclicChemicalCompleteness
import TetraStereo.OneCenter.LocalizedOpenCumuleneChemicalCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Molecule-wide chemical completeness for the scheduled four-family pipeline

This file gives one non-circular applicability relation for the complete public scheduled
analyzer.  Applicability is stated on canonical physical units and includes the independent
finite chemical classification, strict priority/topology facts, and exact geometry required by
the corresponding descriptor family.  It never assumes that the final family evaluator, public
analyzer, or scheduler returned a descriptor.

The resulting theorem packages both directions needed for a refinement claim:

* every public result satisfies its independent declarative family specification; and
* every independently chemically applicable physical unit is emitted exactly once.

This is the end-to-end theorem for the four families currently scheduled by
`analyzeLocalizedScheduledStereochemistry`; it deliberately does not rename unsupported IUPAC
families as supported ones.
-/

/-- Independently resolved chemical applicability for any physical unit recognized by the
four-family scheduled analyzer, at the molecule-size completeness bound.  Geometry is part of
the premise because connectivity alone cannot determine an absolute spatial descriptor. -/
def LocalizedScheduledChemicallyApplicableAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (unit : input.LocalizedScheduledStereochemicalPhysicalUnit) : Prop :=
  match unit with
  | .tetrahedral center =>
      input.LocalizedTetrahedralChemicalReadiness
        input.certified.input.molecule.atomCount center
  | .evenAxial axis =>
      input.LocalizedEvenCumuleneChemicalReadyAtAtomCount axis
  | .ordinaryMonocyclicEZ bond =>
      input.LocalizedOrdinaryMonocyclicChemicalDependencyEvidenceWithState
        input.certified.input.molecule.atomCount
        (input.localizedDescriptorBearingRule3Through5SchedulerState
          input.certified.input.molecule.atomCount)
        bond
  | .oddCumuleneEZ axis =>
      input.LocalizedOddCumuleneChemicalReadyAtAtomCount axis

private theorem exists_conforming_assignment_of_physicalUnit_count_eq_one
    (input : CertifiedLocalizedCIPInput)
    (unit : input.LocalizedScheduledStereochemicalPhysicalUnit)
    (count : List.count unit
      ((input.analyzeLocalizedScheduledStereochemistry
        input.certified.input.molecule.atomCount).map
          LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1) :
    ∃ assignment : input.LocalizedScheduledStereochemicalAssignment
        input.certified.input.molecule.atomCount,
      assignment ∈ input.analyzeLocalizedScheduledStereochemistry
          input.certified.input.molecule.atomCount ∧
        assignment.physicalUnit = unit ∧
        input.DeclarativeLocalizedScheduledStereochemicalAssignment
          input.certified.input.molecule.atomCount assignment ∧
        List.count unit
          ((input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount).map
              LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  have unitPresent : unit ∈
      (input.analyzeLocalizedScheduledStereochemistry
        input.certified.input.molecule.atomCount).map
          LocalizedScheduledStereochemicalAssignment.physicalUnit :=
    List.count_pos_iff.mp (by rw [count]; exact Nat.zero_lt_one)
  obtain ⟨assignment, present, identity⟩ := List.mem_map.mp unitPresent
  exact ⟨assignment, present, identity,
    input.analyzeLocalizedScheduledStereochemistry_member_conforms
      input.certified.input.molecule.atomCount assignment present,
    count⟩

/-- Every independently chemically applicable physical unit has a conforming public assignment,
and that physical unit occurs literally once in the complete scheduled output. -/
theorem every_chemicallyApplicable_scheduledPhysicalUnit_public_exactly_once
    (input : CertifiedLocalizedCIPInput)
    (unit : input.LocalizedScheduledStereochemicalPhysicalUnit)
    (applicable : input.LocalizedScheduledChemicallyApplicableAtAtomCount unit) :
    ∃ assignment : input.LocalizedScheduledStereochemicalAssignment
        input.certified.input.molecule.atomCount,
      assignment ∈ input.analyzeLocalizedScheduledStereochemistry
          input.certified.input.molecule.atomCount ∧
        assignment.physicalUnit = unit ∧
        input.DeclarativeLocalizedScheduledStereochemicalAssignment
          input.certified.input.molecule.atomCount assignment ∧
        List.count unit
          ((input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount).map
              LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  cases unit with
  | tetrahedral center =>
      obtain ⟨_source, _present, _derived, count⟩ :=
        input.every_chemicallyApplicable_localizedTetrahedral_public_exactly_once
          input.certified.input.molecule.atomCount center applicable
      exact input.exists_conforming_assignment_of_physicalUnit_count_eq_one
        (.tetrahedral center) count
  | evenAxial axis =>
      obtain ⟨_source, _present, _derived, count⟩ :=
        input.every_chemicallyApplicable_localizedEvenCumulene_public_exactly_once
          axis applicable
      exact input.exists_conforming_assignment_of_physicalUnit_count_eq_one
        (.evenAxial axis) count
  | ordinaryMonocyclicEZ bond =>
      obtain ⟨_source, _present, _derived, count⟩ :=
        input.every_chemicallyApplicable_localizedOrdinaryMonocyclicEZ_public_exactly_once
          input.certified.input.molecule.atomCount bond applicable
      exact input.exists_conforming_assignment_of_physicalUnit_count_eq_one
        (.ordinaryMonocyclicEZ bond) count
  | oddCumuleneEZ axis =>
      obtain ⟨_source, _present, _derived, count⟩ :=
        input.every_chemicallyApplicable_localizedOddCumulene_public_exactly_once
          axis applicable
      exact input.exists_conforming_assignment_of_physicalUnit_count_eq_one
        (.oddCumuleneEZ axis) count

/-- End-to-end refinement theorem for the complete current scheduled analyzer at the certified
molecule-size bound: all emitted descriptors conform, neither assignments nor physical units are
duplicated, and every independently applicable physical unit is represented exactly once. -/
theorem analyzeLocalizedScheduledStereochemistry_endToEnd_chemicalCompleteness
    (input : CertifiedLocalizedCIPInput) :
    (∀ assignment ∈ input.analyzeLocalizedScheduledStereochemistry
        input.certified.input.molecule.atomCount,
      input.DeclarativeLocalizedScheduledStereochemicalAssignment
        input.certified.input.molecule.atomCount assignment) ∧
    (input.analyzeLocalizedScheduledStereochemistry
      input.certified.input.molecule.atomCount).Nodup ∧
    ((input.analyzeLocalizedScheduledStereochemistry
      input.certified.input.molecule.atomCount).map
        LocalizedScheduledStereochemicalAssignment.physicalUnit).Nodup ∧
    ∀ unit : input.LocalizedScheduledStereochemicalPhysicalUnit,
      input.LocalizedScheduledChemicallyApplicableAtAtomCount unit →
      ∃ assignment : input.LocalizedScheduledStereochemicalAssignment
          input.certified.input.molecule.atomCount,
        assignment ∈ input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount ∧
          assignment.physicalUnit = unit ∧
          input.DeclarativeLocalizedScheduledStereochemicalAssignment
            input.certified.input.molecule.atomCount assignment ∧
          List.count unit
            ((input.analyzeLocalizedScheduledStereochemistry
              input.certified.input.molecule.atomCount).map
                LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  refine ⟨?_, input.analyzeLocalizedScheduledStereochemistry_nodup
      input.certified.input.molecule.atomCount,
    input.analyzeLocalizedScheduledStereochemistry_physicalUnits_nodup
      input.certified.input.molecule.atomCount, ?_⟩
  · intro assignment present
    exact input.analyzeLocalizedScheduledStereochemistry_member_conforms
      input.certified.input.molecule.atomCount assignment present
  · intro unit applicable
    exact input.every_chemicallyApplicable_scheduledPhysicalUnit_public_exactly_once
      unit applicable

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
