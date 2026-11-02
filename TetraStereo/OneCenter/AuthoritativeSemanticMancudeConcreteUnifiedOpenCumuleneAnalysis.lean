import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedCumuleneAnalysis
import TetraStereo.OneCenter.AuthoritativeSemanticEvenOpenCumuleneAxialAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Unified source-canonical analysis through both open-cumulene parity routes
-/

/-- Disjoint output type for tetrahedral, ordinary-double-bond, odd-open-cumulene, and
even-open-cumulene assignments. -/
inductive AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes
    (source : AuthoritativeChemicalInput) where
  | prior : source.AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene →
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes
  | evenOpenCumulene : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment →
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes
  deriving DecidableEq

/-- One deterministic source-indexed result list through both exhaustive open-cumulene routes. -/
noncomputable def analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes :=
  (source.analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene
      carrierFuel ruleFuel).map
    AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ++
  (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial carrierFuel ruleFuel).map
    AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.evenOpenCumulene

/-- Exact executable boundary for the four-family scheduler. -/
def AromaticCanonicalConcreteStereochemicalWithOpenCumulenesExecutableMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment :
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes) : Prop :=
  match assignment with
  | .prior prior =>
      source.AromaticCanonicalConcreteStereochemicalWithOddCumuleneExecutableMember
        carrierFuel ruleFuel prior
  | .evenOpenCumulene even =>
      ∃ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
        source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit = some even

/-- The four-family scheduler contains exactly its executable family judgments. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_iff_executableMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment :
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes) :
    assignment ∈ source.analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes
        carrierFuel ruleFuel ↔
      source.AromaticCanonicalConcreteStereochemicalWithOpenCumulenesExecutableMember
        carrierFuel ruleFuel assignment := by
  cases assignment with
  | prior prior =>
      unfold AromaticCanonicalConcreteStereochemicalWithOpenCumulenesExecutableMember
      constructor
      · intro present
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
          List.mem_append] at present
        rcases present with priorPresent | evenPresent
        · obtain ⟨other, otherPresent, equal⟩ := List.mem_map.mp priorPresent
          cases equal
          exact
            (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene_iff_executableMember
              carrierFuel ruleFuel prior).mp otherPresent
        · obtain ⟨_other, _otherPresent, equal⟩ := List.mem_map.mp evenPresent
          contradiction
      · intro executable
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
          List.mem_append]
        left
        exact List.mem_map.mpr ⟨prior,
          (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene_iff_executableMember
            carrierFuel ruleFuel prior).mpr executable, rfl⟩
  | evenOpenCumulene even =>
      unfold AromaticCanonicalConcreteStereochemicalWithOpenCumulenesExecutableMember
      constructor
      · intro present
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
          List.mem_append] at present
        rcases present with priorPresent | evenPresent
        · obtain ⟨_other, _otherPresent, equal⟩ := List.mem_map.mp priorPresent
          contradiction
        · obtain ⟨other, otherPresent, equal⟩ := List.mem_map.mp evenPresent
          cases equal
          exact
            (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
              carrierFuel ruleFuel even).mp otherPresent
      · intro executable
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
          List.mem_append]
        right
        exact List.mem_map.mpr ⟨even,
          (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
            carrierFuel ruleFuel even).mpr executable, rfl⟩

/-- Independent chemical meaning of every four-family output. -/
def DeclarativeAromaticCanonicalConcreteStereochemicalWithOpenCumulenesMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment :
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes) : Prop :=
  match assignment with
  | .prior prior =>
      source.DeclarativeAromaticCanonicalConcreteStereochemicalWithOddCumuleneMember
        carrierFuel ruleFuel prior
  | .evenOpenCumulene even =>
      source.DeclarativeAromaticCanonicalEvenOpenCumuleneAxialAssignment
        carrierFuel ruleFuel even

/-- Every descriptor emitted through both open-cumulene routes satisfies its independent
topology, complete applicable priority-rule, exact-geometry, and descriptor judgment. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment :
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes)
    (present : assignment ∈
      source.analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes
        carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalConcreteStereochemicalWithOpenCumulenesMember
      carrierFuel ruleFuel assignment := by
  cases assignment with
  | prior prior =>
      have executable :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_iff_executableMember
          carrierFuel ruleFuel (.prior prior)).mp present
      exact
        source.analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene_member_sound
          carrierFuel ruleFuel prior
          ((source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene_iff_executableMember
            carrierFuel ruleFuel prior).mpr executable)
  | evenOpenCumulene even =>
      have executable :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_iff_executableMember
          carrierFuel ruleFuel (.evenOpenCumulene even)).mp present
      exact source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_member_sound
        carrierFuel ruleFuel even
        ((source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
          carrierFuel ruleFuel even).mpr executable)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
