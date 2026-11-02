import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedAnalysis
import TetraStereo.OneCenter.AuthoritativeSemanticOddOpenCumuleneSpatialAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical unified analysis including odd open cumulenes

This module extends the concrete tetrahedral/ordinary-double-bond scheduler with the exhaustive
source-canonical odd-open-cumulene carrier list.  All three families use the same concrete
source-derived auxiliary fixed point for descriptor-dependent endpoint priorities.
-/

/-- Disjoint output type for the previously unified families and odd open cumulenes. -/
inductive AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene
    (source : AuthoritativeChemicalInput) where
  | prior : source.AromaticCanonicalConcreteStereochemicalAssignment →
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene
  | oddOpenCumulene : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment →
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene
  deriving DecidableEq

/-- One deterministic source-indexed result list for concrete tetrahedral, ordinary-double-bond,
and odd-open-cumulene assignments. -/
noncomputable def analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene :=
  (source.analyzeAromaticCanonicalConcreteStereochemistry carrierFuel ruleFuel).map
      AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.prior ++
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial carrierFuel ruleFuel).map
      AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.oddOpenCumulene

/-- Exact executable boundary for the three-family scheduler. -/
def AromaticCanonicalConcreteStereochemicalWithOddCumuleneExecutableMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment :
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene) : Prop :=
  match assignment with
  | .prior prior =>
      source.AromaticCanonicalConcreteStereochemicalExecutableMember
        carrierFuel ruleFuel prior
  | .oddOpenCumulene odd =>
      ∃ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
        source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit = some odd

/-- The three-family scheduler contains exactly the results admitted by the executable family
judgments. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene_iff_executableMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment :
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene) :
    assignment ∈ source.analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene
        carrierFuel ruleFuel ↔
      source.AromaticCanonicalConcreteStereochemicalWithOddCumuleneExecutableMember
        carrierFuel ruleFuel assignment := by
  cases assignment with
  | prior prior =>
      unfold AromaticCanonicalConcreteStereochemicalWithOddCumuleneExecutableMember
      constructor
      · intro present
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene,
          List.mem_append] at present
        rcases present with priorPresent | oddPresent
        · obtain ⟨other, otherPresent, equal⟩ := List.mem_map.mp priorPresent
          cases equal
          exact
            (source.mem_analyzeAromaticCanonicalConcreteStereochemistry_iff_executableMember
              carrierFuel ruleFuel prior).mp otherPresent
        · obtain ⟨_other, _otherPresent, equal⟩ := List.mem_map.mp oddPresent
          contradiction
      · intro executable
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene,
          List.mem_append]
        left
        exact List.mem_map.mpr ⟨prior,
          (source.mem_analyzeAromaticCanonicalConcreteStereochemistry_iff_executableMember
            carrierFuel ruleFuel prior).mpr executable, rfl⟩
  | oddOpenCumulene odd =>
      unfold AromaticCanonicalConcreteStereochemicalWithOddCumuleneExecutableMember
      constructor
      · intro present
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene,
          List.mem_append] at present
        rcases present with priorPresent | oddPresent
        · obtain ⟨_other, _otherPresent, equal⟩ := List.mem_map.mp priorPresent
          contradiction
        · obtain ⟨other, otherPresent, equal⟩ := List.mem_map.mp oddPresent
          cases equal
          exact
            (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
              carrierFuel ruleFuel odd).mp otherPresent
      · intro executable
        rw [analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene,
          List.mem_append]
        right
        exact List.mem_map.mpr ⟨odd,
          (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
            carrierFuel ruleFuel odd).mpr executable, rfl⟩

/-- Independent chemical meaning of every three-family output. -/
def DeclarativeAromaticCanonicalConcreteStereochemicalWithOddCumuleneMember
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment :
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene) : Prop :=
  match assignment with
  | .prior prior =>
      source.DeclarativeAromaticCanonicalConcreteStereochemicalMember
        carrierFuel ruleFuel prior
  | .oddOpenCumulene odd =>
      source.DeclarativeAromaticCanonicalOddOpenCumuleneSpatialAssignment
        carrierFuel ruleFuel odd

/-- Every descriptor emitted by the three-family scheduler satisfies its independent topology,
complete applicable priority-rule, exact-geometry, and final-descriptor judgment. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene_member_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment :
      source.AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene)
    (present : assignment ∈
      source.analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene
        carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalConcreteStereochemicalWithOddCumuleneMember
      carrierFuel ruleFuel assignment := by
  cases assignment with
  | prior prior =>
      have executable :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene_iff_executableMember
          carrierFuel ruleFuel (.prior prior)).mp present
      exact source.analyzeAromaticCanonicalConcreteStereochemistry_member_sound
        carrierFuel ruleFuel prior
        ((source.mem_analyzeAromaticCanonicalConcreteStereochemistry_iff_executableMember
          carrierFuel ruleFuel prior).mpr executable)
  | oddOpenCumulene odd =>
      have executable :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene_iff_executableMember
          carrierFuel ruleFuel (.oddOpenCumulene odd)).mp present
      exact source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_member_sound
        carrierFuel ruleFuel odd
        ((source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
          carrierFuel ruleFuel odd).mpr executable)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
