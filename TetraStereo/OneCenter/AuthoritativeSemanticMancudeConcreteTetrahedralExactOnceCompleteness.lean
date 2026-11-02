import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedCyclicCumuleneAnalysis
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact-once completeness for concrete source tetrahedral centers

The concrete Rules-1a--6 endpoint already has a uniform finite-fuel existence theorem. This module
proves that the exhaustive center list and the whole-source analyzer are duplicate-free, then
strengthens finite-fuel existence to one unique assignment for the exact physical center.
-/

/-- The deterministic source-canonical tetrahedral center list has no duplicates. -/
theorem aromaticCanonicalTetrahedralCenters_nodup
    (source : AuthoritativeChemicalInput) :
    source.aromaticCanonicalTetrahedralCenters.Nodup := by
  unfold aromaticCanonicalTetrahedralCenters
  apply List.Nodup.map
  · intro left right equal
    apply Subtype.ext
    exact congrArg
      (fun center : source.AromaticCanonicalTetrahedralCenter => center.1) equal
  · exact (Finset.sort_nodup source.aromaticCanonicalTetrahedralCenterSet
      (fun left right => left ≤ right)).attach

/-- For arbitrary lawful occurrence semantics, the scheduled source tetrahedral result is
duplicate-free because every emitted record retains its unique source center. -/
theorem analyzeAromaticCanonicalScheduledRule3Through6_nodup
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalScheduledRule3Through6
      semantics ruleFuel).Nodup := by
  unfold analyzeAromaticCanonicalScheduledRule3Through6
  apply source.aromaticCanonicalTetrahedralCenters_nodup.filterMap
  intro left right assignment leftEmitted rightEmitted
  cases leftComputed : source.aromaticCanonicalScheduledRule3Through6Descriptor?
      semantics ruleFuel left with
  | none => simp [leftComputed] at leftEmitted
  | some leftDescriptor =>
      cases rightComputed : source.aromaticCanonicalScheduledRule3Through6Descriptor?
          semantics ruleFuel right with
      | none => simp [rightComputed] at rightEmitted
      | some rightDescriptor =>
          simp [leftComputed] at leftEmitted
          simp [rightComputed] at rightEmitted
          exact
            (congrArg AromaticCanonicalScheduledRule3Through6Assignment.center
              leftEmitted).trans
            (congrArg AromaticCanonicalScheduledRule3Through6Assignment.center
              rightEmitted).symm

/-- The parameter-free concrete source tetrahedral analyzer is duplicate-free. -/
theorem analyzeAromaticCanonicalConcreteRule3Through6_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalConcreteRule3Through6
      carrierFuel ruleFuel).Nodup := by
  unfold analyzeAromaticCanonicalConcreteRule3Through6
  exact source.analyzeAromaticCanonicalScheduledRule3Through6_nodup
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel

/-- At the uniform finite bound, every chemically ready source center has exactly one assignment
in the concrete whole-source tetrahedral result. -/
theorem existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound
      carrierFuel center) :
    ∃! assignment,
      assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
          carrierFuel (2 * (carrierFuel + 1)) ∧
        assignment.center = center := by
  obtain ⟨descriptor, computed⟩ :=
    source.exists_aromaticCanonicalConcreteRule3Through6Descriptor?_at_bound
      carrierFuel center ready
  let assignment : source.AromaticCanonicalScheduledRule3Through6Assignment :=
    { center, descriptor }
  have assignmentPresent : assignment ∈
      source.analyzeAromaticCanonicalConcreteRule3Through6
        carrierFuel (2 * (carrierFuel + 1)) := by
    unfold analyzeAromaticCanonicalConcreteRule3Through6
    exact (source.mem_analyzeAromaticCanonicalScheduledRule3Through6_iff
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))
      (2 * (carrierFuel + 1)) assignment).mpr computed
  refine ⟨assignment, ⟨assignmentPresent, rfl⟩, ?_⟩
  intro other ⟨otherPresent, otherCenter⟩
  have otherComputed :
      source.aromaticCanonicalConcreteRule3Through6Descriptor?
          carrierFuel (2 * (carrierFuel + 1)) other.center = some other.descriptor := by
    unfold analyzeAromaticCanonicalConcreteRule3Through6 at otherPresent
    exact (source.mem_analyzeAromaticCanonicalScheduledRule3Through6_iff
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))
      (2 * (carrierFuel + 1)) other).mp otherPresent
  have descriptorIdentity : other.descriptor = descriptor := by
    rw [otherCenter, computed] at otherComputed
    exact Option.some.inj otherComputed.symm
  cases other with
  | mk otherCenterValue otherDescriptorValue =>
      simp only at otherCenter descriptorIdentity
      subst otherCenterValue
      subst otherDescriptorValue
      rfl

/-- The assignment for a chemically ready center has literal list count one. -/
theorem exists_count_analyzeAromaticCanonicalConcreteRule3Through6_eq_one_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound
      carrierFuel center) :
    ∃ assignment,
      assignment.center = center ∧
        (source.analyzeAromaticCanonicalConcreteRule3Through6
          carrierFuel (2 * (carrierFuel + 1))).count assignment = 1 := by
  obtain ⟨assignment, property, _unique⟩ :=
    source.existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6_at_bound
      carrierFuel center ready
  refine ⟨assignment, property.2, ?_⟩
  rw [(source.analyzeAromaticCanonicalConcreteRule3Through6_nodup
    carrierFuel (2 * (carrierFuel + 1))).count]
  simp [property.1]

/-! ## Exact-once transport into the complete represented source result -/

/-- Canonical injection of a tetrahedral assignment through every disjoint scheduler layer. -/
def embedTetrahedralInConcreteStereochemicalResult
    (source : AuthoritativeChemicalInput)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment) :
    source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes :=
  .prior (.prior (.prior (.tetrahedral assignment)))

/-- Injection through the four successive scheduler extensions preserves the exact tetrahedral
family count. In particular, none of the ordinary-double-bond, odd-open-cumulene,
even-open-cumulene, or fully cyclic branches can collide with a tetrahedral result. -/
theorem count_embedTetrahedralInConcreteStereochemicalResult
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
      carrierFuel ruleFuel).count
        (source.embedTetrahedralInConcreteStereochemicalResult assignment) =
      (source.analyzeAromaticCanonicalConcreteRule3Through6
        carrierFuel ruleFuel).count assignment := by
  simp only [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene,
    analyzeAromaticCanonicalConcreteStereochemistry,
    List.map_append, List.map_map, List.count_append]
  have tetrahedralCount :
      List.count (source.embedTetrahedralInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ∘
              AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.prior ∘
                AromaticCanonicalConcreteStereochemicalAssignment.tetrahedral)
          (source.analyzeAromaticCanonicalConcreteRule3Through6
            carrierFuel ruleFuel)) =
        List.count assignment
          (source.analyzeAromaticCanonicalConcreteRule3Through6
            carrierFuel ruleFuel) := by
    exact List.count_map_of_injective _ _ (by
      intro left right equal
      cases equal
      rfl) assignment
  have ordinaryDoubleBondZero :
      List.count (source.embedTetrahedralInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ∘
              AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.prior ∘
                AromaticCanonicalConcreteStereochemicalAssignment.ordinaryDoubleBond)
          (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedTetrahedralInConcreteStereochemicalResult])
  have oddOpenCumuleneZero :
      List.count (source.embedTetrahedralInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ∘
              AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.oddOpenCumulene)
          (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedTetrahedralInConcreteStereochemicalResult])
  have evenOpenCumuleneZero :
      List.count (source.embedTetrahedralInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.evenOpenCumulene)
          (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedTetrahedralInConcreteStereochemicalResult])
  have cyclicZero :
      List.count (source.embedTetrahedralInConcreteStereochemicalResult assignment)
        (List.map
          AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent
          source.aromaticCanonicalCyclicCumuleneComponents) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedTetrahedralInConcreteStereochemicalResult])
  rw [tetrahedralCount, ordinaryDoubleBondZero, oddOpenCumuleneZero,
    evenOpenCumuleneZero, cyclicZero]
  omega

/-- Every chemically ready source center at the uniform finite bound occurs with literal count one
in the actual five-branch public result. -/
theorem exists_count_embeddedTetrahedral_eq_one_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound
      carrierFuel center) :
    ∃ assignment,
      assignment.center = center ∧
        (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
          carrierFuel (2 * (carrierFuel + 1))).count
            (source.embedTetrahedralInConcreteStereochemicalResult assignment) = 1 := by
  obtain ⟨assignment, centerIdentity, countOne⟩ :=
    source.exists_count_analyzeAromaticCanonicalConcreteRule3Through6_eq_one_at_bound
      carrierFuel center ready
  exact ⟨assignment, centerIdentity, by
    rw [source.count_embedTetrahedralInConcreteStereochemicalResult]
    exact countOne⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
