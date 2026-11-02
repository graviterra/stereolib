import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5FixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RawMolecule
open Rule6ReferenceFamilySemantics
open AuthoritativeCIPRule6P92Enumeration
open RationalTetrahedralPermutation
open Rule6FourWayFamilySemantics
open DeclarativeCIP.ProductionOccurrenceRules456

namespace RationalTetrahedralPermutation

/-!
# End-to-end exact geometry for the source-canonical Rule-3--6 route

This module threads the exact parity/permutation theorem through the real source ranking backend,
all three P-92 Rule-6 carrier branches, the scheduled molecule judgment, and the concrete causal
fixed-point analyzer.  A deliberate quotient/pseudoasymmetric descriptor reversal is represented
geometrically by an explicit odd swap of the first two priority-ordered points.
-/

/-- Exchange the first two members of a point list, leaving every later member fixed. -/
def swapFirstTwoPoints : List CartesianPoint3 → List CartesianPoint3
  | first :: second :: rest => second :: first :: rest
  | points => points

private theorem orientedVolume_swap_first_two
    (first second third fourth : CartesianPoint3) :
    CartesianPoint3.orientedVolume second first third fourth =
      -CartesianPoint3.orientedVolume first second third fourth := by
  simp [CartesianPoint3.orientedVolume]
  ring

/-- An explicit first-two point swap reverses the exact rational `R/S` descriptor. -/
theorem rationalTetrahedralDescriptor_swapFirstTwoPoints
    {points : List CartesianPoint3} {descriptor : RS}
    (correct : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
      points descriptor) :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
      (swapFirstTwoPoints points) (RS.swap descriptor) := by
  rcases correct with ⟨first, second, third, fourth, rfl, sign⟩
  cases descriptor with
  | R =>
      refine ⟨second, first, third, fourth, rfl, ?_⟩
      rw [orientedVolume_swap_first_two]
      exact neg_pos.mpr sign
  | S =>
      refine ⟨second, first, third, fourth, rfl, ?_⟩
      rw [orientedVolume_swap_first_two]
      exact neg_neg_of_pos sign

/-- Geometric meaning of one ranking, with an optional explicit orientation-reversing carrier
swap. -/
def RationalRule6RankingDescriptor (points : List CartesianPoint3)
    (positions : List Nat) (reverse : Bool) (descriptor : RS) : Prop :=
  ∃ reordered,
    FinFourPriorityReordering points positions reordered ∧
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        (if reverse then swapFirstTwoPoints reordered else reordered) descriptor

/-- Exact written-order parity plus a genuine priority permutation proves the geometric meaning
of either the direct descriptor or its explicit odd-swap reversal. -/
theorem rationalRule6RankingDescriptor_of_formula
    (points : List CartesianPoint3) (positions : List Nat)
    (parity : TetrahedralInputParity) (reverse : Bool) (descriptor : RS)
    (inputParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity points parity)
    (positionsPermutation : positions.Perm (List.range 4))
    (formula :
      (if reverse then
          RS.swap (RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven positions))
        else
          RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven positions)) = descriptor) :
    RationalRule6RankingDescriptor points positions reverse descriptor := by
  rcases rationalTetrahedralInputParity_priorityReordering
      points positions parity inputParity positionsPermutation with
    ⟨reordered, reordering, correct⟩
  cases reverse with
  | false =>
      refine ⟨reordered, reordering, ?_⟩
      have formula' : RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven positions) = descriptor := by
        simpa only [if_false] using formula
      rw [formula'] at correct
      exact correct
  | true =>
      refine ⟨reordered, reordering, ?_⟩
      have swapped := rationalTetrahedralDescriptor_swapFirstTwoPoints correct
      have formula' : RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven positions)) = descriptor := by
        simpa only [if_true] using formula
      rw [formula'] at swapped
      exact swapped

/-- A ranking backend is position-lawful when every successful result contains each of the four
source positions exactly once. -/
def FourPositionRankingBackend (backend : ProductionRule6RankingBackend) : Prop :=
  ∀ reference ranking,
    backend reference = some ranking → ranking.positions.Perm (List.range 4)

-- Keep `parity` explicit for source-compatible named applications of this public definition.
set_option linter.unusedVariables false in
/-- Geometry-refined common-reference semantics.  Every listed strict reference has an exact
priority-ordered determinant witness for the same effective descriptor. -/
def RationalCommonRule6EffectiveDescriptor
    (backend : ProductionRule6RankingBackend) (points : List CartesianPoint3)
    (parity : TetrahedralInputParity) (references : List Nat)
    (reverse : Bool) (descriptor : RS) : Prop :=
  references ≠ [] ∧
    ∀ reference, reference ∈ references →
      ∃ ranking,
        backend reference = some ranking ∧
          ranking.unique = true ∧
          RationalRule6RankingDescriptor
            points ranking.positions reverse descriptor

/-- A common symbolic Rule-6 reference descriptor refines to the exact determinant descriptor,
including an optional carrier reversal. -/
theorem rationalCommonRule6EffectiveDescriptor_of_common
    (backend : ProductionRule6RankingBackend) (points : List CartesianPoint3)
    (parity : TetrahedralInputParity) (references : List Nat)
    (reverse : Bool) (commonDescriptor descriptor : RS)
    (inputParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity points parity)
    (lawful : FourPositionRankingBackend backend)
    (common : CommonRule6Descriptor backend parity references commonDescriptor)
    (effective :
      (if reverse then RS.swap commonDescriptor else commonDescriptor) = descriptor) :
    RationalCommonRule6EffectiveDescriptor
      backend points parity references reverse descriptor := by
  refine ⟨common.1, ?_⟩
  intro reference member
  rcases common.2 reference member with
    ⟨ranking, accepted, unique, descriptorEq⟩
  refine ⟨ranking, accepted, unique, ?_⟩
  apply rationalRule6RankingDescriptor_of_formula
    points ranking.positions parity reverse descriptor inputParity
      (lawful reference ranking accepted)
  rw [descriptorEq]
  exact effective

/-- Geometry-refined dependent four-way semantics. -/
def RationalAuthoritativeFourWayDescriptorJudgment
    (backend : ProductionRule6RankingBackend) (points : List CartesianPoint3)
    (parity : TetrahedralInputParity) (sorted : List Nat) (descriptor : RS) : Prop :=
  ∃ firstReference first second,
    sorted[0]? = some firstReference ∧
      backend firstReference = some first ∧
      backend (first.positions[1]?.getD 0) = some second ∧
      FourWayCarrierCoherent parity first second ∧
      RationalRule6RankingDescriptor
        points second.positions (!second.unique) descriptor

/-- The dependent four-way symbolic judgment has the exact determinant meaning of its second
prescribed ranking, with non-uniqueness represented by an explicit odd swap. -/
theorem rationalAuthoritativeFourWayDescriptorJudgment_of_judgment
    (backend : ProductionRule6RankingBackend) (points : List CartesianPoint3)
    (parity : TetrahedralInputParity) (sorted : List Nat) (descriptor : RS)
    (inputParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity points parity)
    (lawful : FourPositionRankingBackend backend)
    (judgment : AuthoritativeFourWayDescriptorJudgment
      backend parity sorted descriptor) :
    RationalAuthoritativeFourWayDescriptorJudgment
      backend points parity sorted descriptor := by
  rcases judgment with
    ⟨firstReference, first, second, firstReferenceEq, firstAccepted,
      secondAccepted, coherent, descriptorEq⟩
  refine ⟨firstReference, first, second, firstReferenceEq, firstAccepted,
    secondAccepted, coherent, ?_⟩
  apply rationalRule6RankingDescriptor_of_formula
    points second.positions parity (!second.unique) descriptor inputParity
      (lawful (first.positions[1]?.getD 0) second secondAccepted)
  cases uniqueEq : second.unique <;>
    simp [uniqueEq] at descriptorEq ⊢ <;>
    exact descriptorEq

end RationalTetrahedralPermutation

namespace AuthoritativeChemicalInput

/-- Every successful ranking of the resolved source frame is a lawful four-position backend. -/
theorem aromaticCanonicalRule3Through6RankingBackendForFrame_fourPosition
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    RationalTetrahedralPermutation.FourPositionRankingBackend
      (source.aromaticCanonicalRule3Through6RankingBackendForFrame
        frame target view fuel roots) := by
  intro reference ranking accepted
  exact source.aromaticCanonicalRule3Through6RankingBackendForFrame_positions_perm
    frame target view fuel roots reference ranking accepted

/-- Exact determinant refinement of the complete 1/2/3-group source Rule-6 dispatch.  The first
conjunct retains the full chemical branch judgment; the second adds a determinant witness for the
descriptor in the branch's effective priority order. -/
def AromaticCanonicalRule3Through6GeometricBranchDescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (points : List CartesianPoint3)
    (parity : TetrahedralInputParity) (descriptor : RS) : Prop :=
  source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
      target view fuel roots partition parity descriptor ∧
    let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
      partition.frame.rule3Frame target view fuel roots
    let sorted := partition.sortedPositions
    let adjacent := partition.adjacentOptions
    let groupCount := rule6GroupCount adjacent
    (groupCount = 1 ∧
        RationalTetrahedralPermutation.RationalAuthoritativeFourWayDescriptorJudgment
          backend points parity sorted descriptor) ∨
      (groupCount = 2 ∧
        RationalTetrahedralPermutation.RationalCommonRule6EffectiveDescriptor
          backend points parity (rule6EquivalentReferencePositions sorted adjacent)
            false descriptor) ∨
      (groupCount = 3 ∧
        RationalTetrahedralPermutation.RationalCommonRule6EffectiveDescriptor
          backend points parity (rule6ThreeGroupReferencePositions sorted)
            true descriptor)

/-- The source branch judgment plus exact source-order parity entails an exact determinant
witness in every P-92 carrier branch. -/
theorem aromaticCanonicalRule3Through6BranchDescriptorJudgment_geometry
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (points : List CartesianPoint3)
    (parity : TetrahedralInputParity) (descriptor : RS)
    (inputParity : RationalTetrahedralInputParity points parity)
    (judgment : source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
      target view fuel roots partition parity descriptor) :
    source.AromaticCanonicalRule3Through6GeometricBranchDescriptorJudgment
      target view fuel roots partition points parity descriptor := by
  refine ⟨judgment, ?_⟩
  let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
    partition.frame.rule3Frame target view fuel roots
  let sorted := partition.sortedPositions
  let adjacent := partition.adjacentOptions
  let groupCount := rule6GroupCount adjacent
  have lawful : RationalTetrahedralPermutation.FourPositionRankingBackend backend :=
    source.aromaticCanonicalRule3Through6RankingBackendForFrame_fourPosition
      partition.frame.rule3Frame target view fuel roots
  unfold AromaticCanonicalRule3Through6BranchDescriptorJudgment at judgment
  dsimp only at judgment
  change
    (groupCount = 1 ∧
        AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor) ∨
      (groupCount = 2 ∧ CommonRule6Descriptor backend parity
        (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
      (groupCount = 3 ∧ CommonRule6Descriptor backend parity
        (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor)) at judgment
  rcases judgment with one | two | three
  · exact Or.inl ⟨one.1,
      RationalTetrahedralPermutation.rationalAuthoritativeFourWayDescriptorJudgment_of_judgment
        backend points parity sorted descriptor inputParity lawful one.2⟩
  · exact Or.inr (Or.inl ⟨two.1,
      RationalTetrahedralPermutation.rationalCommonRule6EffectiveDescriptor_of_common
        backend points parity (rule6EquivalentReferencePositions sorted adjacent)
          false descriptor descriptor inputParity lawful two.2 rfl⟩)
  · have effective : RS.swap (RS.swap descriptor) = descriptor := by
      cases descriptor <;> rfl
    exact Or.inr (Or.inr ⟨three.1,
      RationalTetrahedralPermutation.rationalCommonRule6EffectiveDescriptor_of_common
        backend points parity (rule6ThreeGroupReferencePositions sorted)
          true (RS.swap descriptor) descriptor inputParity lawful three.2 effective⟩)

/-- Full source-coordinate and exact-determinant meaning of a scheduled molecule descriptor. -/
def AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS) : Prop :=
  source.ConnectivityOnlyTetrahedralCenterEvidence center ∧
    let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
    let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
    ∃ (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
        (points : List CartesianPoint3) (parity : TetrahedralInputParity)
        (rootsLength : roots.length = 4)
        (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel),
      source.DeclarativeAromaticCanonicalRerootChildren
          { occurrence := target, previous? := none } roots ∧
        List.Forall₂ source.DeclarativeAromaticCanonicalRerootSpatialPoint roots points ∧
        RationalTetrahedralInputParity points parity ∧
        source.DeclarativeAromaticCanonicalRule3Through5InitialPartition
          target (source.aromaticCanonicalDependencyView state target)
            ruleFuel roots partition ∧
        source.AromaticCanonicalRule6TopologyAdmissible
          center.1 roots rootsLength partition ∧
        source.AromaticCanonicalRule3Through6GeometricBranchDescriptorJudgment
          target (source.aromaticCanonicalDependencyView state target)
            ruleFuel roots partition points parity descriptor

/-- The existing complete scheduled judgment refines to a final determinant witness over the
same source coordinates and the same chemically ranked occurrence frame. -/
theorem aromaticCanonicalScheduledRule3Through6DescriptorJudgment_geometry
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS)
    (judgment : source.AromaticCanonicalScheduledRule3Through6DescriptorJudgment
      semantics ruleFuel center descriptor) :
    source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
      semantics ruleFuel center descriptor := by
  unfold AromaticCanonicalScheduledRule3Through6DescriptorJudgment at judgment
  unfold AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
  dsimp only at judgment ⊢
  rcases judgment with ⟨roots, parity, rootsDerived, frameParity, complete⟩
  rcases frameParity with ⟨points, pointsDerived, inputParity⟩
  rcases complete with
    ⟨rootsLength, partition, partitionDerived, topology, branch⟩
  exact ⟨source.aromaticCanonicalTetrahedralCenter_evidence center,
    roots, points, parity, rootsLength, partition, rootsDerived, pointsDerived,
    inputParity, partitionDerived, topology,
    source.aromaticCanonicalRule3Through6BranchDescriptorJudgment_geometry
      _ _ _ _ _ _ _ _ inputParity branch⟩

/-- Every descriptor emitted by the concrete no-callback source analyzer has a final exact
determinant witness after the complete Rules-1a--6 priority dispatch. -/
theorem aromaticCanonicalConcreteRule3Through6Descriptor?_geometry_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS)
    (computed : source.aromaticCanonicalConcreteRule3Through6Descriptor?
      carrierFuel ruleFuel center = some descriptor) :
    source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel) ruleFuel center descriptor := by
  have complete := source.aromaticCanonicalConcreteRule3Through6Descriptor?_sound
    carrierFuel ruleFuel center descriptor computed
  exact source.aromaticCanonicalScheduledRule3Through6DescriptorJudgment_geometry
    _ _ _ _ complete.1

/-- Whole-molecule corollary: every emitted concrete assignment carries the exact source
coordinate determinant semantics of its final descriptor. -/
theorem analyzeAromaticCanonicalConcreteRule3Through6_member_geometry_sound
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment)
    (present : assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
      carrierFuel ruleFuel) :
    source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel) ruleFuel assignment.center assignment.descriptor := by
  apply source.aromaticCanonicalConcreteRule3Through6Descriptor?_geometry_sound
  exact (source.mem_analyzeAromaticCanonicalScheduledRule3Through6_iff
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel assignment).mp present

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
