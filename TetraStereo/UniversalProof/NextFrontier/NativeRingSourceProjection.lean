import TetraStereo.UniversalProof.NextFrontier.NativeRingSourceGeometry
import TetraStereo.UniversalProof.NextFrontier.NativeRingSourceSparseOrdering

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingSourceProjection

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingSourceInput
open TetraStereo.UniversalProof.NativeRingSourceGeometry
open TetraStereo.UniversalProof.NativeRingSourceSparseOrdering
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering hiding carbonRootLayer

-- Retain the source abstraction while specializing projection lemmas.
attribute [local irreducible] ringSource

private theorem three_observations_natural (source : AuthoritativeChemicalInput)
    (cursor : source.AromaticCanonicalRerootCursor 1) (a b c : Nat)
    (observed : ((source.aromaticCanonicalRerootChildren cursor).map (fun child =>
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation child.occurrence.1.node)).Perm
        [.ofNat a, .ofNat b, .ofNat c]) :
    ∀ child ∈ source.aromaticCanonicalRerootChildren cursor,
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation child.occurrence.1.node =
        .ofNat ((source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator) := by
  intro child member
  have natural := observed.mem_iff.mp (List.mem_map.mpr ⟨child, member, rfl⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at natural
  rcases natural with first | second | third
  · rw [first]; rfl
  · rw [second]; rfl
  · rw [third]; rfl

/-- Actual production keys on the converter's expanded ring graph, at carrier one/rule fuel
four, have the independently derived two-layer projections under every dependency view. -/
theorem actual_projections (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    ExactOfficialRuleMajorKey.exactRule1aLayers (ringSource n parity).molecule.toLocalizedMoleculeGraph
      ((ringViewKeys n parity 1 view).keyAt (ringRoleSlot n parity 1 2 (by simp))).rule3.constitutional.sourceNodes =
        [carbonRootLayer, chlorinatedArmLayer] ∧
    ExactOfficialRuleMajorKey.exactRule1aLayers (ringSource n parity).molecule.toLocalizedMoleculeGraph
      ((ringViewKeys n parity 1 view).keyAt (ringRoleSlot n parity 1 (n + 4) (by simp))).rule3.constitutional.sourceNodes =
        [carbonRootLayer, saturatedArmLayer] := by
  have observed := actual_child_observations n parity
  have leftNode := ring_role_root_node n parity 1 2 (by simp) (by rw [expanded_atom_count]; omega)
  have rightNode := ring_role_root_node n parity 1 (n + 4) (by simp) (by rw [expanded_atom_count]; omega)
  change (leftCursor n parity).occurrence.1.node = _ at leftNode
  change (rightCursor n parity).occurrence.1.node = _ at rightNode
  have leftLive : (ringSource n parity).aromaticCanonicalRerootChildren (leftCursor n parity) ≠ [] := by
    intro empty
    have count := observed.1.length_eq
    rw [empty] at count
    cases count
  have rightLive : (ringSource n parity).aromaticCanonicalRerootChildren (rightCursor n parity) ≠ [] := by
    intro empty
    have count := observed.2.length_eq
    rw [empty] at count
    cases count
  have leftBranch := production_keyFrame_branch (ringSource n parity) _ view 4
    (ringFrame n parity 1) (ringViewKeys n parity 1 view) (ring_view_keys_computed n parity 1 view)
    (ringRoleSlot n parity 1 2 (by simp)) leftLive
  have rightBranch := production_keyFrame_branch (ringSource n parity) _ view 4
    (ringFrame n parity 1) (ringViewKeys n parity 1 view) (ring_view_keys_computed n parity 1 view)
    (ringRoleSlot n parity 1 (n + 4) (by simp)) rightLive
  have leftRoot : (ringSource n parity).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (leftCursor n parity).occurrence.1.node = .ofNat 6 := by
    rw [leftNode, MoleculeGraph.exactOfficialRule1aObservation_rootFromEdge,
      converted_atomic_number (expanded n parity) (ringSource n parity) (ring_annotation_agreement n parity).1]
    exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat (expanded_left_z n parity)
  have rightRoot : (ringSource n parity).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (rightCursor n parity).occurrence.1.node = .ofNat 6 := by
    rw [rightNode, MoleculeGraph.exactOfficialRule1aObservation_rootFromEdge,
      converted_atomic_number (expanded n parity) (ringSource n parity) (ring_annotation_agreement n parity).1]
    exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat (expanded_chain_z n parity n (by omega))
  have leftNumbers := observed.1.map DeclarativeCIP.ExactAtomicNumber.numerator
  have rightNumbers := observed.2.map DeclarativeCIP.ExactAtomicNumber.numerator
  simp only [List.map_map, List.map_cons, List.map_nil, DeclarativeCIP.ExactAtomicNumber.ofNat]
    at leftNumbers rightNumbers
  have left := source_three_leaf_projection (ringSource n parity) (ringCenter n parity)
    (leftCursor n parity) (ring_frame_cursor_mem n parity 1 (ringRoleSlot n parity 1 2 (by simp))) (by rw [leftNode]; rfl)
    ((ringViewKeys n parity 1 view).keyAt (ringRoleSlot n parity 1 2 (by simp))).rule3
    (ringViewKeys n parity 1 view).rule3Frame.excluded 4 leftBranch 6 17 6 1 leftRoot
    leftNumbers (three_observations_natural _ _ 17 6 1 observed.1) (by decide)
  have right := source_three_leaf_projection (ringSource n parity) (ringCenter n parity)
    (rightCursor n parity) (ring_frame_cursor_mem n parity 1 (ringRoleSlot n parity 1 (n + 4) (by simp))) (by rw [rightNode]; rfl)
    ((ringViewKeys n parity 1 view).keyAt (ringRoleSlot n parity 1 (n + 4) (by simp))).rule3
    (ringViewKeys n parity 1 view).rule3Frame.excluded 4 rightBranch 6 6 1 1 rightRoot
    rightNumbers (three_observations_natural _ _ 6 1 1 observed.2) (by decide)
  exact ⟨left, right⟩

theorem actual_rule3_keys_both (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    (ringSource n parity).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((ringViewKeys n parity 1 view).keyAt (ringRoleSlot n parity 1 2 (by simp))).rule3
      ((ringViewKeys n parity 1 view).keyAt (ringRoleSlot n parity 1 (n + 4) (by simp))).rule3 = .gt ∧
    (ringSource n parity).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((ringViewKeys n parity 1 view).keyAt (ringRoleSlot n parity 1 (n + 4) (by simp))).rule3
      ((ringViewKeys n parity 1 view).keyAt (ringRoleSlot n parity 1 2 (by simp))).rule3 = .lt := by
  have projections := actual_projections n parity view
  have atomic := chlorinated_arm_above_saturated [] []
  constructor <;> simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, ExactOfficialRuleMajorKey.compare,
    ExactOfficialRuleMajorKey.compareAddressedSources, Ordering.byKey, compareLex,
    projections.1, projections.2, atomic.1, atomic.2]

theorem actual_carbon_callback_both (n : Nat) (parity : TetrahedralInputParity)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))) :
    (ringSource n parity).compareAromaticCanonicalOccurrenceRule3Through5At? (ringViewKeys n parity 1 view)
      (ringRoleSlot n parity 1 2 (by simp)) (ringRoleSlot n parity 1 (n + 4) (by simp)) =
        some { ordering := .gt, decisiveRule? := none, pseudo := false } ∧
    (ringSource n parity).compareAromaticCanonicalOccurrenceRule3Through5At? (ringViewKeys n parity 1 view)
      (ringRoleSlot n parity 1 (n + 4) (by simp)) (ringRoleSlot n parity 1 2 (by simp)) =
        some { ordering := .lt, decisiveRule? := none, pseudo := false } := by
  have strict := actual_rule3_keys_both n parity view
  constructor <;> simp [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
    compareAromaticCanonicalOccurrenceRule3Through5At, strict.1, strict.2]

end TetraStereo.UniversalProof.NativeRingSourceProjection
