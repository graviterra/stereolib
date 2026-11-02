import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceChildObservations
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSecondSphereOrder

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceProjection

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileSecondSphereOrder
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering hiding carbonRootLayer

-- Keep the converted source abstract during projection elaboration.
attribute [local irreducible] expanded

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

/-- Actual production keys on the converter's expanded nitrile graph, at carrier one/rule fuel
four, have the independently derived two-layer projections under every dependency view. -/
theorem actual_projections (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    ExactOfficialRuleMajorKey.exactRule1aLayers (nitrileSource parity n).molecule.toLocalizedMoleculeGraph
      ((nitrileViewKeys parity n 1 view).keyAt (nitrileRoleSlot parity n 1 2 (by simp))).rule3.constitutional.sourceNodes =
        [carbonRootLayer, nitrileChildLayer] ∧
    ExactOfficialRuleMajorKey.exactRule1aLayers (nitrileSource parity n).molecule.toLocalizedMoleculeGraph
      ((nitrileViewKeys parity n 1 view).keyAt (nitrileRoleSlot parity n 1 4 (by simp))).rule3.constitutional.sourceNodes =
        [carbonRootLayer, aminoalkylChildLayer] := by
  have observed := actual_source_child_observations parity n
  have leftNode := nitrile_role_root_node parity n 1 2 (by simp) (by rw [expanded_atomCount]; omega)
  have rightNode := nitrile_role_root_node parity n 1 4 (by simp) (by rw [expanded_atomCount]; omega)
  change (sourceNitrileCursor parity n).occurrence.1.node = _ at leftNode
  change (sourceAminoCursor parity n).occurrence.1.node = _ at rightNode
  have leftLive : (nitrileSource parity n).aromaticCanonicalRerootChildren (sourceNitrileCursor parity n) ≠ [] := by
    intro empty
    have count := observed.1.length_eq
    rw [empty] at count
    cases count
  have rightLive : (nitrileSource parity n).aromaticCanonicalRerootChildren (sourceAminoCursor parity n) ≠ [] := by
    intro empty
    have count := observed.2.length_eq
    rw [empty] at count
    cases count
  have leftBranch := production_keyFrame_branch (nitrileSource parity n) _ view 4
    (nitrileFrame parity n 1) (nitrileViewKeys parity n 1 view) (nitrile_view_keys_computed parity n 1 view)
    (nitrileRoleSlot parity n 1 2 (by simp)) leftLive
  have rightBranch := production_keyFrame_branch (nitrileSource parity n) _ view 4
    (nitrileFrame parity n 1) (nitrileViewKeys parity n 1 view) (nitrile_view_keys_computed parity n 1 view)
    (nitrileRoleSlot parity n 1 4 (by simp)) rightLive
  have leftRoot : (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (sourceNitrileCursor parity n).occurrence.1.node = .ofNat 6 := by
    rw [leftNode, MoleculeGraph.exactOfficialRule1aObservation_rootFromEdge,
      converted_atomic_number (expanded parity n) (nitrileSource parity n) (expanded_source_annotation_agreement parity n).1]
    exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat ((expanded_local_atomic_numbers parity n).2.2.1)
  have rightRoot : (nitrileSource parity n).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (sourceAminoCursor parity n).occurrence.1.node = .ofNat 6 := by
    rw [rightNode, MoleculeGraph.exactOfficialRule1aObservation_rootFromEdge,
      converted_atomic_number (expanded parity n) (nitrileSource parity n) (expanded_source_annotation_agreement parity n).1]
    exact congrArg DeclarativeCIP.ExactAtomicNumber.ofNat ((expanded_local_atomic_numbers parity n).2.2.2.2.1)
  have leftNumbers := observed.1.map DeclarativeCIP.ExactAtomicNumber.numerator
  have rightNumbers := observed.2.map DeclarativeCIP.ExactAtomicNumber.numerator
  simp only [List.map_map, List.map_cons, List.map_nil, DeclarativeCIP.ExactAtomicNumber.ofNat]
    at leftNumbers rightNumbers
  have left := source_three_leaf_projection (nitrileSource parity n) (nitrileCenter parity n)
    (sourceNitrileCursor parity n) (nitrile_frame_cursor_mem parity n 1 (nitrileRoleSlot parity n 1 2 (by simp))) (by rw [leftNode]; rfl)
    ((nitrileViewKeys parity n 1 view).keyAt (nitrileRoleSlot parity n 1 2 (by simp))).rule3
    (nitrileViewKeys parity n 1 view).rule3Frame.excluded 4 leftBranch 6 7 7 7 leftRoot
    leftNumbers (three_observations_natural _ _ 7 7 7 observed.1) (by decide)
  have right := source_three_leaf_projection (nitrileSource parity n) (nitrileCenter parity n)
    (sourceAminoCursor parity n) (nitrile_frame_cursor_mem parity n 1 (nitrileRoleSlot parity n 1 4 (by simp))) (by rw [rightNode]; rfl)
    ((nitrileViewKeys parity n 1 view).keyAt (nitrileRoleSlot parity n 1 4 (by simp))).rule3
    (nitrileViewKeys parity n 1 view).rule3Frame.excluded 4 rightBranch 6 7 6 1 rightRoot
    rightNumbers (three_observations_natural _ _ 7 6 1 observed.2) (by decide)
  exact ⟨left, right⟩

theorem actual_rule3_keys_both (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    (nitrileSource parity n).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((nitrileViewKeys parity n 1 view).keyAt (nitrileRoleSlot parity n 1 2 (by simp))).rule3
      ((nitrileViewKeys parity n 1 view).keyAt (nitrileRoleSlot parity n 1 4 (by simp))).rule3 = .gt ∧
    (nitrileSource parity n).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((nitrileViewKeys parity n 1 view).keyAt (nitrileRoleSlot parity n 1 4 (by simp))).rule3
      ((nitrileViewKeys parity n 1 view).keyAt (nitrileRoleSlot parity n 1 2 (by simp))).rule3 = .lt := by
  have projections := actual_projections n parity view
  have atomic := NativeNitrileSecondSphereOrder.second_sphere_sparse_both [] []
  constructor <;> simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, ExactOfficialRuleMajorKey.compare,
    ExactOfficialRuleMajorKey.compareAddressedSources, Ordering.byKey, compareLex,
    projections.1, projections.2, atomic.1, atomic.2]

theorem actual_carbon_callback_both (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    (nitrileSource parity n).compareAromaticCanonicalOccurrenceRule3Through5At? (nitrileViewKeys parity n 1 view)
      (nitrileRoleSlot parity n 1 2 (by simp)) (nitrileRoleSlot parity n 1 4 (by simp)) =
        some { ordering := .gt, decisiveRule? := none, pseudo := false } ∧
    (nitrileSource parity n).compareAromaticCanonicalOccurrenceRule3Through5At? (nitrileViewKeys parity n 1 view)
      (nitrileRoleSlot parity n 1 4 (by simp)) (nitrileRoleSlot parity n 1 2 (by simp)) =
        some { ordering := .lt, decisiveRule? := none, pseudo := false } := by
  have strict := actual_rule3_keys_both n parity view
  constructor <;> simp [compareAromaticCanonicalOccurrenceRule3Through5At?, aromaticCanonicalRule3Through5DescriptorComparison,
    compareAromaticCanonicalOccurrenceRule3Through5At, strict.1, strict.2]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceProjection
