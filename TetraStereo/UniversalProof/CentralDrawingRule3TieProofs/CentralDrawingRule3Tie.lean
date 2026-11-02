import TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison
import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyNonvacuitySeed
import TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingLeafRefusal

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

/-!
The two actual central carbon ligands tie through Rule 3. Only the retained semantic molecule's
constitutional atom/occurrence involution and its pure cursor topology are reused from the old
fixture. The key frame and exclusion-aware observations belong to the new drawing-only source.
No old spatial descriptor, auxiliary label, chosen partition or model is transported.
This closes the Rule-3 premise of the central Rule-5 reduction; the complete Rule-4b/4c prior tie
and final descriptor assembly remain separate obligations.
-/

def branchSwapAtoms : Equiv.Perm source.AromaticCanonicalAtom :=
  IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.branchSwapAtomPermutation

theorem branchSwapAtoms_constitution :
    source.AromaticCanonicalConstitutionAutomorphism branchSwapAtoms :=
  IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.branchSwapAtomPermutation_constitution

private theorem source_no_aromatic_edges : source.molecule.aromaticPairEdges = [] := rfl

private theorem source_children_nodup (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount node).Nodup :=
  aromaticCanonicalOfficialCIPChildrenAt_nodup_of_no_edges_of_single
    source.molecule source.molecule.atomCount source_no_aromatic_edges
      IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.source_aromaticCanonicalBondOrder_le_one
        node

/-- Constructed on the actual drawing source's carrier, independently of the old occurrence type. -/
noncomputable def branchSwapOccurrence :
    Equiv.Perm (source.AromaticCanonicalOccurrence branchCarrierFuel) :=
  aromaticCanonicalOccurrencePermutationOfInvolution source branchCarrierFuel branchSwapAtoms
    branchSwapAtoms_constitution
      IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.branchSwapAtomPermutation_involutive
        source_no_aromatic_edges source_children_nodup

noncomputable def branchSwapCursor
    (cursor : source.AromaticCanonicalRerootCursor branchCarrierFuel) :
    source.AromaticCanonicalRerootCursor branchCarrierFuel :=
  { occurrence := branchSwapOccurrence cursor.occurrence
    previous? := cursor.previous?.map branchSwapOccurrence }

theorem branchSwapCursor_maps_central_two :
    branchSwapCursor (centralRootAt centralSlotTwo) = centralRootAt centralSlotThree := by
  apply AuthoritativeChemicalInput.AromaticCanonicalRerootCursor.ext
  · apply Subtype.ext
    rfl
  · rfl

private theorem branchSwapCursor_node
    (cursor : source.AromaticCanonicalRerootCursor branchCarrierFuel) :
    (branchSwapCursor cursor).occurrence.1.node =
      mapAromaticCanonicalOfficialCIPNode branchSwapAtoms cursor.occurrence.1.node := by
  rfl

private theorem leftChildren_explicit :
    source.aromaticCanonicalRerootChildren (centralRootAt centralSlotTwo) =
      [leftContinuingChildAt ⟨0, by decide⟩, leftContinuingChildAt ⟨1, by decide⟩,
        leftContinuingChildAt ⟨2, by decide⟩] :=
  IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.list_eq_three_get _
    continuing_children_lengths.1

private theorem rightChildren_explicit :
    source.aromaticCanonicalRerootChildren (centralRootAt centralSlotThree) =
      [rightContinuingChildAt ⟨0, by decide⟩, rightContinuingChildAt ⟨1, by decide⟩,
        rightContinuingChildAt ⟨2, by decide⟩] :=
  IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.list_eq_three_get _
    continuing_children_lengths.2

private theorem branchSwapCursor_maps_child (slot : Fin 3) :
    branchSwapCursor (leftContinuingChildAt slot) = rightContinuingChildAt slot := by
  fin_cases slot <;> apply AuthoritativeChemicalInput.AromaticCanonicalRerootCursor.ext
  all_goals rfl

private theorem rightChildren_eq_map :
    source.aromaticCanonicalRerootChildren (centralRootAt centralSlotThree) =
      (source.aromaticCanonicalRerootChildren (centralRootAt centralSlotTwo)).map
        branchSwapCursor := by
  rw [leftChildren_explicit, rightChildren_explicit]
  simp [branchSwapCursor_maps_child]

private theorem child_cursor_automorphism_natural (fuel : Nat) (slot : Fin 3) :
    AromaticCanonicalRule3CursorAutomorphismNatural source branchSwapAtoms branchSwapCursor
      fuel (leftContinuingChildAt slot) := by
  cases fuel with
  | zero =>
      exact ⟨branchSwapCursor_node _, by
        rw [branchSwapCursor_maps_child,
          rightContinuingChild_children_empty, leftContinuingChild_children_empty]
        rfl⟩
  | succ fuel =>
      exact ⟨branchSwapCursor_node _, by
        rw [branchSwapCursor_maps_child,
          rightContinuingChild_children_empty, leftContinuingChild_children_empty]
        rfl, by simp [leftContinuingChild_children_empty]⟩

/-- Actual three-leaf branch topology, reconstructed on the drawing-only source. -/
theorem central_cursor_automorphism_natural :
    AromaticCanonicalRule3CursorAutomorphismNatural source branchSwapAtoms branchSwapCursor
      4 (centralRootAt centralSlotTwo) := by
  unfold AromaticCanonicalRule3CursorAutomorphismNatural
  refine ⟨branchSwapCursor_node _, ?_, ?_⟩
  · rw [branchSwapCursor_maps_central_two]
    exact rightChildren_eq_map
  · intro child present
    rw [leftChildren_explicit] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    all_goals exact child_cursor_automorphism_natural 3 _

private theorem source_exact_aromatic_edges :
    source.molecule.SemanticAromaticMancudeEdgeSetExact source.molecule :=
  IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.source_aromaticMancudeEdgeSetExact

theorem central_rule3_node_except_none
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3SpatialNodeExcept? excluded node = some none := by
  have notEdge : ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node := by
    rintro ⟨_, current, parent, _, _, ordinary⟩
    exact source_no_ordinary_double_bond parent current ordinary
  have absent := source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge node notEdge
  simp [aromaticCanonicalRule3SpatialNodeExcept?, absent]

theorem central_rule3_node_except_map_natural
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3SpatialNodeExcept? excluded
        (mapAromaticCanonicalOfficialCIPNode branchSwapAtoms node) =
      source.aromaticCanonicalRule3SpatialNodeExcept? excluded node := by
  rw [central_rule3_node_except_none, central_rule3_node_except_none]

private theorem keyFrame_rule3_computed
    (input : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : input.AromaticCanonicalOccurrence carrierFuel)
    (view : input.AromaticCanonicalDependencyView target) (fuel : Nat)
    (roots : List (input.AromaticCanonicalRerootCursor carrierFuel))
    (frame : input.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : input.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel roots = some frame) :
    input.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel roots = some frame.rule3Frame := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? at computed
  cases rule3Computed : input.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel roots with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases length3 : rule3Frame.keys.length = 4
      · cases keysComputed : roots.mapM
            (input.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) with
        | none => simp [rule3Computed, keysComputed] at computed
        | some keys =>
            by_cases length45 : keys.length = 4
            · simp [rule3Computed, length3, keysComputed, length45] at computed
              subst frame
              rfl
            · simp [rule3Computed, keysComputed, length45] at computed
      · simp [rule3Computed, length3] at computed

theorem central_rule3Frame_computed :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? 4 centralRoots =
      some centralKeyFrame.rule3Frame :=
  keyFrame_rule3_computed source centralTarget centralView 4 centralRoots
    centralKeyFrame centralKeyFrame_computed

private theorem canonicalExceptList_forall₂
    {input : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List input.AromaticCanonicalRule3PhysicalUnitId}
    {roots : List (input.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List input.AromaticCanonicalUncancelledRule3SpatialKey}
    (canonical : input.CanonicalAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel roots keys) :
    List.Forall₂ (input.CanonicalAromaticCanonicalRule3SpatialKeyExcept excluded fuel) roots keys :=
  match canonical with
  | .nil _ => .nil
  | .cons head tail => .cons head (canonicalExceptList_forall₂ tail)

/-- Every actual production slot retains its own exclusion-aware compiled Rule-3 key. -/
theorem central_rule3_keyAt_computed (slot : Fin 4) :
    source.buildAromaticCanonicalRule3SpatialKeyExcept? centralKeyFrame.rule3Frame.excluded
      4 (centralRootAt slot) = some (centralKeyFrame.keyAt slot).rule3 := by
  have canonical := (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
    4 centralRoots centralKeyFrame.rule3Frame).mp central_rule3Frame_computed
  have pointwise := canonicalExceptList_forall₂ canonical.2.2.2
  apply (source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
    centralKeyFrame.rule3Frame.excluded 4 (centralRootAt slot)
      (centralKeyFrame.keyAt slot).rule3).mpr
  exact pointwise.get (i := slot.val)
    (by rw [central_roots_length]; exact slot.isLt)
    (by rw [centralKeyFrame.rule3Length]; exact slot.isLt)

theorem central_rule3_build_right_eq_map_left :
    source.buildAromaticCanonicalRule3SpatialKeyExcept? centralKeyFrame.rule3Frame.excluded
        4 (centralRootAt centralSlotThree) =
      (source.buildAromaticCanonicalRule3SpatialKeyExcept? centralKeyFrame.rule3Frame.excluded
        4 (centralRootAt centralSlotTwo)).map
          (mapAromaticCanonicalUncancelledRule3SpatialKey branchSwapAtoms) := by
  rw [← branchSwapCursor_maps_central_two,
    source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_with]
  exact buildAromaticCanonicalRule3SpatialKeyWith?_automorphism_natural_of_cursor
    source branchSwapAtoms branchSwapCursor
    (source.aromaticCanonicalRule3SpatialNodeExcept? centralKeyFrame.rule3Frame.excluded)
    (central_rule3_node_except_map_natural centralKeyFrame.rule3Frame.excluded)
    (compareAromaticCanonicalUncancelledRule3SpatialKeys_map_natural_of_constitution_of_no_edges
      source branchSwapAtoms branchSwapAtoms_constitution source_exact_aromatic_edges
        source_no_aromatic_edges)
    4 (centralRootAt centralSlotTwo) central_cursor_automorphism_natural

theorem central_rule3_right_eq_map_left :
    (centralKeyFrame.keyAt centralSlotThree).rule3 =
      mapAromaticCanonicalUncancelledRule3SpatialKey branchSwapAtoms
        (centralKeyFrame.keyAt centralSlotTwo).rule3 := by
  have transported := central_rule3_build_right_eq_map_left
  rw [central_rule3_keyAt_computed centralSlotThree,
    central_rule3_keyAt_computed centralSlotTwo] at transported
  exact Option.some.inj transported

/-- Complete actual Rule-3 comparison, with no supplied comparator or label-success premise. -/
theorem central_rule3_tie :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule3
      (centralKeyFrame.keyAt centralSlotThree).rule3 = Ordering.eq := by
  rw [central_rule3_right_eq_map_left]
  exact compareAromaticCanonicalUncancelledRule3SpatialKeys_self_map_eq_of_observations
    source branchSwapAtoms
    (exactOfficialRule1aObservation_natural_of_constitution_of_no_edges source branchSwapAtoms
      branchSwapAtoms_constitution source_exact_aromatic_edges source_no_aromatic_edges)
    (officialNodeRule2_natural_of_constitution source branchSwapAtoms branchSwapAtoms_constitution)
    (centralKeyFrame.keyAt centralSlotTwo).rule3

theorem central_rule3_tie_reversed :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotThree).rule3
      (centralKeyFrame.keyAt centralSlotTwo).rule3 = Ordering.eq := by
  letI := source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
  rw [Std.OrientedCmp.eq_swap
    (cmp := source.compareAromaticCanonicalUncancelledRule3SpatialKeys)
    (a := (centralKeyFrame.keyAt centralSlotThree).rule3)
    (b := (centralKeyFrame.keyAt centralSlotTwo).rule3), central_rule3_tie]
  rfl

end TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison
