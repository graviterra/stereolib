import TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction
import TetraStereo.OneCenter.LocalizedMultipleBondShapeRoleRecovery
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.KernelOnly

set_option autoImplicit false








































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open LocalizedMultipleBondOrderReconstruction
open scoped BigOperators

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
variable {tree : LocalizedCumulativeDecoratedTree input carrierFuel}

/-! ## Lists: filtering then mapping -/

/-- Mapping after a `filterMap` is the same as filtering and mapping pointwise. -/
theorem filterMap_map {α β γ : Type*} (f : α → Option β) (g : β → γ) (l : List α) :
    (l.filterMap f).map g = l.filterMap (fun a => (f a).map g) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      cases hfa : f a with
      | none => simp [hfa, ih]
      | some b => simp [hfa, ih]

/-! ## The address of a position is shorter than the actual tree height -/

/-- **Rank bound from the actual tree.**  Every position address is strictly shorter than the
height of the actual decorated tree. -/
theorem position_val_length_lt_height {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : p.val.length < height tree := by
  have main : ∀ (candidate : LocalizedCumulativeDecoratedTree input carrierFuel)
      (path : List Nat) {node : LocalizedCumulativeDecoratedTree input carrierFuel},
      subtreeAt? candidate path = some node → path.length < height candidate := by
    intro candidate path
    induction path generalizing candidate with
    | nil =>
        intro node _
        have hpos : 1 ≤ height candidate := one_le_height candidate
        simp only [List.length_nil]
        omega
    | cons slot rest ih =>
        intro node lookup
        rw [subtreeAt?_cons_eq_some_iff] at lookup
        obtain ⟨child, childLookup, restLookup⟩ := lookup
        have childMem : child ∈ candidate.children := List.mem_of_getElem? childLookup
        have hchild : height child ≤ heightList candidate.children :=
          height_le_heightList candidate.children childMem
        have hrest : rest.length < height child := ih child restLookup
        have hcandidate : height candidate = 1 + heightList candidate.children := by
          cases candidate with
          | mk source atomicNumber rule1bDistance isotopeMass label children =>
              rw [table_height_mk]
        simp only [List.length_cons]
        omega
  exact main tree p.val (positionNode_spec p)

/-! ## The actual real children of a real position -/

/-- The optional actual real child of a real position in one actual sibling slot.  The bound is
the actual number of children of the node at the position, and the slot is retained exactly when
the resulting position is real. -/
def realChildAt {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) (slot : Nat) : Option (RealPosition tree) :=
  if h : slot < (positionNode p.1).children.length then
    if real : (positionNode (positionChild p.1 slot h)).source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom then
      some ⟨positionChild p.1 slot h, real⟩
    else none
  else none

/-- The actual immediate real children of a real position, in increasing actual sibling-slot
(address) order. -/
def realChildList {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) : List (RealPosition tree) :=
  (List.range (positionNode p.1).children.length).filterMap (fun slot => realChildAt p slot)

/-- A successful `realChildAt` lookup returns a position whose address is the parent address with
the slot appended. -/
theorem realChildAt_some_val {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {p : RealPosition tree} {slot : Nat} {q : RealPosition tree}
    (h : realChildAt p slot = some q) :
    q.1.val = p.1.val ++ [slot] := by
  classical
  unfold realChildAt at h
  by_cases hbound : slot < (positionNode p.1).children.length
  · rw [dif_pos hbound] at h
    by_cases hreal : (positionNode (positionChild p.1 slot hbound)).source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom
    · rw [dif_pos hreal] at h
      have hq : (⟨positionChild p.1 slot hbound, hreal⟩ : RealPosition tree) = q :=
        Option.some.inj h
      rw [← hq]
      rfl
    · rw [dif_neg hreal] at h
      cases h
  · rw [dif_neg hbound] at h
    cases h

/-- **Membership in the canonical child list.**  A real position is a listed child of `p` exactly
when its address is `p`'s address with one actual sibling slot appended. -/
theorem mem_realChildList_iff {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p q : RealPosition tree) :
    q ∈ realChildList p ↔
      ∃ slot : Nat, slot < (positionNode p.1).children.length ∧
        q.1.val = p.1.val ++ [slot] := by
  classical
  unfold realChildList
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨slot, hslot, hsome⟩
    rw [List.mem_range] at hslot
    exact ⟨slot, hslot, realChildAt_some_val hsome⟩
  · rintro ⟨slot, hbound, hval⟩
    refine ⟨slot, List.mem_range.mpr hbound, ?_⟩
    unfold realChildAt
    rw [dif_pos hbound]
    have hpos : positionChild p.1 slot hbound = q.1 := by
      apply position_ext
      show (positionChild p.1 slot hbound).val = q.1.val
      rw [hval]
      rfl
    have hreal : (positionNode (positionChild p.1 slot hbound)).source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom := by
      rw [hpos]
      exact q.2
    rw [dif_pos hreal]
    congr 1
    exact Subtype.ext hpos

/-- **The canonical child list is exactly the actual real-child relation.** -/
theorem realChildList_iff_realPositionChild
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p q : RealPosition tree) :
    q ∈ realChildList p ↔ RealPositionChild p q := by
  rw [mem_realChildList_iff]
  constructor
  · rintro ⟨slot, _, hval⟩
    exact ⟨slot, hval⟩
  · rintro ⟨slot, hval⟩
    have hlookup : (positionNode p.1).children[slot]? = some (positionNode q.1) := by
      have h := subtreeAt?_append_singleton p.1.val tree slot
      rw [positionNode_spec p.1] at h
      have h' : subtreeAt? tree (p.1.val ++ [slot]) =
          (positionNode p.1).children[slot]? := by
        rw [h]
        rfl
      rw [← hval, positionNode_spec q.1] at h'
      exact h'.symm
    obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hlookup
    exact ⟨slot, hbound, hval⟩

/-- The canonical child list is duplicate-free.  Distinct sibling slots give distinct addresses,
and no duplicate-freeness of the actual child list is needed. -/
theorem realChildList_nodup {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) : (realChildList p).Nodup := by
  unfold realChildList
  refine List.Nodup.filterMap ?_ List.nodup_range
  intro a a' b hb hb'
  have h1 : b.1.val = p.1.val ++ [a] := realChildAt_some_val (Option.mem_def.mp hb)
  have h2 : b.1.val = p.1.val ++ [a'] := realChildAt_some_val (Option.mem_def.mp hb')
  have hEq : p.1.val ++ [a] = p.1.val ++ [a'] := by rw [← h1, h2]
  have hslots : [a] = [a'] := List.append_cancel_left hEq
  simpa using hslots

/-! ## The actual parent map with an explicit root case -/

/-- The actual `realPositionParent`, with the root case made explicit as `none`. -/
def realPositionParentOption
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree) : Option (RealPosition tree) :=
  if h : p.1.val = [] then none else some (realPositionParent realizes p h)

/-- The parent option is `none` at a root address. -/
theorem realPositionParentOption_eq_none
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree) (h : p.1.val = []) :
    realPositionParentOption realizes p = none := by
  unfold realPositionParentOption
  exact dif_pos h

/-- The parent option is the actual real parent away from the root address. -/
theorem realPositionParentOption_of_ne
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree) (h : p.1.val ≠ []) :
    realPositionParentOption realizes p = some (realPositionParent realizes p h) := by
  unfold realPositionParentOption
  exact dif_neg h

/-- The actual parent position drops the last slot of the address. -/
theorem realPositionParent_apply_val
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree) (ne : p.1.val ≠ []) :
    (realPositionParent realizes p ne).1.val = p.1.val.dropLast :=
  positionParent_val p.1 ne

/-- **The actual child relation is exactly the parent option.** -/
theorem realPositionChild_iff_parentOption
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p q : RealPosition tree) :
    RealPositionChild p q ↔ realPositionParentOption realizes q = some p := by
  constructor
  · rintro ⟨slot, hval⟩
    have hne : q.1.val ≠ [] := by rw [hval]; simp
    rw [realPositionParentOption_of_ne realizes q hne]
    congr 1
    apply Subtype.ext
    apply position_ext
    show (positionParent q.1 hne).val = p.1.val
    rw [positionParent_val, hval]
    simp
  · intro hparent
    by_cases hnil : q.1.val = []
    · rw [realPositionParentOption_eq_none realizes q hnil] at hparent
      cases hparent
    · rw [realPositionParentOption_of_ne realizes q hnil] at hparent
      have hpq : realPositionParent realizes q hnil = p := Option.some.inj hparent
      refine ⟨q.1.val.getLast hnil, ?_⟩
      have hlast := position_eq_parent_append_last q.1 hnil
      have hpval : p.1 = positionParent q.1 hnil := by
        have h := congrArg Subtype.val hpq
        exact h.symm
      exact hlast.trans (by rw [← hpval])

/-! ## The canonical actual rooted branch -/

/-- **The canonical rooted branch on the actual real positions.**  Root, parent, child list, rank
and rank bound are all read off the actual realized tree. -/
def canonicalRealPositionRootedBranch
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    RootedBranch (RealPosition tree) :=
  RootedBranch.mk
    ⟨rootPosition tree, startReal⟩
    (realPositionParentOption realizes)
    realChildList
    (fun p => p.1.val.length)
    (height tree)
    (by
      show realPositionParentOption realizes ⟨rootPosition tree, startReal⟩ = none
      exact realPositionParentOption_eq_none realizes _ rfl)
    (by
      intro x hx
      by_cases hnil : x.1.val = []
      · refine absurd ?_ hx
        apply Subtype.ext
        apply position_ext
        show x.1.val = (rootPosition tree).val
        rw [hnil]
        rfl
      · exact ⟨realPositionParent realizes x hnil,
          realPositionParentOption_of_ne realizes x hnil⟩)
    (fun x c => (realChildList_iff_realPositionChild x c).trans
      (realPositionChild_iff_parentOption realizes x c))
    (fun p => realChildList_nodup p)
    (by
      intro x p hp
      by_cases hnil : x.1.val = []
      · rw [realPositionParentOption_eq_none realizes x hnil] at hp
        cases hp
      · rw [realPositionParentOption_of_ne realizes x hnil] at hp
        have hpq : realPositionParent realizes x hnil = p := Option.some.inj hp
        have hval : x.1.val = p.1.val ++ [x.1.val.getLast hnil] := by
          have hlast := position_eq_parent_append_last x.1 hnil
          have hpval : p.1 = positionParent x.1 hnil := by
            have h := congrArg Subtype.val hpq
            exact h.symm
          exact hlast.trans (by rw [← hpval])
        show x.1.val.length = p.1.val.length + 1
        rw [hval]
        simp)
    (fun p => Nat.le_of_lt (position_val_length_lt_height p.1))

/-- **The constructed alignment.**  Root, parent and child list of the canonical branch are, by
construction, the actual root, the actual real parent and the actual real child relation. -/
def canonicalRealPositionBranchAlignment
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    RealPositionBranchAlignment realizes
      (canonicalRealPositionRootedBranch realizes startReal) startReal where
  root_eq := rfl
  parent_eq := fun p ne => realPositionParentOption_of_ne realizes p ne
  children_iff := fun p q => realChildList_iff_realPositionChild p q





noncomputable def canonicalPhysicalBranchTree
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom) :
    PhysicalBranchTree input.moleculeGraph
      (canonicalRealPositionRootedBranch realizes startReal) :=
  physicalBranchTreeOfRealPosition acyclic enough realizes previous previousEq sameRoot valid
    startReal previousReal oObserved pObserved incomingEdge
    (canonicalRealPositionRootedBranch realizes startReal)
    (canonicalRealPositionBranchAlignment realizes startReal)





theorem canonical_bond_orders_determined
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (S : input.Atom → ℕ)
    (hS : ∀ p : RealPosition tree, S (realPositionAtom p) =
      ∑ u ∈ input.moleculeGraph.neighborFinset (realPositionAtom p),
        (input.moleculeGraph.bond (realPositionAtom p) u - 1))
    (w : RealPosition tree → ℕ)
    (hw : ∀ p : RealPosition tree, S (realPositionAtom p) =
      childTotal (canonicalRealPositionRootedBranch realizes startReal).childList w p) :
    w = incomingExcess input.moleculeGraph
      (canonicalRealPositionRootedBranch realizes startReal) realPositionAtom pAtom :=
  bond_orders_determined_by_excess_sums input.moleculeGraph
    (canonicalRealPositionRootedBranch realizes startReal)
    (canonicalPhysicalBranchTree acyclic enough realizes previous previousEq sameRoot valid
      startReal previousReal oObserved pObserved incomingEdge)
    acyclic S hS w hw











section ActualRealPositionBranchIso

variable {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
  Option LocalizedAuxiliaryLabel}
variable {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
variable (acyclic : input.moleculeGraph.Acyclic)
variable (leftRealizes : LocalizedCumulativeTreeRealizes input readLeft left)
variable (rightRealizes : LocalizedCumulativeTreeRealizes input readRight right)
variable (leftRootReal : left.source.occurrence.1.node.provenance =
  OfficialCIPNodeProvenance.realAtom)
variable (rightRootReal : right.source.occurrence.1.node.provenance =
  OfficialCIPNodeProvenance.realAtom)
variable (hshape : shape left = shape right)



noncomputable def realPositionShapeEquiv : RealPosition left ≃ RealPosition right :=
  (shapePositionEquiv hshape).subtypeEquiv (fun p =>
    provenance_real_iff_at_same_address_of_shape_eq acyclic left right leftRealizes
      rightRealizes leftRootReal rightRootReal hshape (positionNode_spec p)
      (positionNode_spec (shapePositionEquiv hshape p)))

/-- The transported position keeps the raw address. -/
theorem realPositionShapeEquiv_apply_val (p : RealPosition left) :
    ((realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal rightRootReal
      hshape p).1).val = p.1.val := rfl

/-- The transported position has exactly as many actual children. -/
theorem realPositionShapeEquiv_children_length (p : RealPosition left) :
    (positionNode ((realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal
      rightRootReal hshape p).1)).children.length =
      (positionNode p.1).children.length :=
  shapePositionEquiv_positionNode_children_length_eq hshape p.1



theorem realPositionShapeEquiv_real_child_iff (p : RealPosition left) (slot : Nat)
    (hl : slot < (positionNode p.1).children.length)
    (hr : slot < (positionNode ((realPositionShapeEquiv acyclic leftRealizes rightRealizes
      leftRootReal rightRootReal hshape p).1)).children.length) :
    ((positionNode (positionChild p.1 slot hl)).source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom) ↔
      ((positionNode (positionChild ((realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape p).1) slot hr)).source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom) := by
  have hval : ((realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal
      rightRootReal hshape p).1).val = p.1.val :=
    realPositionShapeEquiv_apply_val acyclic leftRealizes rightRealizes leftRootReal
      rightRootReal hshape p
  have hleft : subtreeAt? left (p.1.val ++ [slot]) =
      some (positionNode (positionChild p.1 slot hl)) := by
    simpa only [positionChild_val] using positionNode_spec (positionChild p.1 slot hl)
  have hright : subtreeAt? right (p.1.val ++ [slot]) =
      some (positionNode (positionChild ((realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape p).1) slot hr)) := by
    have hspec := positionNode_spec (positionChild ((realPositionShapeEquiv acyclic
      leftRealizes rightRealizes leftRootReal rightRootReal hshape p).1) slot hr)
    rw [positionChild_val, hval] at hspec
    exact hspec
  exact provenance_real_iff_at_same_address_of_shape_eq acyclic left right leftRealizes
    rightRealizes leftRootReal rightRootReal hshape hleft hright

/-- **The child list transports exactly, option by option.**  At every actual sibling slot the
transported real child is the real child at the same slot. -/
theorem realChildAt_map_eq (p : RealPosition left) (slot : Nat) :
    (realChildAt p slot).map (fun q => realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape q) =
      realChildAt (realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal
        rightRootReal hshape p) slot := by
  classical
  unfold realChildAt
  by_cases hboundL : slot < (positionNode p.1).children.length
  · have hboundR : slot < (positionNode ((realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape p).1)).children.length := by
      rw [realPositionShapeEquiv_children_length acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape p]
      exact hboundL
    rw [dif_pos hboundL, dif_pos hboundR]
    by_cases hrealL : (positionNode (positionChild p.1 slot hboundL)).source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom
    · have hrealR : (positionNode (positionChild ((realPositionShapeEquiv acyclic
          leftRealizes rightRealizes leftRootReal rightRootReal hshape p).1) slot
          hboundR)).source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom :=
        (realPositionShapeEquiv_real_child_iff acyclic leftRealizes rightRealizes
          leftRootReal rightRootReal hshape p slot hboundL hboundR).mp hrealL
      rw [dif_pos hrealL, dif_pos hrealR]
      rfl
    · have hrealR : ¬ ((positionNode (positionChild ((realPositionShapeEquiv acyclic
          leftRealizes rightRealizes leftRootReal rightRootReal hshape p).1) slot
          hboundR)).source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom) := fun h =>
        hrealL ((realPositionShapeEquiv_real_child_iff acyclic leftRealizes rightRealizes
          leftRootReal rightRootReal hshape p slot hboundL hboundR).mpr h)
      rw [dif_neg hrealL, dif_neg hrealR]
      rfl
  · have hboundR : ¬ slot < (positionNode ((realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape p).1)).children.length := by
      rw [realPositionShapeEquiv_children_length acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape p]
      exact hboundL
    rw [dif_neg hboundL, dif_neg hboundR]
    rfl

/-- **The exact ordered child list transports.**  The whole `filterMap` list is mapped, in order,
onto the child list of the transported position. -/
theorem realPositionShapeEquiv_map_childList (p : RealPosition left) :
    (realChildList p).map (fun q => realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape q) =
      realChildList (realPositionShapeEquiv acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape p) := by
  unfold realChildList
  rw [filterMap_map]
  have hlen : (positionNode ((realPositionShapeEquiv acyclic leftRealizes rightRealizes
      leftRootReal rightRootReal hshape p).1)).children.length =
      (positionNode p.1).children.length :=
    realPositionShapeEquiv_children_length acyclic leftRealizes rightRealizes
      leftRootReal rightRootReal hshape p
  rw [← hlen]
  exact List.filterMap_congr (fun slot _ =>
    realChildAt_map_eq acyclic leftRealizes rightRealizes leftRootReal rightRootReal
      hshape p slot)

/-- The root transports to the root. -/
theorem realPositionShapeEquiv_map_root :
    realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal rightRootReal
        hshape ⟨rootPosition left, leftRootReal⟩ =
      ⟨rootPosition right, rightRootReal⟩ := by
  apply Subtype.ext
  apply position_ext
  show ((realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal
    rightRootReal hshape ⟨rootPosition left, leftRootReal⟩).1).val =
      (rootPosition right).val
  rw [realPositionShapeEquiv_apply_val acyclic leftRealizes rightRealizes leftRootReal
    rightRootReal hshape ⟨rootPosition left, leftRootReal⟩]
  rfl

/-- The actual real parent transports: the parent option commutes with the address-preserving
equivalence. -/
theorem realPositionShapeEquiv_map_parent (x : RealPosition left) :
    (realPositionParentOption leftRealizes x).map (fun q =>
        realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal
          rightRootReal hshape q) =
      realPositionParentOption rightRealizes (realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape x) := by
  classical
  by_cases hnil : x.1.val = []
  · have hnilR : ((realPositionShapeEquiv acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape x).1).val = [] := by
      rw [realPositionShapeEquiv_apply_val acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape x, hnil]
    rw [realPositionParentOption_eq_none leftRealizes x hnil,
      realPositionParentOption_eq_none rightRealizes _ hnilR]
    rfl
  · have hnilR : ((realPositionShapeEquiv acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape x).1).val ≠ [] := by
      rw [realPositionShapeEquiv_apply_val acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape x]
      exact hnil
    rw [realPositionParentOption_of_ne leftRealizes x hnil,
      realPositionParentOption_of_ne rightRealizes _ hnilR]
    show some (realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal
        rightRootReal hshape (realPositionParent leftRealizes x hnil)) =
      some (realPositionParent rightRealizes (realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape x) hnilR)
    rfl

/-- **The actual same-shape rooted-branch isomorphism.**  Root, parent map and the exact ordered
child list of the two canonical actual branches correspond under the address-preserving
equivalence. -/
noncomputable def actualRealPositionBranchIso :
    RootedBranchIso (canonicalRealPositionRootedBranch leftRealizes leftRootReal)
      (canonicalRealPositionRootedBranch rightRealizes rightRootReal) :=
  RootedBranchIso.mk
    (realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal rightRootReal
      hshape)
    (realPositionShapeEquiv_map_root acyclic leftRealizes rightRealizes leftRootReal
      rightRootReal hshape)
    (realPositionShapeEquiv_map_parent acyclic leftRealizes rightRealizes leftRootReal
      rightRootReal hshape)
    (realPositionShapeEquiv_map_childList acyclic leftRealizes rightRealizes leftRootReal
      rightRootReal hshape)

/-- The ordered child list of the left canonical branch maps, in order, onto the child list of the
image vertex in the right canonical branch.  This is the `map_children` field of the constructed
`RootedBranchIso`, spelled out. -/
theorem actualRealPositionBranchIso_childList (x : RealPosition left) :
    ((canonicalRealPositionRootedBranch leftRealizes leftRootReal).childList x).map
        (actualRealPositionBranchIso acyclic leftRealizes rightRealizes leftRootReal
          rightRootReal hshape).toEquiv =
      (canonicalRealPositionRootedBranch rightRealizes rightRootReal).childList
        ((actualRealPositionBranchIso acyclic leftRealizes rightRealizes leftRootReal
          rightRootReal hshape).toEquiv x) :=
  (actualRealPositionBranchIso acyclic leftRealizes rightRealizes leftRootReal
    rightRootReal hshape).map_children x

/-- **The actual real-child relation is preserved by the iso.** -/
theorem realPositionShapeEquiv_realPositionChild_iff (p q : RealPosition left) :
    RealPositionChild p q ↔
      RealPositionChild (realPositionShapeEquiv acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape p) (realPositionShapeEquiv acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape q) := by
  rw [← realChildList_iff_realPositionChild p q,
    ← realChildList_iff_realPositionChild (realPositionShapeEquiv acyclic leftRealizes
      rightRealizes leftRootReal rightRootReal hshape p) (realPositionShapeEquiv acyclic
      leftRealizes rightRealizes leftRootReal rightRootReal hshape q)]
  constructor
  · intro hmem
    have hmap : realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal
        rightRootReal hshape q ∈ (realChildList p).map (fun q => realPositionShapeEquiv
          acyclic leftRealizes rightRealizes leftRootReal rightRootReal hshape q) :=
      List.mem_map.mpr ⟨q, hmem, rfl⟩
    rwa [realPositionShapeEquiv_map_childList acyclic leftRealizes rightRealizes
      leftRootReal rightRootReal hshape p] at hmap
  · intro hmem
    have hmap : realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal
        rightRootReal hshape q ∈ (realChildList p).map (fun q => realPositionShapeEquiv
          acyclic leftRealizes rightRealizes leftRootReal rightRootReal hshape q) := by
      rwa [realPositionShapeEquiv_map_childList acyclic leftRealizes rightRealizes
        leftRootReal rightRootReal hshape p]
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmap
    have haz : a = q := (realPositionShapeEquiv acyclic leftRealizes rightRealizes
      leftRootReal rightRootReal hshape).injective heq
    rwa [haz] at ha




theorem actualRealPositionBranchIso_adjacent_iff
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (leftPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (leftPreviousEq : left.source.previous? = some leftPrevious)
    (leftSameRoot : left.source.occurrence.1.root = leftPrevious.1.root)
    (leftValid : input.LocalizedRerootCursorValid left.source)
    (leftPreviousReal : leftPrevious.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (rightPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (rightPreviousEq : right.source.previous? = some rightPrevious)
    (rightSameRoot : right.source.occurrence.1.root = rightPrevious.1.root)
    (rightValid : input.LocalizedRerootCursorValid right.source)
    (rightPreviousReal : rightPrevious.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom oAtomR pAtomR : input.Atom}
    (oObserved : left.source.occurrence.1.node.current? = some oAtom)
    (pObserved : leftPrevious.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (oObservedR : right.source.occurrence.1.node.current? = some oAtomR)
    (pObservedR : rightPrevious.1.node.current? = some pAtomR)
    (incomingEdgeR : input.moleculeGraph.Adj pAtomR oAtomR)
    (p q : RealPosition left) :
    input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom q) ↔
      input.moleculeGraph.Adj
        (realPositionAtom (realPositionShapeEquiv acyclic leftRealizes rightRealizes
          leftRootReal rightRootReal hshape p))
        (realPositionAtom (realPositionShapeEquiv acyclic leftRealizes rightRealizes
          leftRootReal rightRootReal hshape q)) := by
  rw [realPosition_adjacent_iff_realPositionChild acyclic enough leftRealizes
    leftPrevious leftPreviousEq leftSameRoot leftValid leftRootReal leftPreviousReal
    oObserved pObserved incomingEdge p q]
  rw [realPosition_adjacent_iff_realPositionChild acyclic enough rightRealizes
    rightPrevious rightPreviousEq rightSameRoot rightValid rightRootReal rightPreviousReal
    oObservedR pObservedR incomingEdgeR]
  constructor
  · rintro (h | h)
    · exact Or.inl ((realPositionShapeEquiv_realPositionChild_iff acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape p q).mp h)
    · exact Or.inr ((realPositionShapeEquiv_realPositionChild_iff acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape q p).mp h)
  · rintro (h | h)
    · exact Or.inl ((realPositionShapeEquiv_realPositionChild_iff acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape p q).mpr h)
    · exact Or.inr ((realPositionShapeEquiv_realPositionChild_iff acyclic leftRealizes
        rightRealizes leftRootReal rightRootReal hshape q p).mpr h)



theorem actualRealPositionBranchIso_weights_transport
    (S₁ : RealPosition left → ℕ) (S₂ : RealPosition right → ℕ)
    (w₁ : RealPosition left → ℕ) (w₂ : RealPosition right → ℕ)
    (hsum : ∀ x, S₁ x = S₂ ((actualRealPositionBranchIso acyclic leftRealizes rightRealizes
      leftRootReal rightRootReal hshape).toEquiv x))
    (hw₁ : ∀ x, S₁ x = childTotal
      (canonicalRealPositionRootedBranch leftRealizes leftRootReal).childList w₁ x)
    (hw₂ : ∀ y, S₂ y = childTotal
      (canonicalRealPositionRootedBranch rightRealizes rightRootReal).childList w₂ y) :
    ∀ x, w₁ x = w₂ ((actualRealPositionBranchIso acyclic leftRealizes rightRealizes
      leftRootReal rightRootReal hshape).toEquiv x) :=
  RootedBranchIso.weights_transport (actualRealPositionBranchIso acyclic leftRealizes
    rightRealizes leftRootReal rightRootReal hshape) S₁ S₂ w₁ w₂ hsum hw₁ hw₂

end ActualRealPositionBranchIso

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.filterMap_map
assert_kernel_only TetraStereo.OneCenter.position_val_length_lt_height
assert_kernel_only TetraStereo.OneCenter.realChildAt
assert_kernel_only TetraStereo.OneCenter.realChildList
assert_kernel_only TetraStereo.OneCenter.realChildAt_some_val
assert_kernel_only TetraStereo.OneCenter.mem_realChildList_iff
assert_kernel_only TetraStereo.OneCenter.realChildList_iff_realPositionChild
assert_kernel_only TetraStereo.OneCenter.realChildList_nodup
assert_kernel_only TetraStereo.OneCenter.realPositionParentOption
assert_kernel_only TetraStereo.OneCenter.realPositionParentOption_eq_none
assert_kernel_only TetraStereo.OneCenter.realPositionParentOption_of_ne
assert_kernel_only TetraStereo.OneCenter.realPositionParent_apply_val
assert_kernel_only TetraStereo.OneCenter.realPositionChild_iff_parentOption
assert_kernel_only TetraStereo.OneCenter.canonicalRealPositionRootedBranch
assert_kernel_only TetraStereo.OneCenter.canonicalRealPositionBranchAlignment
assert_kernel_only TetraStereo.OneCenter.canonicalPhysicalBranchTree
assert_kernel_only TetraStereo.OneCenter.canonical_bond_orders_determined
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv_apply_val
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv_children_length
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv_real_child_iff
assert_kernel_only TetraStereo.OneCenter.realChildAt_map_eq
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv_map_childList
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv_map_root
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv_map_parent
assert_kernel_only TetraStereo.OneCenter.actualRealPositionBranchIso
assert_kernel_only TetraStereo.OneCenter.actualRealPositionBranchIso_childList
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv_realPositionChild_iff
assert_kernel_only TetraStereo.OneCenter.actualRealPositionBranchIso_adjacent_iff
assert_kernel_only TetraStereo.OneCenter.actualRealPositionBranchIso_weights_transport
