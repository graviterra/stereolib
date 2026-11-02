import TetraStereo.OneCenter.LocalizedContextCompleteReadingOrder
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# Stage-to-stage isomorphism of one retained context cursor

Rules 4b, 4c and the no-reference stage sort the same actual `localizedRerootChildren?` frame as
Rule 4a.  Two traces may also use different label readers.  The readers can sort siblings
differently, but both frames are `localizedRerootChildren?` of the shared source cursor, so the
child sources remain permutations of one reader-independent list.

`ruleMajorTreeGraph` is `(toOfficialSourceTree tree).toDeclarativeDigraph`.
`toOfficialSourceTree` drops the reader's auxiliary stereo label and also the stored atomic
number, Rule-1b distance and isotope.  It keeps the official occurrence node.  A digraph label
is that node's `toDeclarativeLabel`: `current?` and provenance.  Hierarchy addresses permute
with sibling order; the matched address still carries the stored occurrence's current atom and
provenance, so distinct duplicates stay distinct when their current atoms coincide.  The
official node's history is not a digraph-label field.

The resulting `RootedDigraph.Iso` transports that erased topology and those occurrence labels.
It does not transport cumulative keys, and it does not transfer an arbitrary stereochemical
reading from one reader to the other.  `descriptorMap` remains a fixed table and is still read
independently at the stored source occurrences.  A constant-`none` reader can supply the finite
erased arm; the generated reader's keys are a separate observation.

The isomorphism is read off two `LocalizedRuleMajorSortTrace`s at the same source cursor and
the same fuel, at arbitrary stages.  It does not assume the readers agree, a desired label, a
correct outcome, `Acyclic`, a fresh-root `FaithfulExactExpansion`, or an all-real premise.
Retained branch faithfulness for every context is a separate result.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open Classical

noncomputable section

/-! ## Index equivalence induced by a list permutation -/

private def finCastEquiv {n m : Nat} (h : n = m) : Fin n ≃ Fin m where
  toFun i := i.cast h
  invFun i := i.cast h.symm
  left_inv i := by
    ext
    simp [Fin.val_cast]
  right_inv i := by
    ext
    simp [Fin.val_cast]

@[simp] private theorem finCastEquiv_apply {n m : Nat} (h : n = m) (i : Fin n) :
    finCastEquiv h i = i.cast h := rfl

private def finConsEquiv {n : Nat} (e : Fin n ≃ Fin n) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.cases 0 fun j => (e j).succ
  invFun := Fin.cases 0 fun j => (e.symm j).succ
  left_inv := by
    intro i
    induction i using Fin.induction with
    | zero => simp [Fin.cases_zero]
    | succ i _ => simp [Fin.cases_zero, Fin.cases_succ, Equiv.left_inv]
  right_inv := by
    intro i
    induction i using Fin.induction with
    | zero => simp [Fin.cases_zero]
    | succ i _ => simp [Fin.cases_zero, Fin.cases_succ, Equiv.right_inv]

@[simp] private theorem finConsEquiv_zero {n : Nat} (e : Fin n ≃ Fin n) :
    finConsEquiv e 0 = 0 := by
  simp [finConsEquiv, Fin.cases_zero]

@[simp] private theorem finConsEquiv_succ {n : Nat} (e : Fin n ≃ Fin n) (j : Fin n) :
    finConsEquiv e j.succ = (e j).succ := by
  simp [finConsEquiv, Fin.cases_succ]

/-- A list permutation is an index equivalence that preserves elements, including duplicates. -/
@[irreducible] private def consIndex {n m : Nat} (h : n = m) (e : Fin n ≃ Fin m) :
    Fin (n + 1) ≃ Fin (m + 1) :=
  finConsEquiv (e.trans (finCastEquiv h.symm)) |>.trans
    (finCastEquiv (congrArg Nat.succ h))

private theorem consIndex_zero {n m : Nat} (h : n = m) (e : Fin n ≃ Fin m) :
    consIndex h e 0 = 0 := by
  apply Fin.ext
  unfold consIndex
  simp only [Equiv.trans_apply, finConsEquiv_zero, finCastEquiv_apply, Fin.val_cast,
    Fin.val_zero]

private theorem consIndex_succ {n m : Nat} (h : n = m) (e : Fin n ≃ Fin m) (j : Fin n) :
    consIndex h e j.succ = (e j).succ := by
  apply Fin.ext
  unfold consIndex
  simp only [Equiv.trans_apply, finConsEquiv_succ, finCastEquiv_apply, Fin.val_succ,
    Fin.val_cast]

private theorem swapIndex_zero (k : Nat) :
    (Equiv.swap (0 : Fin (k + 2)) (1 : Fin (k + 2))) 0 = 1 :=
  Equiv.swap_apply_left _ _

private theorem swapIndex_one (k : Nat) :
    (Equiv.swap (0 : Fin (k + 2)) (1 : Fin (k + 2))) 1 = 0 :=
  Equiv.swap_apply_right _ _

private theorem swapIndex_succ_succ (k : Nat) (i : Fin k) :
    (Equiv.swap (0 : Fin (k + 2)) (1 : Fin (k + 2))) i.succ.succ = i.succ.succ := by
  refine Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ?_
  intro eq
  have valEq := congrArg Fin.val eq
  rw [Fin.val_succ, Fin.val_succ] at valEq
  have oneVal : ((1 : Fin (k + 2)) : Nat) = 1 := rfl
  rw [oneVal] at valEq
  omega

private theorem indexEquiv_cons {α : Type _} {l₁ l₂ : List α} (x : α)
    (hlen : l₁.length = l₂.length) (e : Fin l₁.length ≃ Fin l₂.length)
    (he : ∀ i : Fin l₁.length, l₁.get i = l₂.get (e i))
    (i : Fin (x :: l₁).length) :
    (x :: l₁).get i = (x :: l₂).get (consIndex hlen e i) := by
  refine Fin.cases ?_ ?_ i
  · apply Eq.trans (b := x)
    · exact List.get_cons_zero
    · apply Eq.trans (b := (x :: l₂).get 0)
      · exact List.get_cons_zero.symm
      · exact congrArg ((x :: l₂).get) (consIndex_zero hlen e).symm
  · intro j
    apply Eq.trans (b := (x :: l₂).get (e j).succ)
    · exact List.get_cons_succ'.trans ((he j).trans (List.get_cons_succ' (i := e j)).symm)
    · exact congrArg ((x :: l₂).get) (consIndex_succ hlen e j).symm

private theorem indexEquiv_of_perm {α : Type _} :
    ∀ {left right : List α}, left.Perm right →
      ∃ e : Fin left.length ≃ Fin right.length,
        ∀ i : Fin left.length, left.get i = right.get (e i) := by
  intro left right h
  induction h with
  | nil =>
      refine ⟨Equiv.refl (Fin 0), ?_⟩
      intro i
      exact Fin.elim0 i
  | cons x perm ih =>
      obtain ⟨e, he⟩ := ih
      have hlen := perm.length_eq
      exact ⟨consIndex hlen e, indexEquiv_cons x hlen e he⟩
  | swap x y l =>
      refine ⟨Equiv.swap (0 : Fin (l.length + 2)) (1 : Fin (l.length + 2)), ?_⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · apply Eq.trans (b := (x :: y :: l).get (1 : Fin (l.length + 2)))
        · rw [List.get_cons_zero]
          rw [show (1 : Fin (l.length + 2)) = (0 : Fin (l.length + 1)).succ from Fin.ext rfl]
          rw [List.get_cons_succ', List.get_cons_zero]
        · exact congrArg ((x :: y :: l).get) (swapIndex_zero l.length).symm
      · intro i
        refine Fin.cases ?_ ?_ i
        · apply Eq.trans (b := (x :: y :: l).get (0 : Fin (l.length + 2)))
          · rw [List.get_cons_succ', List.get_cons_zero, List.get_cons_zero]
          · exact congrArg ((x :: y :: l).get)
              ((congrArg (Equiv.swap (0 : Fin (l.length + 2)) (1 : Fin (l.length + 2)))
                  (show (0 : Fin (l.length + 1)).succ = (1 : Fin (l.length + 2)) from
                    Fin.ext rfl)).trans
                (swapIndex_one l.length)).symm
        · intro i
          apply Eq.trans (b := (x :: y :: l).get i.succ.succ)
          · rw [List.get_cons_succ', List.get_cons_succ', List.get_cons_succ',
              List.get_cons_succ']
          · exact congrArg ((x :: y :: l).get) (swapIndex_succ_succ l.length i).symm
  | trans perm12 perm23 ih12 ih23 =>
      obtain ⟨e12, he12⟩ := ih12
      obtain ⟨e23, he23⟩ := ih23
      refine ⟨e12.trans e23, ?_⟩
      intro i
      rw [Equiv.trans_apply, he12, he23]

/-! ## Hierarchy addresses are a root plus one child address per sibling slot -/

private theorem cons_mem_hierarchyAddresses {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (i : Fin children.length)
    {rest : List Nat}
    (restMem : rest ∈ (children.get i).hierarchyAddresses) :
    i.val :: rest ∈ (OfficialCIPSourceTree.node source children).hierarchyAddresses := by
  simp only [OfficialCIPSourceTree.hierarchyAddresses, List.mem_cons, List.mem_flatMap]
    at restMem ⊢
  have indexed : (children.get i, i.val) ∈ children.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    rw [List.getElem?_eq_getElem i.isLt]
    simp [List.get_eq_getElem]
  rcases restMem with rfl | ⟨sourceEntry, sourcePresent, prefixMem⟩
  · have rootPresent :
        ([], (children.get i).source) ∈ (children.get i).occurrences := by
      cases childTree : children.get i with
      | node src subs =>
          simp [OfficialCIPSourceTree.occurrences, OfficialCIPSourceTree.source]
    have forest :
        ([i.val], (children.get i).source) ∈
          OfficialCIPSourceTree.forestOccurrences children 0 := by
      rw [OfficialCIPSourceTree.mem_forestOccurrences_iff_zipIdx]
      exact ⟨(children.get i, i.val), indexed,
        ([], (children.get i).source), rootPresent, rfl⟩
    refine Or.inr ⟨([i.val], (children.get i).source), ?_, ?_⟩
    · simp only [OfficialCIPSourceTree.occurrences, List.mem_cons]
      exact Or.inr forest
    · exact (List.mem_inits [i.val] [i.val]).mpr ⟨[], rfl⟩
  · rw [List.mem_inits] at prefixMem
    rcases prefixMem with ⟨suffix, restEq⟩
    have forest :
        (i.val :: sourceEntry.1, sourceEntry.2) ∈
          OfficialCIPSourceTree.forestOccurrences children 0 := by
      rw [OfficialCIPSourceTree.mem_forestOccurrences_iff_zipIdx]
      exact ⟨(children.get i, i.val), indexed, sourceEntry, sourcePresent, rfl⟩
    refine Or.inr ⟨(i.val :: sourceEntry.1, sourceEntry.2), ?_, ?_⟩
    · simp only [OfficialCIPSourceTree.occurrences, List.mem_cons]
      exact Or.inr forest
    · rw [List.mem_inits]
      refine ⟨suffix, ?_⟩
      simp [List.cons_append, restEq]

private theorem cons_decomposition {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    {slot : Nat} {rest : List Nat}
    (present : slot :: rest ∈ (OfficialCIPSourceTree.node source children).hierarchyAddresses) :
    ∃ bound : slot < children.length,
      rest ∈ (children.get ⟨slot, bound⟩).hierarchyAddresses := by
  simp only [OfficialCIPSourceTree.hierarchyAddresses, List.mem_cons, List.mem_flatMap]
    at present
  rcases present with impossible | ⟨entry, entryPresent, prefixMem⟩
  · cases impossible
  rw [List.mem_inits] at prefixMem
  rcases prefixMem with ⟨suffix, addressEq⟩
  simp only [OfficialCIPSourceTree.occurrences, List.mem_cons] at entryPresent
  rcases entryPresent with rootEntry | forestEntry
  · have entryAddress : entry.1 = [] := congrArg Prod.fst rootEntry
    rw [entryAddress] at addressEq
    have nilBoth := List.append_eq_nil_iff.mp addressEq
    cases nilBoth.1
  · rw [OfficialCIPSourceTree.mem_forestOccurrences_iff_zipIdx] at forestEntry
    rcases forestEntry with ⟨indexed, indexedPresent, sourceEntry, sourcePresent, entryEq⟩
    have entryAddress : entry.1 = indexed.2 :: sourceEntry.1 := congrArg Prod.fst entryEq
    rw [entryAddress] at addressEq
    simp only [List.cons_append] at addressEq
    injection addressEq with slotEq tailEq
    have slotLt : slot < children.length := by
      rw [slotEq]
      simpa using List.snd_lt_of_mem_zipIdx indexedPresent
    have childEq : indexed.1 = children.get ⟨slot, slotLt⟩ := by
      subst slotEq
      have raw := List.fst_eq_of_mem_zipIdx indexedPresent
      simp only [Nat.sub_zero] at raw
      simpa [List.get_eq_getElem] using raw
    have restPrefix : rest ∈ sourceEntry.1.inits := by
      rw [List.mem_inits]
      exact ⟨suffix, tailEq⟩
    have restMem : rest ∈ indexed.1.hierarchyAddresses := by
      simp only [OfficialCIPSourceTree.hierarchyAddresses, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨sourceEntry, sourcePresent, restPrefix⟩
    rw [childEq] at restMem
    exact ⟨slotLt, restMem⟩

private theorem declarativeLabel_root {V : Type _} [DecidableEq V]
    (tree : OfficialCIPSourceTree V)
    (present : [] ∈ tree.hierarchyAddresses) :
    tree.declarativeLabel ⟨[], present⟩ = tree.source.toDeclarativeLabel := by
  have lookup : tree.subtreeAt? [] = some tree := by
    simp [OfficialCIPSourceTree.subtreeAt?]
  simpa using tree.declarativeLabel_eq_of_subtreeAt? tree ⟨[], present⟩ lookup

private theorem declarativeLabel_cons {V : Type _} [DecidableEq V]
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (i : Fin children.length)
    {rest : List Nat}
    (restMem : rest ∈ (children.get i).hierarchyAddresses)
    (parentMem : i.val :: rest ∈
      (OfficialCIPSourceTree.node source children).hierarchyAddresses) :
    (OfficialCIPSourceTree.node source children).declarativeLabel
        ⟨i.val :: rest, parentMem⟩ =
      (children.get i).declarativeLabel ⟨rest, restMem⟩ := by
  have childLookup :
      (OfficialCIPSourceTree.node source children).subtreeAt? [i.val] =
        some (children.get i) := by
    simp [OfficialCIPSourceTree.subtreeAt?, List.getElem?_eq_getElem, List.get_eq_getElem]
  obtain ⟨sub, subLookup⟩ :=
    (children.get i).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses rest restMem
  have parentLookup :
      (OfficialCIPSourceTree.node source children).subtreeAt? (i.val :: rest) = some sub := by
    rw [show i.val :: rest = [i.val] ++ rest from rfl,
      OfficialCIPSourceTree.subtreeAt?_append, childLookup]
    simpa using subLookup
  have parentLabel :=
    (OfficialCIPSourceTree.node source children).declarativeLabel_eq_of_subtreeAt?
      sub ⟨i.val :: rest, parentMem⟩ parentLookup
  have childLabel :=
    (children.get i).declarativeLabel_eq_of_subtreeAt? sub ⟨rest, restMem⟩ subLookup
  rw [parentLabel, childLabel]

/-! ## A sibling permutation of isomorphic child digraphs is a parent isomorphism -/

private noncomputable def hierarchyToSum {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (node : (OfficialCIPSourceTree.node source children).HierarchyNode) :
    Unit ⊕ Σ i : Fin children.length, (children.get i).HierarchyNode :=
  match node with
  | ⟨[], _⟩ => Sum.inl ()
  | ⟨slot :: rest, present⟩ =>
      Sum.inr ⟨
        ⟨slot, (cons_decomposition source children present).choose⟩,
        ⟨rest, (cons_decomposition source children present).choose_spec⟩⟩

private def hierarchyOfSum {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V)) :
    (Unit ⊕ Σ i : Fin children.length, (children.get i).HierarchyNode) →
      (OfficialCIPSourceTree.node source children).HierarchyNode
  | Sum.inl () => ⟨[], (OfficialCIPSourceTree.node source children).nil_mem_hierarchyAddresses⟩
  | Sum.inr ⟨i, child⟩ =>
      ⟨i.val :: child.1, cons_mem_hierarchyAddresses source children i child.2⟩

private theorem hierarchyToSum_nil {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (present : [] ∈ (OfficialCIPSourceTree.node source children).hierarchyAddresses) :
    hierarchyToSum source children ⟨[], present⟩ = Sum.inl () := rfl

private theorem hierarchyToSum_cons {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    {slot : Nat} {rest : List Nat}
    (present : slot :: rest ∈ (OfficialCIPSourceTree.node source children).hierarchyAddresses) :
    hierarchyToSum source children ⟨slot :: rest, present⟩ =
      Sum.inr ⟨
        ⟨slot, (cons_decomposition source children present).choose⟩,
        ⟨rest, (cons_decomposition source children present).choose_spec⟩⟩ := rfl

private theorem hierarchyOfSum_inl {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V)) :
    hierarchyOfSum source children (Sum.inl ()) =
      ⟨[], (OfficialCIPSourceTree.node source children).nil_mem_hierarchyAddresses⟩ := rfl

private theorem hierarchyOfSum_inr {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (i : Fin children.length)
    (child : (children.get i).HierarchyNode) :
    hierarchyOfSum source children (Sum.inr ⟨i, child⟩) =
      ⟨i.val :: child.1, cons_mem_hierarchyAddresses source children i child.2⟩ := rfl

private theorem hierarchyOfSum_toSum {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (node : (OfficialCIPSourceTree.node source children).HierarchyNode) :
    hierarchyOfSum source children (hierarchyToSum source children node) = node := by
  rcases node with ⟨address, present⟩
  cases address with
  | nil =>
      rw [hierarchyToSum_nil, hierarchyOfSum_inl]
  | cons slot rest =>
      rw [hierarchyToSum_cons, hierarchyOfSum_inr]

private theorem hierarchyToSum_ofSum {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (packed : Unit ⊕ Σ i : Fin children.length, (children.get i).HierarchyNode) :
    hierarchyToSum source children (hierarchyOfSum source children packed) = packed := by
  cases packed with
  | inl u =>
      cases u
      rw [hierarchyOfSum_inl, hierarchyToSum_nil]
  | inr pair =>
      rcases pair with ⟨i, child⟩
      rw [hierarchyOfSum_inr, hierarchyToSum_cons]

private noncomputable def hierarchySumEquiv {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V)) :
    (OfficialCIPSourceTree.node source children).HierarchyNode ≃
      (Unit ⊕ Σ i : Fin children.length, (children.get i).HierarchyNode) where
  toFun := hierarchyToSum source children
  invFun := hierarchyOfSum source children
  left_inv := hierarchyOfSum_toSum source children
  right_inv := hierarchyToSum_ofSum source children

@[simp] private theorem hierarchySumEquiv_apply {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (node : (OfficialCIPSourceTree.node source children).HierarchyNode) :
    hierarchySumEquiv source children node = hierarchyToSum source children node := rfl

@[simp] private theorem hierarchySumEquiv_symm_apply {V : Type _}
    (source : OfficialCIPNode V)
    (children : List (OfficialCIPSourceTree V))
    (packed : Unit ⊕ Σ i : Fin children.length, (children.get i).HierarchyNode) :
    (hierarchySumEquiv source children).symm packed =
      hierarchyOfSum source children packed := rfl

private theorem sigmaCongr_apply_mk {α₁ α₂ : Type _} {β₁ : α₁ → Type _} {β₂ : α₂ → Type _}
    (f : α₁ ≃ α₂) (F : ∀ a, β₁ a ≃ β₂ (f a)) (a : α₁) (b : β₁ a) :
    Equiv.sigmaCongr f F ⟨a, b⟩ = ⟨f a, F a b⟩ := by
  simp [Equiv.sigmaCongr, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaCongrLeft_apply]

section SiblingIso

variable {V : Type _} [DecidableEq V]
variable (source : OfficialCIPNode V)
variable (leftChildren rightChildren : List (OfficialCIPSourceTree V))
variable (e : Fin leftChildren.length ≃ Fin rightChildren.length)
variable (childIso : ∀ i : Fin leftChildren.length,
  RootedDigraph.Iso (leftChildren.get i).toDeclarativeDigraph
    (rightChildren.get (e i)).toDeclarativeDigraph)

private noncomputable def siblingSigmaEquiv :
    (Σ i : Fin leftChildren.length, (leftChildren.get i).HierarchyNode) ≃
      (Σ j : Fin rightChildren.length, (rightChildren.get j).HierarchyNode) :=
  Equiv.sigmaCongr e fun i => (childIso i).toEquiv

private noncomputable def siblingSumEquiv :
    Unit ⊕ (Σ i : Fin leftChildren.length, (leftChildren.get i).HierarchyNode) ≃
      Unit ⊕ (Σ j : Fin rightChildren.length, (rightChildren.get j).HierarchyNode) :=
  Equiv.sumCongr (Equiv.refl Unit) (siblingSigmaEquiv leftChildren rightChildren e childIso)

private theorem siblingSumEquiv_inl :
    siblingSumEquiv leftChildren rightChildren e childIso (Sum.inl ()) = Sum.inl () := by
  unfold siblingSumEquiv siblingSigmaEquiv
  rw [Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]

private theorem siblingSumEquiv_inr
    (i : Fin leftChildren.length)
    (child : (leftChildren.get i).HierarchyNode) :
    siblingSumEquiv leftChildren rightChildren e childIso (Sum.inr ⟨i, child⟩) =
      Sum.inr ⟨e i, (childIso i).toEquiv child⟩ := by
  unfold siblingSumEquiv siblingSigmaEquiv
  rw [Equiv.sumCongr_apply, Sum.map_inr, sigmaCongr_apply_mk]
  rfl

private noncomputable def siblingNodeEquiv :
    (OfficialCIPSourceTree.node source leftChildren).HierarchyNode ≃
      (OfficialCIPSourceTree.node source rightChildren).HierarchyNode :=
  (hierarchySumEquiv source leftChildren).trans <|
    (siblingSumEquiv leftChildren rightChildren e childIso).trans
      (hierarchySumEquiv source rightChildren).symm

private theorem siblingNodeEquiv_root
    (present : [] ∈ (OfficialCIPSourceTree.node source leftChildren).hierarchyAddresses) :
    siblingNodeEquiv source leftChildren rightChildren e childIso ⟨[], present⟩ =
      ⟨[], (OfficialCIPSourceTree.node source rightChildren).nil_mem_hierarchyAddresses⟩ := by
  rw [siblingNodeEquiv, Equiv.trans_apply, Equiv.trans_apply, hierarchySumEquiv_apply,
    hierarchyToSum_nil, siblingSumEquiv_inl, hierarchySumEquiv_symm_apply, hierarchyOfSum_inl]

private theorem siblingNodeEquiv_cons
    {slot : Nat} {rest : List Nat}
    (present : slot :: rest ∈
      (OfficialCIPSourceTree.node source leftChildren).hierarchyAddresses) :
    siblingNodeEquiv source leftChildren rightChildren e childIso ⟨slot :: rest, present⟩ =
      ⟨(e ⟨slot, (cons_decomposition source leftChildren present).choose⟩).val ::
          ((childIso ⟨slot, (cons_decomposition source leftChildren present).choose⟩).toEquiv
            ⟨rest, (cons_decomposition source leftChildren present).choose_spec⟩).1,
        cons_mem_hierarchyAddresses source rightChildren
          (e ⟨slot, (cons_decomposition source leftChildren present).choose⟩)
          ((childIso ⟨slot, (cons_decomposition source leftChildren present).choose⟩).toEquiv
            ⟨rest, (cons_decomposition source leftChildren present).choose_spec⟩).2⟩ := by
  rw [siblingNodeEquiv, Equiv.trans_apply, Equiv.trans_apply, hierarchySumEquiv_apply,
    hierarchyToSum_cons, siblingSumEquiv_inr, hierarchySumEquiv_symm_apply, hierarchyOfSum_inr]

private theorem siblingNodeEquiv_depth
    (node : (OfficialCIPSourceTree.node source leftChildren).HierarchyNode) :
    node.1.length =
      (siblingNodeEquiv source leftChildren rightChildren e childIso node).1.length := by
  rcases node with ⟨address, present⟩
  cases address with
  | nil =>
      rw [siblingNodeEquiv_root]
  | cons slot rest =>
      rw [siblingNodeEquiv_cons]
      have bound := (cons_decomposition source leftChildren present).choose
      have restMem := (cons_decomposition source leftChildren present).choose_spec
      let i : Fin leftChildren.length := ⟨slot, bound⟩
      have childDepth :=
        (childIso i).map_depth ⟨rest, restMem⟩
      simpa [RootedDigraph.depth] using congrArg Nat.succ childDepth

private theorem hierarchy_cast_val
    {t1 t2 : OfficialCIPSourceTree V} (h : t1 = t2) (node : t1.HierarchyNode) :
    ((h ▸ node) : t2.HierarchyNode).1 = node.1 := by
  subst h
  rfl

private theorem childImage_cast
    {i j : Fin leftChildren.length} (h : i = j)
    (node : (leftChildren.get i).HierarchyNode) :
    ((childIso i).toEquiv node).1 =
      ((childIso j).toEquiv (congrArg leftChildren.get h ▸ node)).1 := by
  subst h
  rfl

private noncomputable def siblingGraphIso :
    RootedDigraph.Iso
      (OfficialCIPSourceTree.node source leftChildren).toDeclarativeDigraph
      (OfficialCIPSourceTree.node source rightChildren).toDeclarativeDigraph where
  toEquiv := siblingNodeEquiv source leftChildren rightChildren e childIso
  map_root := by
    simpa [OfficialCIPSourceTree.toDeclarativeDigraph] using
      siblingNodeEquiv_root source leftChildren rightChildren e childIso
        ((OfficialCIPSourceTree.node source leftChildren).nil_mem_hierarchyAddresses)
  map_label := by
    intro node
    simp only [OfficialCIPSourceTree.toDeclarativeDigraph]
    rcases node with ⟨address, present⟩
    cases address with
    | nil =>
        rw [siblingNodeEquiv_root, declarativeLabel_root, declarativeLabel_root]
        rfl
    | cons slot rest =>
        rw [siblingNodeEquiv_cons]
        have bound := (cons_decomposition source leftChildren present).choose
        have restMem := (cons_decomposition source leftChildren present).choose_spec
        let i : Fin leftChildren.length := ⟨slot, bound⟩
        let image := (childIso i).toEquiv ⟨rest, restMem⟩
        rw [declarativeLabel_cons source leftChildren i restMem present]
        have imageLabel :=
          (declarativeLabel_cons source rightChildren (e i) image.2
            (cons_mem_hierarchyAddresses source rightChildren (e i) image.2)).symm
        have childLabel := (childIso i).map_label ⟨rest, restMem⟩
        simpa [OfficialCIPSourceTree.toDeclarativeDigraph] using childLabel.trans imageLabel
  map_depth := by
    intro node
    simpa [OfficialCIPSourceTree.toDeclarativeDigraph] using
      siblingNodeEquiv_depth source leftChildren rightChildren e childIso node
  map_child := by
    intro parent node
    simp only [OfficialCIPSourceTree.toDeclarativeDigraph]
    constructor
    · intro edge
      rcases edge with ⟨extra, addrEq⟩
      rcases parent with ⟨parentAddress, parentPresent⟩
      rcases node with ⟨nodeAddress, nodePresent⟩
      cases parentAddress with
      | nil =>
          have nodeForm : nodeAddress = [extra] := by
            simpa [List.nil_append] using addrEq
          subst nodeForm
          have imageParent :=
            siblingNodeEquiv_root source leftChildren rightChildren e childIso parentPresent
          have imageNode :=
            siblingNodeEquiv_cons source leftChildren rightChildren e childIso nodePresent
          have imageNil :
              ((childIso ⟨extra,
                  (cons_decomposition source leftChildren nodePresent).choose⟩).toEquiv
                ⟨[], (cons_decomposition source leftChildren nodePresent).choose_spec⟩).1 = [] := by
            let i : Fin leftChildren.length :=
              ⟨extra, (cons_decomposition source leftChildren nodePresent).choose⟩
            let restNode : (leftChildren.get i).HierarchyNode :=
              ⟨[], (cons_decomposition source leftChildren nodePresent).choose_spec⟩
            have restRoot :
                restNode = ⟨[], (leftChildren.get i).nil_mem_hierarchyAddresses⟩ :=
              Subtype.ext rfl
            have mapped :
                (childIso i).toEquiv restNode =
                  (rightChildren.get (e i)).toDeclarativeDigraph.root := by
              rw [restRoot]
              exact (childIso i).map_root
            simpa [i, restNode] using congrArg Subtype.val mapped
          refine ⟨(e ⟨extra,
              (cons_decomposition source leftChildren nodePresent).choose⟩).val, ?_⟩
          have parentAddr := congrArg Subtype.val imageParent
          have nodeAddr := congrArg Subtype.val imageNode
          rw [parentAddr, nodeAddr, List.nil_append]
          change
            (e ⟨extra, (cons_decomposition source leftChildren nodePresent).choose⟩).val ::
                ((childIso ⟨extra,
                    (cons_decomposition source leftChildren nodePresent).choose⟩).toEquiv
                  ⟨[], (cons_decomposition source leftChildren nodePresent).choose_spec⟩).1 =
              [(e ⟨extra, (cons_decomposition source leftChildren nodePresent).choose⟩).val]
          rw [imageNil]
      | cons parentSlot parentRest =>
          have nodeForm : nodeAddress = parentSlot :: (parentRest ++ [extra]) := by
            simpa [List.cons_append] using addrEq
          subst nodeForm
          let iParent : Fin leftChildren.length :=
            ⟨parentSlot, (cons_decomposition source leftChildren parentPresent).choose⟩
          let iNode : Fin leftChildren.length :=
            ⟨parentSlot, (cons_decomposition source leftChildren nodePresent).choose⟩
          have iEq : iNode = iParent := Fin.ext rfl
          let parentChild : (leftChildren.get iParent).HierarchyNode :=
            ⟨parentRest, (cons_decomposition source leftChildren parentPresent).choose_spec⟩
          let nodeChild : (leftChildren.get iNode).HierarchyNode :=
            ⟨parentRest ++ [extra],
              (cons_decomposition source leftChildren nodePresent).choose_spec⟩
          have treeEq : leftChildren.get iNode = leftChildren.get iParent :=
            congrArg leftChildren.get iEq
          let nodeOnParent : (leftChildren.get iParent).HierarchyNode := treeEq ▸ nodeChild
          have nodeAddr : nodeOnParent.1 = parentRest ++ [extra] :=
            hierarchy_cast_val treeEq nodeChild
          have childEdge :
              (leftChildren.get iParent).HierarchyChild parentChild nodeOnParent :=
            ⟨extra, by rw [nodeAddr]⟩
          have imageEdge :=
            ((childIso iParent).map_child parentChild nodeOnParent).mp
              (by simpa [OfficialCIPSourceTree.toDeclarativeDigraph] using childEdge)
          rcases imageEdge with ⟨imageSlot, imageEq⟩
          refine ⟨imageSlot, ?_⟩
          rw [siblingNodeEquiv_cons, siblingNodeEquiv_cons]
          change
            (e iNode).val :: ((childIso iNode).toEquiv nodeChild).1 =
              ((e iParent).val :: ((childIso iParent).toEquiv parentChild).1) ++ [imageSlot]
          rw [childImage_cast leftChildren rightChildren e childIso iEq nodeChild]
          have headEq : (e iNode).val = (e iParent).val :=
            congrArg (fun k => (e k).val) iEq
          rw [headEq, imageEq, List.cons_append]
    · intro edge
      rcases edge with ⟨extra, addrEq⟩
      rcases parent with ⟨parentAddress, parentPresent⟩
      rcases node with ⟨nodeAddress, nodePresent⟩
      cases parentAddress with
      | nil =>
          rw [siblingNodeEquiv_root] at addrEq
          cases nodeAddress with
          | nil =>
              rw [siblingNodeEquiv_root] at addrEq
              have bad : [] = [extra] := by
                simpa [List.nil_append] using addrEq
              cases bad
          | cons slot rest =>
              rw [siblingNodeEquiv_cons] at addrEq
              let i : Fin leftChildren.length :=
                ⟨slot, (cons_decomposition source leftChildren nodePresent).choose⟩
              let restNode : (leftChildren.get i).HierarchyNode :=
                ⟨rest, (cons_decomposition source leftChildren nodePresent).choose_spec⟩
              have addrCons :
                  (e i).val :: ((childIso i).toEquiv restNode).1 = [extra] := by
                simpa [i, restNode, List.nil_append] using addrEq
              injection addrCons with _slotEq restEq
              have imageRoot :
                  (childIso i).toEquiv restNode =
                    ⟨[], (rightChildren.get (e i)).nil_mem_hierarchyAddresses⟩ :=
                Subtype.ext restEq
              have restRoot :
                  restNode = ⟨[], (leftChildren.get i).nil_mem_hierarchyAddresses⟩ := by
                apply (childIso i).toEquiv.injective
                rw [imageRoot]
                exact (childIso i).map_root.symm
              have restNil : rest = [] := congrArg Subtype.val restRoot
              subst restNil
              exact ⟨slot, by simp [List.nil_append]⟩
      | cons parentSlot parentRest =>
          cases nodeAddress with
          | nil =>
              rw [siblingNodeEquiv_cons, siblingNodeEquiv_root] at addrEq
              cases (by simpa [List.cons_append] using addrEq :
                (e ⟨parentSlot,
                    (cons_decomposition source leftChildren parentPresent).choose⟩).val ::
                  (((childIso ⟨parentSlot,
                      (cons_decomposition source leftChildren parentPresent).choose⟩).toEquiv
                    ⟨parentRest,
                      (cons_decomposition source leftChildren parentPresent).choose_spec⟩).1 ++
                    [extra]) = [])
          | cons slot rest =>
              rw [siblingNodeEquiv_cons, siblingNodeEquiv_cons] at addrEq
              let iParent : Fin leftChildren.length :=
                ⟨parentSlot, (cons_decomposition source leftChildren parentPresent).choose⟩
              let iNode : Fin leftChildren.length :=
                ⟨slot, (cons_decomposition source leftChildren nodePresent).choose⟩
              let parentChild : (leftChildren.get iParent).HierarchyNode :=
                ⟨parentRest, (cons_decomposition source leftChildren parentPresent).choose_spec⟩
              let nodeChild : (leftChildren.get iNode).HierarchyNode :=
                ⟨rest, (cons_decomposition source leftChildren nodePresent).choose_spec⟩
              have addrCons :
                  (e iNode).val :: ((childIso iNode).toEquiv nodeChild).1 =
                    (e iParent).val ::
                      (((childIso iParent).toEquiv parentChild).1 ++ [extra]) := by
                simpa [iParent, iNode, parentChild, nodeChild, List.cons_append] using addrEq
              injection addrCons with slotValEq tailEq
              have iEq : iNode = iParent := e.injective (Fin.ext slotValEq)
              have treeEq : leftChildren.get iNode = leftChildren.get iParent :=
                congrArg leftChildren.get iEq
              let nodeOnParent : (leftChildren.get iParent).HierarchyNode := treeEq ▸ nodeChild
              have imageCast :
                  ((childIso iNode).toEquiv nodeChild).1 =
                    ((childIso iParent).toEquiv nodeOnParent).1 :=
                childImage_cast leftChildren rightChildren e childIso iEq nodeChild
              have imageEdge :
                  (rightChildren.get (e iParent)).HierarchyChild
                    ((childIso iParent).toEquiv parentChild)
                    ((childIso iParent).toEquiv nodeOnParent) :=
                ⟨extra, by rw [← imageCast]; exact tailEq⟩
              have originalEdge :=
                ((childIso iParent).map_child parentChild nodeOnParent).mpr
                  (by simpa [OfficialCIPSourceTree.toDeclarativeDigraph] using imageEdge)
              rcases originalEdge with ⟨originalSlot, originalEq⟩
              have restEq : rest = parentRest ++ [originalSlot] := by
                have nodeAddr := hierarchy_cast_val treeEq nodeChild
                have nodeVal : nodeOnParent.1 = rest := by
                  simpa [nodeChild] using nodeAddr
                rw [← nodeVal]
                simpa [parentChild] using originalEq
              have slotNatEq : slot = parentSlot := congrArg Fin.val iEq
              subst slotNatEq
              refine ⟨originalSlot, ?_⟩
              simp [List.cons_append, restEq]

end SiblingIso

/-! ## Equal source cursors at one fuel have isomorphic stage graphs -/

private theorem get_map_source
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (trees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (i : Fin trees.length) :
    (trees.map (fun tree => tree.source)).get
        (i.cast (List.length_map
          (fun tree : LocalizedCumulativeDecoratedTree input carrierFuel => tree.source)).symm) =
      (trees.get i).source := by
  rw [List.get_eq_getElem, List.getElem_map, List.get_eq_getElem]
  rfl

private theorem cursor_eq_of_rootTree
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    (localizedRootTree input cursor label children).source = cursor := rfl

/-- The erased stage graph does not depend on the auxiliary label stored at the root.
`toOfficialSourceTree` drops that label before `toDeclarativeDigraph` is formed. -/
private theorem ruleMajorTreeGraph_label_irrelevant
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label₁ label₂ : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    ruleMajorTreeGraph (localizedRootTree input cursor label₁ children) =
      ruleMajorTreeGraph (localizedRootTree input cursor label₂ children) := by
  unfold ruleMajorTreeGraph
  rw [toOfficialSourceTree_localizedRootTree, toOfficialSourceTree_localizedRootTree]

/-- Two actual cumulative traces at one fuel and one source cursor have isomorphic erased stage
graphs, for arbitrary stages and arbitrary readers.

`ruleMajorTreeGraph` erases the auxiliary stereo label, atomic number, Rule-1b distance and
isotope.  Its digraph label retains the stored occurrence's `current?` and provenance.
Different readers may permute siblings; they do not change `localizedRerootChildren?` of the
shared source cursor.  The isomorphism transports that topology and those occurrence labels.

It does not transport cumulative keys and does not transfer an arbitrary stereochemical reading
across the reader change.  `descriptorMap` stays fixed and is still read independently at the
stored source occurrences.  No reader equality, desired label, correct outcome, acyclicity, or
all-real hypothesis is used. -/
theorem ruleMajorTreeGraph_iso_nonempty_of_sameSourceCrossReaderTraces
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) :
    ∀ {stageL stageR : LocalizedCumulativeRule45Stage}
      {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
      {keyL keyR : input.LocalizedRerootCumulativeRule45Key},
      LocalizedRuleMajorSortTrace input stageL readL fuel treeL keyL →
      LocalizedRuleMajorSortTrace input stageR readR fuel treeR keyR →
      treeL.source = treeR.source →
      Nonempty (RootedDigraph.Iso (ruleMajorTreeGraph treeL)
        (ruleMajorTreeGraph treeR)) := by
  induction fuel with
  | zero =>
      intro stageL stageR treeL treeR keyL keyR traceL traceR sourceEq
      cases traceL with
      | terminal _ cursorL _ _ _ _ _ =>
          cases traceR with
          | terminal _ cursorR _ _ _ _ _ =>
              have cursorEq : cursorL = cursorR := by
                simpa [cursor_eq_of_rootTree] using sourceEq
              subst cursorEq
              rw [ruleMajorTreeGraph_label_irrelevant cursorL (readL cursorL) (readR cursorL) []]
              exact ⟨RootedDigraph.Iso.refl _⟩
  | succ fuel ih =>
      intro stageL stageR treeL treeR keyL keyR traceL traceR sourceEq
      rcases LocalizedRuleMajorSortTrace.structure_of_trace traceL with termL | nodeL
      · rcases LocalizedRuleMajorSortTrace.structure_of_trace traceR with termR | nodeR
        · rcases termL with ⟨cursorL, _, treeEqL, _, _, _, _⟩
          rcases termR with ⟨cursorR, _, treeEqR, _, _, _, _⟩
          have cursorEq : cursorL = cursorR := by
            have hL : treeL.source = cursorL := by rw [treeEqL, cursor_eq_of_rootTree]
            have hR : treeR.source = cursorR := by rw [treeEqR, cursor_eq_of_rootTree]
            exact hL.symm.trans (sourceEq.trans hR)
          rw [treeEqL, treeEqR, cursorEq]
          rw [ruleMajorTreeGraph_label_irrelevant cursorR (readL cursorR) (readR cursorR) []]
          exact ⟨RootedDigraph.Iso.refl _⟩
        · rcases termL with ⟨cursorL, childrenL, treeEqL, _, _, computedL, emptyL⟩
          rcases nodeR with ⟨cursorR, childrenR, _, _, _, treeEqR, _, _, computedR, nonemptyR,
            _, _, _, _, _⟩
          have cursorEq : cursorL = cursorR := by
            have hL : treeL.source = cursorL := by rw [treeEqL, cursor_eq_of_rootTree]
            have hR : treeR.source = cursorR := by rw [treeEqR, cursor_eq_of_rootTree]
            exact hL.symm.trans (sourceEq.trans hR)
          have childrenEq : childrenL = childrenR := by
            apply Option.some.inj
            rw [← computedL, ← computedR, cursorEq]
          exact False.elim (nonemptyR (childrenEq.symm.trans emptyL))
      · rcases LocalizedRuleMajorSortTrace.structure_of_trace traceR with termR | nodeR
        · rcases nodeL with ⟨cursorL, childrenL, _, _, _, treeEqL, _, _, computedL, nonemptyL,
            _, _, _, _, _⟩
          rcases termR with ⟨cursorR, childrenR, treeEqR, _, _, computedR, emptyR⟩
          have cursorEq : cursorL = cursorR := by
            have hL : treeL.source = cursorL := by rw [treeEqL, cursor_eq_of_rootTree]
            have hR : treeR.source = cursorR := by rw [treeEqR, cursor_eq_of_rootTree]
            exact hL.symm.trans (sourceEq.trans hR)
          have childrenEq : childrenL = childrenR := by
            apply Option.some.inj
            rw [← computedL, ← computedR, cursorEq]
          exact False.elim (nonemptyL (childrenEq.trans emptyR))
        · rcases nodeL with ⟨cursorL, _childrenL, _childKeysL, sortedKeysL, sortedTreesL,
            treeEqL, _, _, _, _, _, _, _, _, tracedL⟩
          rcases nodeR with ⟨cursorR, _childrenR, _childKeysR, sortedKeysR, sortedTreesR,
            treeEqR, _, _, _, _, _, _, _, _, tracedR⟩
          have cursorEq : cursorL = cursorR := by
            have hL : treeL.source = cursorL := by rw [treeEqL, cursor_eq_of_rootTree]
            have hR : treeR.source = cursorR := by rw [treeEqR, cursor_eq_of_rootTree]
            exact hL.symm.trans (sourceEq.trans hR)
          obtain ⟨frameL, computedFrameL, permL⟩ :=
            exists_sourcePerm (LocalizedRuleMajorSortTrace.realizes_of_trace traceL)
          obtain ⟨frameR, computedFrameR, permR⟩ :=
            exists_sourcePerm (LocalizedRuleMajorSortTrace.realizes_of_trace traceR)
          have frameEq : frameL = frameR := by
            apply Option.some.inj
            rw [← computedFrameL, ← computedFrameR, sourceEq]
          have sourcePerm :
              (sortedTreesL.map fun tree => tree.source).Perm
                (sortedTreesR.map fun tree => tree.source) := by
            have childEqL : treeL.children = sortedTreesL := by
              rw [treeEqL]
              rfl
            have childEqR : treeR.children = sortedTreesR := by
              rw [treeEqR]
              rfl
            have permL' :
                (sortedTreesL.map fun tree => tree.source).Perm frameL := by
              simpa [childEqL] using permL
            have permR' :
                (sortedTreesR.map fun tree => tree.source).Perm frameR := by
              simpa [childEqR] using permR
            exact permL'.trans (frameEq ▸ permR'.symm)
          obtain ⟨eSrc, eSpec⟩ := indexEquiv_of_perm sourcePerm
          have lenSrcL :
              (sortedTreesL.map (fun tree => tree.source)).length = sortedTreesL.length :=
            List.length_map
              (fun tree : LocalizedCumulativeDecoratedTree input carrierFuel => tree.source)
          have lenSrcR :
              (sortedTreesR.map (fun tree => tree.source)).length = sortedTreesR.length :=
            List.length_map
              (fun tree : LocalizedCumulativeDecoratedTree input carrierFuel => tree.source)
          let eDec : Fin sortedTreesL.length ≃ Fin sortedTreesR.length :=
            (finCastEquiv lenSrcL.symm).trans eSrc |>.trans (finCastEquiv lenSrcR)
          have eDecSpec : ∀ i : Fin sortedTreesL.length,
              (sortedTreesL.get i).source = (sortedTreesR.get (eDec i)).source := by
            intro i
            have mapped := eSpec (i.cast lenSrcL.symm)
            have leftSrc := get_map_source sortedTreesL i
            have rightSrc := get_map_source sortedTreesR (eDec i)
            have rightIdx :
                eSrc (i.cast lenSrcL.symm) = (eDec i).cast lenSrcR.symm := by
              apply Fin.ext
              simp only [eDec, Equiv.trans_apply, finCastEquiv_apply, Fin.val_cast]
            exact (leftSrc.symm.trans mapped).trans
              ((congrArg
                  (fun j => (sortedTreesR.map (fun tree => tree.source)).get j) rightIdx).trans
                rightSrc)
          let offL := sortedTreesL.map toOfficialSourceTree
          let offR := sortedTreesR.map toOfficialSourceTree
          have lenOffL : offL.length = sortedTreesL.length :=
            List.length_map toOfficialSourceTree
          have lenOffR : offR.length = sortedTreesR.length :=
            List.length_map toOfficialSourceTree
          let eOff : Fin offL.length ≃ Fin offR.length :=
            (finCastEquiv lenOffL).trans eDec |>.trans (finCastEquiv lenOffR.symm)
          have forallL := LocalizedRuleMajorSortTraceList.to_forall₂ tracedL
          have forallR := LocalizedRuleMajorSortTraceList.to_forall₂ tracedR
          have childIsoOff : ∀ i : Fin offL.length,
              RootedDigraph.Iso (offL.get i).toDeclarativeDigraph
                (offR.get (eOff i)).toDeclarativeDigraph := by
            intro i
            let iDec : Fin sortedTreesL.length := i.cast lenOffL
            have keyLenL : sortedKeysL.length = sortedTreesL.length := forallL.length_eq
            have keyLenR : sortedKeysR.length = sortedTreesR.length := forallR.length_eq
            have traceChildL :=
              forallL.get (i := iDec.val)
                (by rw [keyLenL]; exact iDec.isLt) iDec.isLt
            have traceChildR :=
              forallR.get (i := (eDec iDec).val)
                (by
                  rw [keyLenR]
                  exact (eDec iDec).isLt)
                (eDec iDec).isLt
            have sourceChild := eDecSpec iDec
            have isoChild := Classical.choice (ih traceChildL traceChildR sourceChild)
            have leftGraph :
                (offL.get i).toDeclarativeDigraph =
                  ruleMajorTreeGraph (sortedTreesL.get iDec) := by
              simp [offL, ruleMajorTreeGraph, List.get_eq_getElem, List.getElem_map, iDec,
                Fin.val_cast]
            have rightIndex :
                eOff i = (eDec iDec).cast lenOffR.symm := by
              ext
              simp [eOff, eDec, iDec, Equiv.trans_apply, finCastEquiv_apply, Fin.val_cast]
            have rightGraph :
                (offR.get (eOff i)).toDeclarativeDigraph =
                  ruleMajorTreeGraph (sortedTreesR.get (eDec iDec)) := by
              rw [rightIndex]
              simp [offR, ruleMajorTreeGraph, List.get_eq_getElem, List.getElem_map, Fin.val_cast]
            exact leftGraph.symm ▸ rightGraph.symm ▸ isoChild
          have sourceNodeEq :
              cursorL.occurrence.1.node = cursorR.occurrence.1.node := by
            rw [cursorEq]
          have leftSource :
              toOfficialSourceTree treeL =
                OfficialCIPSourceTree.node cursorL.occurrence.1.node offL := by
            simp [offL, treeEqL, toOfficialSourceTree_localizedRootTree,
              toOfficialSourceTreeList_eq_map]
          have rightSource :
              toOfficialSourceTree treeR =
                OfficialCIPSourceTree.node cursorR.occurrence.1.node offR := by
            simp [offR, treeEqR, toOfficialSourceTree_localizedRootTree,
              toOfficialSourceTreeList_eq_map]
          have iso :=
            siblingGraphIso cursorL.occurrence.1.node offL offR eOff childIsoOff
          have graphL :
              ruleMajorTreeGraph treeL =
                (OfficialCIPSourceTree.node cursorL.occurrence.1.node offL).toDeclarativeDigraph := by
            unfold ruleMajorTreeGraph
            rw [leftSource]
          have graphR :
              ruleMajorTreeGraph treeR =
                (OfficialCIPSourceTree.node cursorL.occurrence.1.node offR).toDeclarativeDigraph := by
            unfold ruleMajorTreeGraph
            rw [rightSource, ← sourceNodeEq]
          exact ⟨graphL.symm ▸ graphR.symm ▸ iso⟩

/-- Same-reader specialization of the cross-reader stage-graph isomorphism.  The two traces use
one reader; the erased graph is still the only object identified. -/
theorem ruleMajorTreeGraph_iso_nonempty_of_sameSourceTraces
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) :
    ∀ {stageL stageR : LocalizedCumulativeRule45Stage}
      {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
      {keyL keyR : input.LocalizedRerootCumulativeRule45Key},
      LocalizedRuleMajorSortTrace input stageL read fuel treeL keyL →
      LocalizedRuleMajorSortTrace input stageR read fuel treeR keyR →
      treeL.source = treeR.source →
      Nonempty (RootedDigraph.Iso (ruleMajorTreeGraph treeL)
        (ruleMajorTreeGraph treeR)) :=
  ruleMajorTreeGraph_iso_nonempty_of_sameSourceCrossReaderTraces read read fuel

/-- Every actual contextual stage at one cursor is isomorphic to the Rule-4a stage graph.
The six arms already carry traces at the same fuel and the same cursor, so the isomorphism does
not assume a valid incoming edge, a simple-bonded acyclic carrier, or a fresh physical root. -/
noncomputable def ruleMajorContextStageGraphIsoBundle_of_stages
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (stages : input.RuleMajorContextStages carrierFuel read cursor) :
    RuleMajorContextStageGraphIsoBundle stages where
  b reference :=
    Classical.choice
      (ruleMajorTreeGraph_iso_nonempty_of_sameSourceTraces read (2 * (carrierFuel + 1))
        stages.a.trace (stages.b reference).trace
        (stages.a.sourceEq.trans (stages.b reference).sourceEq.symm))
  c reference :=
    Classical.choice
      (ruleMajorTreeGraph_iso_nonempty_of_sameSourceTraces read (2 * (carrierFuel + 1))
        stages.a.trace (stages.c reference).trace
        (stages.a.sourceEq.trans (stages.c reference).sourceEq.symm))
  noReference :=
    Classical.choice
      (ruleMajorTreeGraph_iso_nonempty_of_sameSourceTraces read (2 * (carrierFuel + 1))
        stages.a.trace stages.noReference.trace
        (stages.a.sourceEq.trans stages.noReference.sourceEq.symm))

assert_kernel_only ruleMajorTreeGraph_iso_nonempty_of_sameSourceCrossReaderTraces
assert_kernel_only ruleMajorTreeGraph_iso_nonempty_of_sameSourceTraces
assert_kernel_only ruleMajorContextStageGraphIsoBundle_of_stages

end

end Rule4aTableBridge
end TetraStereo.OneCenter
