/-
COORDINATION: Rootward Rule-1a separation only. Do not edit the arm-expansion,
locality, transport, reconstruction, or cyclic-fixture modules. The predecessor
cut and its faithfulness isomorphism are used as already proved.
-/
import TetraStereo.OneCenter.LocalizedRetainedRealArmExpansion
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Rootward constitutional separation

When two real arms of a carrier root tie at complete Rule 1a, every real node on
one of those arms separates its actual parent cut from every outward cut at Rule 1a.
The comparison is a node-count gap in the retained carrier. Missing sparse spheres
are empty lists, so the addressed Rule 1a table has one entry per decorated node.
-/

namespace TetraStereo.OneCenter
namespace LocalizedRootwardConstitutionalSeparation

open DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier
open DeclarativeCIP.RetainedCutArm
open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open OfficialCIPSourceTree
open SparseAddress
open OfficialRuleMajorKey
open Rule4aTableBridge

noncomputable section
open scoped Classical

abbrev carrierFuel (input : CertifiedLocalizedCIPInput) : Nat :=
  input.certified.input.molecule.atomCount + 1

/-! ## List prefixes -/

private theorem length_le_of_isPrefix {α : Type*} {l m : List α} (h : l <+: m) :
    l.length ≤ m.length := by
  obtain ⟨t, ht⟩ := h
  have := congrArg List.length ht
  simp at this
  omega

private theorem isPrefix_eq_of_length_eq {α : Type*} {l m : List α}
    (h : l <+: m) (hlen : l.length = m.length) : l = m := by
  obtain ⟨t, ht⟩ := h
  have htlen : t.length = 0 := by
    have := congrArg List.length ht
    simp at this
    omega
  simp [List.length_eq_zero_iff.mp htlen] at ht
  exact ht

private theorem head?_eq_of_isPrefix {α : Type*} {l m : List α}
    (h : l <+: m) (hne : l ≠ []) : l.head? = m.head? := by
  obtain ⟨t, ht⟩ := h
  cases l with
  | nil => exact (hne rfl).elim
  | cons a as =>
      cases m with
      | nil => simp at ht
      | cons b bs =>
          simp at ht
          simp [ht.1]

private theorem prefix_append_singleton {α : Type*} (l : List α) (a : α) :
    l <+: l ++ [a] :=
  ⟨[a], by simp⟩

private theorem dropLast_isPrefix {α : Type*} {l : List α} (h : l ≠ []) :
    l.dropLast <+: l := by
  refine ⟨[l.getLast h], ?_⟩
  simp [List.dropLast_concat_getLast h]

private theorem dropLast_cons_of_ne_nil {α : Type*} (a : α) {l : List α} (hl : l ≠ []) :
    (a :: l).dropLast = a :: l.dropLast := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons _ _ => rfl

private theorem dropLast_append_of_ne_nil {α : Type*} {l t : List α} (ht : t ≠ []) :
    (l ++ t).dropLast = l ++ t.dropLast := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hne : l ++ t ≠ [] := by
        cases t with
        | nil => exact (ht rfl).elim
        | cons _ _ => simp
      rw [List.cons_append, dropLast_cons_of_ne_nil a hne, ih]
      simp

private theorem prefix_dropLast_of_ne {α : Type*} {l s : List α}
    (h : l <+: s) (hne : l ≠ s) (_hs : s ≠ []) : l <+: s.dropLast := by
  obtain ⟨t, ht⟩ := h
  have htne : t ≠ [] := by
    intro hempty
    apply hne
    simpa [hempty] using ht
  rw [← ht, dropLast_append_of_ne_nil htne]
  exact ⟨t.dropLast, rfl⟩

private theorem prefix_ne_concat {α : Type*} {l s : List α} {a : α}
    (h : l <+: s ++ [a]) (hne : l ≠ s ++ [a]) : l <+: s := by
  induction s generalizing l with
  | nil =>
      obtain ⟨t, ht⟩ := h
      cases t with
      | nil => exact (hne (by simpa using ht)).elim
      | cons b rest =>
          cases rest with
          | nil =>
              cases l with
              | nil => exact ⟨[], rfl⟩
              | cons _ _ => simp at ht
          | cons =>
              have := congrArg List.length ht
              simp at this
              omega
  | cons x xs ih =>
      cases l with
      | nil => exact ⟨x :: xs, by simp⟩
      | cons y ys =>
          obtain ⟨t, ht⟩ := h
          have hy : y = x := by
            have := congrArg List.head? ht
            simp at this
            exact this
          have htail : ys ++ t = xs ++ [a] := by
            have := congrArg List.tail ht
            simp [hy] at this
            exact this
          have hys : ys <+: xs ++ [a] := ⟨t, htail⟩
          have hysNe : ys ≠ xs ++ [a] := by
            intro heq
            apply hne
            simp [hy, heq]
          obtain ⟨t', ht'⟩ := ih hys hysNe
          refine ⟨t', ?_⟩
          simp [hy, ht']

private theorem pair_prefix_eq {α : Type*} {r a b : α} {path : List α}
    (ha : [r, a] <+: path) (hb : [r, b] <+: path) : a = b := by
  obtain ⟨ta, hta⟩ := ha
  obtain ⟨tb, htb⟩ := hb
  have hjoin : r :: a :: ta = r :: b :: tb := by simpa using hta.trans htb.symm
  injections

private theorem range_succ_eq_cons_map (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => simp [List.range_succ]
  | succ n ih =>
      calc
        List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by rw [List.range_succ]
        _ = (0 :: (List.range n).map Nat.succ) ++ [n + 1] := by rw [ih]
        _ = 0 :: ((List.range n).map Nat.succ ++ [n + 1]) := by simp
        _ = 0 :: ((List.range n ++ [n]).map Nat.succ) := by simp [List.map_append]
        _ = 0 :: (List.range (n + 1)).map Nat.succ := by rw [List.range_succ]

private theorem sum_map_const_zero (n : Nat) :
    ((List.range n).map fun _ : Nat => (0 : Nat)).sum = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp

/-! ## Carrier cones of one reroot -/

section Cones

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

def CarrierExtends (base : List Atom) : CarrierNode Atom → Prop
  | .real path => base <+: path
  | .ring path _ => base <+: path

def pathOf : CarrierNode Atom → List Atom
  | .real path => path
  | .ring path _ => path

private theorem carrierExtends_iff {base : List Atom} {node : CarrierNode Atom} :
    CarrierExtends base node ↔ base <+: pathOf node := by
  cases node <;> simp [CarrierExtends, pathOf]

def Extending (molecule : MoleculeGraph Atom) (root : Atom) (base : List Atom) :=
  {node : Nodes molecule root // CarrierExtends base node.1}

def Avoiding (molecule : MoleculeGraph Atom) (root : Atom) (base : List Atom) :=
  {node : Nodes molecule root // ¬ CarrierExtends base node.1}

private theorem nodes_finite (molecule : MoleculeGraph Atom) (root : Atom) :
    Finite (Nodes molecule root) :=
  (valid_finite molecule root).to_subtype

private theorem extending_finite (molecule : MoleculeGraph Atom) (root : Atom)
    (base : List Atom) : Finite (Extending molecule root base) := by
  haveI := nodes_finite molecule root
  exact Finite.of_injective Subtype.val Subtype.val_injective

private theorem avoiding_finite (molecule : MoleculeGraph Atom) (root : Atom)
    (base : List Atom) : Finite (Avoiding molecule root base) := by
  haveI := nodes_finite molecule root
  exact Finite.of_injective Subtype.val Subtype.val_injective

private theorem natCard_lt_of_injective_miss {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (hf : Function.Injective f) (miss : β) (hmiss : ∀ a, f a ≠ miss) :
    Nat.card α < Nat.card β := by
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcard : (Finset.univ.map ⟨f, hf⟩).card = Fintype.card α := by
    rw [Finset.card_map]
    simp
  rw [← hcard]
  apply Finset.card_lt_card
  refine ⟨Finset.subset_univ _, ?_⟩
  intro hsubset
  have hmem : miss ∈ Finset.univ.map ⟨f, hf⟩ := hsubset (Finset.mem_univ miss)
  rw [Finset.mem_map] at hmem
  obtain ⟨a, _, ha⟩ := hmem
  exact hmiss a ha

private theorem natCard_ge_two {α : Type*} [Finite α] (a b : α) (hab : a ≠ b) :
    2 ≤ Nat.card α := by
  letI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  have hpair : Finset.card ({a, b} : Finset α) = 2 := Finset.card_pair hab
  exact hpair ▸ Finset.card_le_card (Finset.subset_univ ({a, b} : Finset α))

private theorem ne_focus_of_armChild {molecule : MoleculeGraph Atom} {root : Atom}
    {focus : List Atom} {parent node : Nodes molecule root}
    (hchild : armChild focus parent node) : node.1 ≠ .real focus := by
  intro heq
  have hraw : rawNewParent focus node.1 = some parent.1 := hchild
  rw [heq, rawNewParent_focus] at hraw
  cases hraw

private theorem extends_trans {base longer : List Atom} {node : CarrierNode Atom}
    (hbase : base <+: longer) (hext : CarrierExtends longer node) :
    CarrierExtends base node := by
  rw [carrierExtends_iff] at hext ⊢
  exact hbase.trans hext

private theorem not_extends_of_shorter {base path : List Atom}
    (h : path.length < base.length) : ¬ base <+: path := by
  intro hpre
  have hle := length_le_of_isPrefix hpre
  omega

private theorem extends_parent_of_node_extends {molecule : MoleculeGraph Atom} {root : Atom}
    {focus : List Atom} (_hfocus : SimpleFrom molecule root focus)
    {parent node : Nodes molecule root}
    (hchild : armChild focus parent node)
    (hext : CarrierExtends focus node.1) : CarrierExtends focus parent.1 := by
  have hne := ne_focus_of_armChild hchild
  have hraw : rawNewParent focus node.1 = some parent.1 := hchild
  cases node with
  | mk val hval =>
      cases val with
      | ring path atom =>
          have hringNe : CarrierNode.ring path atom ≠ CarrierNode.real focus := by
            intro h; cases h
          rw [rawNewParent, if_neg hringNe] at hraw
          injection hraw with hparent
          rw [← hparent]
          simpa [CarrierExtends] using hext
      | real path =>
          unfold rawNewParent at hraw
          rw [if_neg hne] at hraw
          by_cases hpre : path.length < focus.length ∧ focus.take path.length = path
          · simp [hpre] at hraw
            have hlen := length_le_of_isPrefix (by simpa [CarrierExtends] using hext)
            have hlt : path.length < focus.length := hpre.1
            omega
          · simp [hpre] at hraw
            have hpathNe : path ≠ focus := by
              intro heq
              apply hne
              simp [heq]
            have hprefix : focus <+: path := by simpa [CarrierExtends] using hext
            have hdrop : focus <+: path.dropLast :=
              prefix_dropLast_of_ne hprefix hpathNe.symm (SimpleFrom.ne_nil hval)
            rw [← hraw]
            simpa [CarrierExtends] using hdrop

private theorem not_extends_step {molecule : MoleculeGraph Atom} {root : Atom}
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {parent node : Nodes molecule root}
    (hchild : armChild focus parent node)
    (hparent : ¬ CarrierExtends focus parent.1) : ¬ CarrierExtends focus node.1 := by
  intro hext
  exact hparent (extends_parent_of_node_extends hfocus hchild hext)

private theorem extends_propagates_from_parent {molecule : MoleculeGraph Atom} {root : Atom}
    {focus : List Atom} (_hfocus : SimpleFrom molecule root focus)
    (hlen : 1 < focus.length) {parent node : Nodes molecule root}
    (hchild : armChild focus parent node)
    (hparent : CarrierExtends focus parent.1)
    (hnotInward : node.1 ≠ .real focus.dropLast) : CarrierExtends focus node.1 := by
  have hne := ne_focus_of_armChild hchild
  have hraw : rawNewParent focus node.1 = some parent.1 := hchild
  cases node with
  | mk val hval =>
      cases val with
      | ring path atom =>
          have hringNe : CarrierNode.ring path atom ≠ CarrierNode.real focus := by
            intro h; cases h
          rw [rawNewParent, if_neg hringNe] at hraw
          injection hraw with hparentNode
          have hprefix : focus <+: path := by
            have : CarrierExtends focus parent.1 := hparent
            rw [← hparentNode] at this
            simpa [CarrierExtends] using this
          simpa [CarrierExtends] using hprefix
      | real path =>
          unfold rawNewParent at hraw
          rw [if_neg hne] at hraw
          by_cases hpre : path.length < focus.length ∧ focus.take path.length = path
          · simp [hpre] at hraw
            have hparentPath : focus <+: path ++ [focus[path.length]'(hpre.1)] := by
              have : CarrierExtends focus (.real (path ++ [focus[path.length]'(hpre.1)])) := by
                rw [← hraw] at hparent
                exact hparent
              simpa [CarrierExtends] using this
            have hlenEq : (path ++ [focus[path.length]'(hpre.1)]).length = focus.length := by
              have hle := length_le_of_isPrefix hparentPath
              have happ : (path ++ [focus[path.length]'(hpre.1)]).length = path.length + 1 := by
                simp
              have hlt : path.length < focus.length := hpre.1
              omega
            have hjoin := isPrefix_eq_of_length_eq hparentPath hlenEq.symm
            have hdrop : path = focus.dropLast := by
              rw [hjoin]
              simp [List.dropLast_concat]
            exact (hnotInward (by simp [hdrop])).elim
          · simp [hpre] at hraw
            have hprefix : focus <+: path.dropLast := by
              have : CarrierExtends focus parent.1 := hparent
              rw [← hraw] at this
              simpa [CarrierExtends] using this
            exact extends_trans hprefix (by
              rw [carrierExtends_iff]
              exact dropLast_isPrefix (SimpleFrom.ne_nil hval))

/-- The subtree of the inward predecessor is the complement of the focus cone. -/
theorem inArmSubtree_predecessor_iff {molecule : MoleculeGraph Atom} {root : Atom}
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (hlen : 1 < focus.length) (node : Nodes molecule root) :
    InArmSubtree focus ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩ node ↔
      ¬ CarrierExtends focus node.1 := by
  let inward : Nodes molecule root := ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩
  constructor
  · intro hsub
    induction hsub with
    | refl =>
        intro hext
        have hlenDrop : focus.dropLast.length < focus.length := by
          have hsplit := List.dropLast_concat_getLast (SimpleFrom.ne_nil hfocus)
          have hlenEq := congrArg List.length hsplit
          have : focus.dropLast.length + 1 = focus.length := by
            simpa [List.length_append] using hlenEq
          omega
        exact not_extends_of_shorter hlenDrop (by simpa [CarrierExtends] using hext)
    | @tail prev step _ hstep ih =>
        exact not_extends_step hfocus hstep ih
  · intro hnot
    suffices ∀ d, ∀ node : Nodes molecule root, armDepth focus node.1 = d →
        ¬ CarrierExtends focus node.1 → InArmSubtree focus inward node by
      exact this (armDepth focus node.1) node rfl hnot
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih node hd hnot
    by_cases hinward : node.1 = .real focus.dropLast
    · have : node = inward := Subtype.ext hinward
      subst this
      exact Relation.ReflTransGen.refl
    · have hneFocus : node.1 ≠ .real focus := by
        intro heq
        apply hnot
        simpa [heq, CarrierExtends] using (List.prefix_refl focus)
      obtain ⟨parentVal, hraw, hvalid, hdepth⟩ := rawNewParent_spec hfocus node.2 hneFocus
      let parent : Nodes molecule root := ⟨parentVal, hvalid⟩
      have hchild : armChild focus parent node := hraw
      have hparentNot : ¬ CarrierExtends focus parent.1 := by
        intro hparent
        exact hnot (extends_propagates_from_parent hfocus hlen hchild hparent hinward)
      have hlt : armDepth focus parentVal < d := by
        have hdepth' : armDepth focus node.1 = armDepth focus parentVal + 1 := hdepth
        rw [hd] at hdepth'
        omega
      have hparentDepth : armDepth focus parent.1 = armDepth focus parentVal := by
        rfl
      exact (ih _ (hparentDepth ▸ hlt) parent rfl hparentNot).tail hchild

private theorem extends_of_extension_step {molecule : MoleculeGraph Atom} {root : Atom}
    {focus childPath : List Atom} {atom : Atom}
    (hshape : childPath = focus ++ [atom]) {parent node : Nodes molecule root}
    (hchild : armChild focus parent node)
    (hext : CarrierExtends childPath parent.1) : CarrierExtends childPath node.1 := by
  have hneNode : node.1 ≠ .real focus := ne_focus_of_armChild hchild
  have hraw : rawNewParent focus node.1 = some parent.1 := hchild
  cases node with
  | mk val hval =>
      cases val with
      | ring path atomR =>
          have hringNe : CarrierNode.ring path atomR ≠ CarrierNode.real focus := by
            intro h; cases h
          rw [rawNewParent, if_neg hringNe] at hraw
          injection hraw with hparent
          have hprefix : childPath <+: path := by
            have : CarrierExtends childPath parent.1 := hext
            rw [← hparent] at this
            simpa [CarrierExtends] using this
          simpa [CarrierExtends] using hprefix
      | real path =>
          unfold rawNewParent at hraw
          rw [if_neg hneNode] at hraw
          by_cases hpre : path.length < focus.length ∧ focus.take path.length = path
          · simp [hpre] at hraw
            have hprefix : childPath <+: path ++ [focus[path.length]'(hpre.1)] := by
              have : CarrierExtends childPath parent.1 := hext
              rw [← hraw] at this
              simpa [CarrierExtends] using this
            have hlen := length_le_of_isPrefix hprefix
            simp [hshape] at hlen
            have hlt : path.length < focus.length := hpre.1
            omega
          · simp [hpre] at hraw
            have hprefix : childPath <+: path.dropLast := by
              have : CarrierExtends childPath parent.1 := hext
              rw [← hraw] at this
              simpa [CarrierExtends] using this
            rw [carrierExtends_iff]
            exact hprefix.trans (dropLast_isPrefix (SimpleFrom.ne_nil hval))

private theorem parent_extends_extension {molecule : MoleculeGraph Atom} {root : Atom}
    {focus childPath : List Atom} {atom : Atom}
    (hshape : childPath = focus ++ [atom]) {node : Nodes molecule root}
    (hext : CarrierExtends childPath node.1) (hne : node.1 ≠ .real childPath)
    {parentVal : CarrierNode Atom}
    (hraw : rawNewParent focus node.1 = some parentVal) : CarrierExtends childPath parentVal := by
  cases node with
  | mk val hval =>
      cases val with
      | ring path atomR =>
          have hringNe : CarrierNode.ring path atomR ≠ CarrierNode.real focus := by
            intro h; cases h
          rw [rawNewParent, if_neg hringNe] at hraw
          injection hraw with hparent
          rw [← hparent]
          simpa [CarrierExtends] using hext
      | real path =>
          have hneFocus : CarrierNode.real path ≠ CarrierNode.real focus := by
            intro heq
            have : childPath <+: focus := by
              have hpath : path = focus := by injection heq
              have hextPath : childPath <+: path := by simpa [CarrierExtends] using hext
              simpa [hpath] using hextPath
            have hlen := length_le_of_isPrefix this
            simp [hshape] at hlen
          unfold rawNewParent at hraw
          rw [if_neg hneFocus] at hraw
          by_cases hpre : path.length < focus.length ∧ focus.take path.length = path
          · simp [hpre] at hraw
            have hprefix : childPath <+: path := by simpa [CarrierExtends] using hext
            have hlen := length_le_of_isPrefix hprefix
            simp [hshape] at hlen
            have hlt : path.length < focus.length := hpre.1
            omega
          · simp [hpre] at hraw
            have hpathNe : path ≠ childPath := by
              intro heq
              exact hne (by simp [heq])
            have hprefix : childPath <+: path := by simpa [CarrierExtends] using hext
            have hstem : childPath <+: path.dropLast := by
              have hsplit : path = path.dropLast ++ [path.getLast (SimpleFrom.ne_nil hval)] :=
                (List.dropLast_concat_getLast (SimpleFrom.ne_nil hval)).symm
              rw [hsplit] at hprefix
              have hneConcat : childPath ≠ path.dropLast ++ [path.getLast (SimpleFrom.ne_nil hval)] := by
                rw [← hsplit]
                exact hpathNe.symm
              exact prefix_ne_concat hprefix hneConcat
            rw [← hraw]
            simpa [CarrierExtends] using hstem

/-- The subtree of one outward child is the cone of that child path. -/
theorem inArmSubtree_extension_iff {molecule : MoleculeGraph Atom} {root : Atom}
    {focus childPath : List Atom} {atom : Atom}
    (hfocus : SimpleFrom molecule root focus)
    (hshape : childPath = focus ++ [atom])
    (hchildPath : SimpleFrom molecule root childPath)
    (node : Nodes molecule root) :
    InArmSubtree focus ⟨.real childPath, hchildPath⟩ node ↔
      CarrierExtends childPath node.1 := by
  let childNode : Nodes molecule root := ⟨.real childPath, hchildPath⟩
  constructor
  · intro hsub
    induction hsub with
    | refl =>
        simpa [CarrierExtends] using (List.prefix_refl childPath)
    | @tail prev step _ hstep ih =>
        exact extends_of_extension_step hshape hstep ih
  · intro hext
    suffices ∀ d, ∀ node : Nodes molecule root, armDepth focus node.1 = d →
        CarrierExtends childPath node.1 → InArmSubtree focus childNode node by
      exact this (armDepth focus node.1) node rfl hext
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih node hd hext
    by_cases hchildEq : node.1 = .real childPath
    · have : node = childNode := Subtype.ext hchildEq
      subst this
      exact Relation.ReflTransGen.refl
    · have hneFocus : node.1 ≠ .real focus := by
        intro heq
        have : childPath <+: focus := by simpa [CarrierExtends, heq] using hext
        have hlen := length_le_of_isPrefix this
        simp [hshape] at hlen
      obtain ⟨parentVal, hraw, hvalid, hdepth⟩ := rawNewParent_spec hfocus node.2 hneFocus
      let parent : Nodes molecule root := ⟨parentVal, hvalid⟩
      have hchildRel : armChild focus parent node := hraw
      have hextParent : CarrierExtends childPath parent.1 :=
        parent_extends_extension hshape hext hchildEq hraw
      have hlt : armDepth focus parentVal < d := by
        have hdepth' : armDepth focus node.1 = armDepth focus parentVal + 1 := hdepth
        rw [hd] at hdepth'
        omega
      have hparentDepth : armDepth focus parent.1 = armDepth focus parentVal := by
        rfl
      exact (ih _ (hparentDepth ▸ hlt) parent rfl hextParent).tail hchildRel

theorem kept_predecessor_iff {molecule : MoleculeGraph Atom} {root : Atom}
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (hlen : 1 < focus.length) (node : Nodes molecule root) :
    KeptAfterCut focus (some ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩) node ↔
      CarrierExtends focus node.1 := by
  constructor
  · intro hkept
    by_contra hnot
    exact hkept _ rfl ((inArmSubtree_predecessor_iff hfocus hlen node).2 hnot)
  · intro hext inc hsome hsub
    cases hsome
    exact ((inArmSubtree_predecessor_iff hfocus hlen node).1 hsub) hext

theorem kept_extension_iff {molecule : MoleculeGraph Atom} {root : Atom}
    {focus childPath : List Atom} {atom : Atom}
    (hfocus : SimpleFrom molecule root focus)
    (hshape : childPath = focus ++ [atom])
    (hchildPath : SimpleFrom molecule root childPath)
    (node : Nodes molecule root) :
    KeptAfterCut focus (some ⟨.real childPath, hchildPath⟩) node ↔
      ¬ CarrierExtends childPath node.1 := by
  constructor
  · intro hkept hext
    exact hkept _ rfl ((inArmSubtree_extension_iff hfocus hshape hchildPath node).2 hext)
  · intro hnot inc hsome hsub
    cases hsome
    exact hnot ((inArmSubtree_extension_iff hfocus hshape hchildPath node).1 hsub)

theorem natCard_predecessor_cut {molecule : MoleculeGraph Atom} {root : Atom}
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (hlen : 1 < focus.length) :
    Nat.card (realCutRetainedArm molecule root hfocus
        (some ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩)
        (someAnchor hfocus ((armChild_focus_iff hfocus _).2 (Or.inr ⟨hlen, rfl⟩)))).Node =
      Nat.card (Extending molecule root focus) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun node => ?_)
  simpa using kept_predecessor_iff hfocus hlen node

theorem natCard_extension_cut {molecule : MoleculeGraph Atom} {root : Atom}
    {focus childPath : List Atom} {atom : Atom}
    (hfocus : SimpleFrom molecule root focus)
    (hshape : childPath = focus ++ [atom])
    (hchildPath : SimpleFrom molecule root childPath) :
    Nat.card (realCutRetainedArm molecule root hfocus
        (some ⟨.real childPath, hchildPath⟩)
        (someAnchor hfocus ((armChild_focus_iff hfocus _).2
          (Or.inl ⟨atom, hshape⟩)))).Node =
      Nat.card (Avoiding molecule root childPath) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun node => ?_)
  simpa using kept_extension_iff hfocus hshape hchildPath node

end Cones

/-! ## Rule 1a entry count is the source-node count -/

def sparseEntryCount {α : Type*} : List (List α) → Nat
  | [] => 0
  | layer :: layers => layer.length + sparseEntryCount layers

private theorem sparseEntryCount_eq_map_sum {α : Type*} (layers : List (List α)) :
    sparseEntryCount layers = (layers.map List.length).sum := by
  induction layers with
  | nil => rfl
  | cons layer layers ih =>
      simp [sparseEntryCount, ih]

private theorem sum_getD_length {α : Type*} (layers : List (List α)) (count : Nat)
    (h : layers.length ≤ count) :
    ((List.range count).map fun d => (layers.getD d []).length).sum =
      sparseEntryCount layers := by
  rw [sparseEntryCount_eq_map_sum]
  induction layers generalizing count with
  | nil =>
      simpa using (sum_map_const_zero count).symm
  | cons layer rest ih =>
      cases count with
      | zero =>
          simp at h
      | succ count =>
          have hrest : rest.length ≤ count := by
            simp at h
            exact h
          rw [range_succ_eq_cons_map, List.map_cons, List.sum_cons]
          have hzero : ((layer :: rest).getD 0 []).length = layer.length := by
            simp
          rw [hzero]
          have hsucc :
              ((List.range count).map Nat.succ).map
                  (fun d => ((layer :: rest).getD d []).length) =
                (List.range count).map fun d => (rest.getD d []).length := by
            rw [List.map_map]
            apply List.map_congr_left
            intro d _
            simp
          rw [hsucc, ih count hrest]
          rfl

private theorem mergePairs_length {β α : Type*} (pairs : List (β × Nat))
    (block : β → List (OfficialSparseEntry α)) :
    (mergePairs pairs block).length =
      (pairs.map fun p => (block p.1).length).sum := by
  induction pairs with
  | nil => simp [mergePairs]
  | cons p ps ih =>
      unfold mergePairs
      rw [List.flatMap_cons, List.length_append]
      have htail :
          (List.flatMap (fun pair => OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1)) ps).length =
            (ps.map fun q => (block q.1).length).sum := by
        simpa [mergePairs] using ih
      rw [htail]
      simp [OfficialRuleMajorKey.prefixLayer, List.length_map, List.map_cons, List.sum_cons]

private theorem sum_map_add {α : Type*} (l : List α) (f g : α → Nat) :
    ((l.map fun a => f a + g a).sum) = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [ih, Nat.add_assoc, Nat.add_left_comm]

private theorem sparseEntryCount_mergePairTable {β α : Type*}
    (pairs : List (β × Nat))
    (layers : β → List (List (OfficialSparseEntry α))) (count : Nat)
    (hle : ∀ p ∈ pairs, (layers p.1).length ≤ count) :
    sparseEntryCount (mergePairTable pairs layers count) =
      (pairs.map fun p => sparseEntryCount (layers p.1)).sum := by
  rw [mergePairTable, sparseEntryCount_eq_map_sum]
  induction pairs with
  | nil =>
      simp [mergePairs]
  | cons p ps ih =>
      have hhead : (layers p.1).length ≤ count := hle p (by simp)
      have htail : ∀ q ∈ ps, (layers q.1).length ≤ count :=
        fun q hq => hle q (List.mem_cons_of_mem p hq)
      rw [List.map_cons, List.sum_cons]
      have hlen :
          ((List.range count).map fun d =>
              (mergePairs (p :: ps) (fun value => (layers value).getD d [])).length).sum =
            ((List.range count).map fun d => ((layers p.1).getD d []).length).sum +
              ((List.range count).map fun d =>
                (mergePairs ps (fun value => (layers value).getD d [])).length).sum := by
        have hpoint :
            (List.range count).map (fun d =>
                (mergePairs (p :: ps) (fun value => (layers value).getD d [])).length) =
              (List.range count).map fun d =>
                ((layers p.1).getD d []).length +
                  (mergePairs ps (fun value => (layers value).getD d [])).length := by
          apply List.map_congr_left
          intro d _
          have htail := mergePairs_length ps (fun value => (layers value).getD d [])
          rw [mergePairs, List.flatMap_cons, List.length_append]
          simp [OfficialRuleMajorKey.prefixLayer, List.length_map, mergePairs, htail]
        rw [hpoint, sum_map_add (List.range count)
          (fun d => ((layers p.1).getD d []).length)
          (fun d => (mergePairs ps (fun value => (layers value).getD d [])).length)]
      have hshape :
          (List.map List.length
              (List.map (fun depth =>
                  mergePairs (p :: ps) (fun value => (layers value).getD depth []))
                (List.range count))).sum =
            ((List.range count).map fun d =>
                (mergePairs (p :: ps) (fun value => (layers value).getD d [])).length).sum := by
        simp only [List.map_map]
        rfl
      rw [hshape, hlen, sum_getD_length _ _ hhead]
      have htailCount := ih htail
      unfold mergePairTable at htailCount
      have htailShape :
          ((List.range count).map fun d =>
              (mergePairs ps (fun value => (layers value).getD d [])).length).sum =
            (List.map List.length
                (List.map (fun depth =>
                    mergePairs ps (fun value => (layers value).getD depth []))
                  (List.range count))).sum := by
        simp only [List.map_map]
        rfl
      rw [htailShape, htailCount]

private theorem fst_mem_zipIdx {α : Type*} :
    ∀ (l : List α) (start : Nat) (p : α × Nat), p ∈ l.zipIdx start → p.1 ∈ l
  | [], _, _, h => by simp at h
  | a :: l, start, p, h => by
      rw [List.zipIdx_cons] at h
      simp at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (fst_mem_zipIdx l (start + 1) p h)

private theorem foldl_max_ge_init {β : Type*} (f : β → Nat) :
    ∀ (l : List β) (acc : Nat), acc ≤ l.foldl (fun m x => max m (f x)) acc
  | [], _ => le_rfl
  | b :: l, acc => by
      rw [List.foldl_cons]
      exact le_trans (le_max_left _ _) (foldl_max_ge_init f l _)

private theorem foldl_max_of_mem {β : Type*} (f : β → Nat) :
    ∀ (l : List β) (acc : Nat) (b : β), b ∈ l → f b ≤ l.foldl (fun m x => max m (f x)) acc
  | [], _, _, h => by cases h
  | head :: tail, acc, b, h => by
      rw [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | htail
      · exact le_trans (le_max_right _ _) (foldl_max_ge_init f tail _)
      · exact foldl_max_of_mem f tail _ b htail

private theorem length_le_childLayerCount {α : Type*}
    (tables : List (List (List (OfficialSparseEntry α))))
    (table : List (List (OfficialSparseEntry α))) (h : table ∈ tables) :
    table.length ≤ localizedTreeChildLayerCount tables := by
  unfold localizedTreeChildLayerCount
  simpa using foldl_max_of_mem (fun table => table.length) tables 0 table h

private theorem zipIdx_entryCount_sum {α : Type*} :
    ∀ (tables : List (List (List α))) (start : Nat),
      (tables.zipIdx start).map (fun p => sparseEntryCount p.1) =
        tables.map sparseEntryCount
  | [], _ => by simp
  | table :: tables, start => by
      rw [List.zipIdx_cons]
      simp [zipIdx_entryCount_sum tables (start + 1)]

mutual
def sourceNodeCount {V : Type*} : OfficialCIPSourceTree V → Nat
  | .node _ kids => 1 + sourceForestCount kids

def sourceForestCount {V : Type*} : List (OfficialCIPSourceTree V) → Nat
  | [] => 0
  | tree :: trees => sourceNodeCount tree + sourceForestCount trees
end

mutual
private theorem occurrences_length_eq {V : Type*} :
    ∀ tree : OfficialCIPSourceTree V, tree.occurrences.length = sourceNodeCount tree
  | .node _ subtrees => by
      rw [occurrences, sourceNodeCount, List.length_cons, forest_length_eq subtrees 0]
      omega

private theorem forest_length_eq {V : Type*} :
    ∀ (trees : List (OfficialCIPSourceTree V)) (start : Nat),
      (forestOccurrences trees start).length = sourceForestCount trees
  | [], _ => by
      rw [forestOccurrences, sourceForestCount]
      simp
  | tree :: trees, start => by
      rw [forestOccurrences, sourceForestCount, List.length_append, List.length_map,
        occurrences_length_eq tree, forest_length_eq trees (start + 1)]
end

private theorem nil_mem_occurrences {V : Type*} (tree : OfficialCIPSourceTree V) :
    ([], tree.source) ∈ tree.occurrences := by
  cases tree with
  | node sourceNode subtrees =>
      rw [occurrences]
      simp [OfficialCIPSourceTree.source]

private theorem cons_prefix_dest {α : Type*} {a : α} {l m : List α}
    (h : a :: l <+: m) : ∃ rest, m = a :: rest ∧ l <+: rest := by
  cases m with
  | nil =>
      obtain ⟨t, ht⟩ := h
      simp at ht
  | cons b rest =>
      obtain ⟨t, ht⟩ := h
      simp at ht
      exact ⟨rest, by simp [ht.1], ⟨t, ht.2⟩⟩

private theorem prefix_mem_occurrences {V : Type*} (tree : OfficialCIPSourceTree V)
    {address full : List ℕ} {node : OfficialCIPNode V}
    (hpre : address <+: full) (hmem : (full, node) ∈ tree.occurrences) :
    ∃ node', (address, node') ∈ tree.occurrences := by
  suffices ∀ n, ∀ (tree : OfficialCIPSourceTree V) {address full : List ℕ}
      {node : OfficialCIPNode V}, address.length = n → address <+: full →
        (full, node) ∈ tree.occurrences → ∃ node', (address, node') ∈ tree.occurrences by
    exact this address.length tree rfl hpre hmem
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih tree address full node hlen hpre hmem
  cases address with
  | nil =>
      exact ⟨tree.source, nil_mem_occurrences tree⟩
  | cons slot rest =>
      cases tree with
      | node sourceNode subtrees =>
          obtain ⟨fullTail, hfull, hrest⟩ := cons_prefix_dest hpre
          rw [occurrences] at hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with hroot | hforest
          · have := congrArg Prod.fst hroot
            simp [hfull] at this
          · rw [mem_forestOccurrences_iff_zipIdx] at hforest
            rcases hforest with ⟨indexed, hpresent, sourceEntry, hsource, hentry⟩
            have hfst : full = indexed.2 :: sourceEntry.1 := congrArg Prod.fst hentry
            rw [hfull] at hfst
            injection hfst with hslot htail
            have hshorter : rest.length < n := by
              rw [← hlen]
              simp
            have hrestEntry : rest <+: sourceEntry.1 := by
              simpa [htail] using hrest
            obtain ⟨node', hnode'⟩ :=
              ih rest.length hshorter indexed.1 (address := rest) (full := sourceEntry.1)
                (node := sourceEntry.2) rfl hrestEntry hsource
            refine ⟨node', ?_⟩
            rw [occurrences]
            simp only [List.mem_cons]
            refine Or.inr ?_
            rw [mem_forestOccurrences_iff_zipIdx]
            exact ⟨(indexed.1, slot), by simpa [hslot] using hpresent, (rest, node'), hnode', rfl⟩

mutual
private theorem occurrences_fst_nodup {V : Type*} :
    ∀ tree : OfficialCIPSourceTree V, (tree.occurrences.map Prod.fst).Nodup
  | .node _ subtrees => by
      rw [occurrences]
      simp only [List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, forest_fst_nodup subtrees 0⟩
      intro hmem
      obtain ⟨slot, rest, _, heq⟩ := forest_address_is_cons subtrees 0 _ hmem
      simp at heq

private theorem forest_fst_nodup {V : Type*} :
    ∀ (trees : List (OfficialCIPSourceTree V)) (start : Nat),
      ((forestOccurrences trees start).map Prod.fst).Nodup
  | [], _ => by
      rw [forestOccurrences]
      simp
  | tree :: trees, start => by
      rw [forestOccurrences]
      simp only [List.map_append, List.map_map]
      rw [List.nodup_append]
      refine ⟨?_, forest_fst_nodup trees (start + 1), ?_⟩
      · have hnodup := occurrences_fst_nodup tree
        have hmap :
            ((tree.occurrences.map Prod.fst).map fun addr => start :: addr) =
              (tree.occurrences.map fun entry => (start :: entry.1, entry.2)).map Prod.fst := by
          simp [List.map_map, Function.comp]
        simp only [← List.map_map]
        rw [← hmap]
        exact List.Nodup.map (fun a b hab => (List.cons.inj hab).2) hnodup
      · intro left leftMem right rightMem heq
        obtain ⟨rest, hleft⟩ := forest_head_slot tree start left leftMem
        obtain ⟨slot, restR, hge, hright⟩ :=
          forest_address_is_cons trees (start + 1) right rightMem
        rw [hleft, hright] at heq
        simp at heq
        omega

private theorem forest_address_is_cons {V : Type*} :
    ∀ (trees : List (OfficialCIPSourceTree V)) (start : Nat) (addr : List ℕ),
      addr ∈ (forestOccurrences trees start).map Prod.fst →
        ∃ slot rest, start ≤ slot ∧ addr = slot :: rest
  | [], _, _, h => by
      simp [forestOccurrences] at h
  | tree :: trees, start, addr, h => by
      rw [forestOccurrences] at h
      simp only [List.map_append, List.map_map, List.mem_append] at h
      rcases h with hleft | hright
      · obtain ⟨rest, hleft⟩ := forest_head_slot tree start addr hleft
        exact ⟨start, rest, le_rfl, hleft⟩
      · obtain ⟨slot, rest, hge, heq⟩ :=
          forest_address_is_cons trees (start + 1) addr hright
        exact ⟨slot, rest, Nat.le_trans (Nat.le_succ start) hge, heq⟩

private theorem forest_head_slot {V : Type*} (tree : OfficialCIPSourceTree V)
    (start : Nat) (addr : List ℕ)
    (h : addr ∈ (tree.occurrences.map fun entry => start :: entry.1)) :
    ∃ rest, addr = start :: rest := by
  simp only [List.mem_map] at h
  obtain ⟨entry, _, rfl⟩ := h
  exact ⟨entry.1, rfl⟩
end

private theorem mem_hierarchy_iff_mem_occurrences {V : Type*}
    (tree : OfficialCIPSourceTree V) (address : List ℕ) :
    address ∈ tree.hierarchyAddresses ↔ address ∈ tree.occurrences.map Prod.fst := by
  constructor
  · intro hmem
    simp only [hierarchyAddresses, List.mem_cons, List.mem_flatMap] at hmem
    rcases hmem with rfl | ⟨entry, hentry, hprefix⟩
    · exact List.mem_map.mpr ⟨([], tree.source), nil_mem_occurrences tree, rfl⟩
    · rw [List.mem_inits] at hprefix
      obtain ⟨node', hnode'⟩ := prefix_mem_occurrences tree hprefix hentry
      exact List.mem_map.mpr ⟨(address, node'), hnode', rfl⟩
  · intro hmem
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
    rw [hierarchyAddresses]
    refine List.mem_cons_of_mem _ ?_
    exact List.mem_flatMap.mpr ⟨entry, hentry,
      (List.mem_inits entry.1 entry.1).mpr (List.prefix_refl entry.1)⟩

private theorem natCard_mem_nodup {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) :
    Nat.card {a // a ∈ l} = l.length := by
  have hequiv : {a // a ∈ l} ≃ {a // a ∈ l.toFinset} :=
    Equiv.subtypeEquivRight fun a => (List.mem_toFinset (l := l) (a := a)).symm
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hl]

private theorem natCard_hierarchyNode {V : Type*} (tree : OfficialCIPSourceTree V) :
    Nat.card tree.HierarchyNode = tree.occurrences.length := by
  have hequiv : tree.HierarchyNode ≃ {a // a ∈ tree.occurrences.map Prod.fst} :=
    Equiv.subtypeEquivRight fun address => mem_hierarchy_iff_mem_occurrences tree address
  rw [Nat.card_congr hequiv, natCard_mem_nodup _ (occurrences_fst_nodup tree), List.length_map]

private theorem natCard_toDeclarativeDigraph {V : Type} [DecidableEq V]
    (tree : OfficialCIPSourceTree V) :
    Nat.card tree.toDeclarativeDigraph.Node = sourceNodeCount tree := by
  have hcard : Nat.card tree.HierarchyNode = sourceNodeCount tree := by
    rw [natCard_hierarchyNode, occurrences_length_eq]
  simpa [toDeclarativeDigraph] using hcard

mutual
def nodeCount {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    LocalizedCumulativeDecoratedTree input carrierFuel → Nat
  | ⟨_, _, _, _, _, kids⟩ => 1 + nodeCountList kids
termination_by tree => sizeOf tree
decreasing_by
  simp_wf

def nodeCountList {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    List (LocalizedCumulativeDecoratedTree input carrierFuel) → Nat
  | [] => 0
  | child :: kids => nodeCount child + nodeCountList kids
termination_by children => sizeOf children
decreasing_by
  all_goals (simp_wf <;> omega)
end

private theorem nodeCount_mk {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (source : input.LocalizedRerootCursor carrierFuel)
    (atomicNumber rule1bDistance isotopeMass : Nat)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    nodeCount ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =
      1 + nodeCountList children := by
  rw [nodeCount]

private theorem nodeCountList_nil {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    nodeCountList ([] : List (LocalizedCumulativeDecoratedTree input carrierFuel)) = 0 := by
  rw [nodeCountList]

private theorem nodeCountList_cons {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (child : LocalizedCumulativeDecoratedTree input carrierFuel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    nodeCountList (child :: children) = nodeCount child + nodeCountList children := by
  rw [nodeCountList]

mutual
private theorem nodeCount_source {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
      nodeCount tree = sourceNodeCount (toOfficialSourceTree tree)
  | ⟨src, atomicNumber, rule1bDistance, isotopeMass, label, kids⟩ => by
      rw [nodeCount_mk, toOfficialSourceTree_mk, sourceNodeCount]
      exact congrArg (fun n => 1 + n) (nodeCountList_source kids)
termination_by tree => sizeOf tree
decreasing_by simp_wf

private theorem nodeCountList_source {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ children : List (LocalizedCumulativeDecoratedTree input carrierFuel),
      nodeCountList children = sourceForestCount (toOfficialSourceTreeList children)
  | [] => by
      rw [nodeCountList_nil, toOfficialSourceTreeList_nil, sourceForestCount]
  | child :: kids => by
      rw [nodeCountList_cons, toOfficialSourceTreeList_cons, sourceForestCount,
        nodeCount_source child, nodeCountList_source kids]
termination_by children => sizeOf children
decreasing_by
  all_goals (simp_wf <;> omega)
end

mutual
private theorem sparseEntryCount_table {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {α : Type*} (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) :
    ∀ tree, sparseEntryCount (table observe tree) = nodeCount tree
  | ⟨src, atomicNumber, rule1bDistance, isotopeMass, label, kids⟩ => by
      rw [table_eq_root_merge, nodeCount_mk]
      simp [sparseEntryCount]
      have hmerge := sparseEntryCount_tableList observe kids
      have hcount :
          sparseEntryCount (mergeLocalizedTreeChildTables (kids.map (table observe))) =
            nodeCountList kids := by
        rw [mergeLocalizedTreeChildTables, sparseEntryCount_mergePairTable]
        · have hzip := zipIdx_entryCount_sum (kids.map (table observe)) 0
          calc
            ((kids.map (table observe)).zipIdx.map fun p => sparseEntryCount (id p.1)).sum =
                ((kids.map (table observe)).zipIdx.map fun p => sparseEntryCount p.1).sum := by
              simp
            _ = ((kids.map (table observe)).map sparseEntryCount).sum := by
              rw [hzip]
            _ = (kids.map fun child => sparseEntryCount (table observe child)).sum := by
              simp [List.map_map]
              rfl
            _ = nodeCountList kids := hmerge
        · intro p hp
          have hmem : p.1 ∈ kids.map (table observe) := fst_mem_zipIdx _ _ p hp
          simpa using length_le_childLayerCount _ _ hmem
      simp [hcount]
termination_by tree => sizeOf tree
decreasing_by simp_wf

private theorem sparseEntryCount_tableList {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {α : Type*} (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) :
    ∀ children, (children.map fun child => sparseEntryCount (table observe child)).sum =
        nodeCountList children
  | [] => by
      rw [nodeCountList_nil]
      simp
  | child :: kids => by
      rw [nodeCountList_cons, List.map_cons, List.sum_cons, sparseEntryCount_table observe child,
        sparseEntryCount_tableList observe kids]
termination_by children => sizeOf children
decreasing_by
  all_goals (simp_wf <;> omega)
end

theorem rule1aEntryCount_eq_graphCard {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor fuel}
    (arm : input.RuleMajorContextArm fuel stage read cursor) :
    sparseEntryCount arm.key.constitutional.rule1a =
      Nat.card (ruleMajorTreeGraph arm.tree).Node := by
  have matched := LocalizedRuleMajorSortTrace.fullMatch_of_trace arm.trace
  have tableEq : (arm.tree.tables stage).rule1a = arm.key.constitutional.rule1a :=
    matched.tableMatch.1
  rw [← tableEq, tables_rule1a, sparseEntryCount_table, nodeCount_source,
    natCard_toDeclarativeDigraph]

private theorem natCard_ringTerminal {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    {molecule : MoleculeGraph Atom} {root : Atom} {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    Nat.card (ringTerminalArm molecule root h).Node = 1 := by
  letI : Fintype (ringTerminalArm molecule root h).Node :=
    (ringTerminalArm molecule root h).nodeFintype
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_eq_one_iff.mpr ?_
  refine ⟨(ringTerminalArm molecule root h).root, ?_⟩
  intro node
  cases node
  rfl

/-! ## Actual frames -/

private theorem executableChild_root_eq (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren target) :
    child.occurrence.1.root = target.occurrence.1.root := by
  have intended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames target := by
    rw [← input.executableLocalizedRerootChildren_map target]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended target
    child.occurrence.1 intended
  exact input.localizedRerootNeighborFrames_root_eq target.occurrence.1
    child.occurrence.1 neighbor

private theorem history_singleton_of_root_address (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (address : cursor.occurrence.1.address = [])
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    cursor.occurrence.1.node.history = [cursor.occurrence.1.root] := by
  have path := input.simpleOccurrencePath_of_carrier_real singleBonded cursor.occurrence real
  have hlen := input.simpleOccurrencePath_history_length path
  rw [address] at hlen
  have hlast := input.legitimateOccurrence_history_getLast
    (input.carrierOccurrence_legitimate singleBonded cursor.occurrence)
  cases hhist : cursor.occurrence.1.node.history with
  | nil => simp [hhist] at hlen
  | cons atom rest =>
      cases rest with
      | nil =>
          have hlast' := hlast
          simp [hhist] at hlast'
          simp [hhist, hlast']
      | cons _ _ =>
          simp [hhist] at hlen

theorem carrierPath_of_real_root_child (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor armCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    ∃ ligand : input.Atom,
      input.occurrenceCarrierNode singleBonded rootCursor.occurrence =
          .real [rootCursor.occurrence.1.root] ∧
        input.occurrenceCarrierNode singleBonded armCursor.occurrence =
          .real [rootCursor.occurrence.1.root, ligand] ∧
          SimpleFrom input.moleculeGraph rootCursor.occurrence.1.root
            [rootCursor.occurrence.1.root, ligand] ∧
            armCursor.occurrence.1.root = rootCursor.occurrence.1.root := by
  have rootReal :=
    input.retainedExecutableParent_realAtom singleBonded rootCursor armCursor armMem
  have hhist := history_singleton_of_root_address input singleBonded rootCursor rootAddress rootReal
  have rootCarrier : input.occurrenceCarrierNode singleBonded rootCursor.occurrence =
      .real [rootCursor.occurrence.1.root] := by
    rw [CertifiedLocalizedCIPInput.occurrenceCarrierNode, if_pos rootReal, hhist]
    simp
  obtain ⟨path, hpath, inc, hcursor, htarget, hchild⟩ :=
    input.realExecutableChild_incomingArmChild singleBonded rootCursor armCursor armMem armReal
  have hinc : inc.1 = .real [rootCursor.occurrence.1.root] := by
    rw [← htarget, rootCarrier]
  have hrootEq := executableChild_root_eq input rootCursor armCursor armMem
  rcases (armChild_focus_iff hpath inc).1 hchild with hout | ⟨_hlen, hin⟩
  · cases hval : inc.1 with
    | real ipath =>
        rw [hval] at hout
        obtain ⟨atom, hjoin⟩ := hout
        rw [hinc] at hval
        injection hval with hipath
        rw [← hipath] at hjoin
        have hlen : (1 : Nat) = path.length + 1 := by
          simpa using congrArg List.length hjoin
        have hpos : 0 < path.length :=
          List.length_pos_of_ne_nil (SimpleFrom.ne_nil hpath)
        omega
    | ring _ _ =>
        rw [hinc] at hval
        cases hval
  · have hdrop : path.dropLast = [rootCursor.occurrence.1.root] := by
      have hnode : inc.1 = .real path.dropLast := hin
      rw [hinc] at hnode
      injection hnode with hrev
      exact hrev.symm
    have hsplit : path =
        [rootCursor.occurrence.1.root, path.getLast (SimpleFrom.ne_nil hpath)] := by
      have hconcat := List.dropLast_concat_getLast (SimpleFrom.ne_nil hpath)
      rw [hdrop] at hconcat
      exact hconcat.symm
    have hsimple : SimpleFrom input.moleculeGraph rootCursor.occurrence.1.root
        [rootCursor.occurrence.1.root, path.getLast (SimpleFrom.ne_nil hpath)] := by
      rw [← hsplit, ← hrootEq]
      exact hpath
    refine ⟨path.getLast (SimpleFrom.ne_nil hpath), rootCarrier, ?_, hsimple, hrootEq⟩
    rw [hcursor]
    exact congrArg CarrierNode.real hsplit

private theorem real_carrier_path (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    input.occurrenceCarrierNode singleBonded cursor.occurrence =
      .real cursor.occurrence.1.node.history.reverse ∧
      SimpleFrom input.moleculeGraph cursor.occurrence.1.root
        cursor.occurrence.1.node.history.reverse := by
  have hcarrier : input.occurrenceCarrierNode singleBonded cursor.occurrence =
      .real cursor.occurrence.1.node.history.reverse := by
    rw [CertifiedLocalizedCIPInput.occurrenceCarrierNode, if_pos real]
  have hvalid := input.occurrenceCarrierNode_valid singleBonded cursor.occurrence
  refine ⟨hcarrier, ?_⟩
  simpa [hcarrier] using hvalid

private theorem graphCard_eq_cutCard {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    {molecule : MoleculeGraph Atom} {root : Atom}
    {focus : Nodes molecule root} {incoming : Option (Nodes molecule root)}
    {anchor : CutAnchor focus incoming} {graph : RootedDigraph Atom}
    (faithful : RetainedContextArmFaithful molecule root focus incoming anchor graph) :
    Nat.card graph.Node = Nat.card (cutRetainedArm molecule root focus incoming anchor).Node := by
  rcases faithful with ⟨iso⟩
  exact (Nat.card_congr iso.toEquiv).symm

private theorem entryCount_eq_incomingCut (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (carrierFuel input) → Option LocalizedAuxiliaryLabel}
    (target cursor : input.LocalizedRerootCursor (carrierFuel input))
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (arm : input.RuleMajorContextArm (carrierFuel input) stage read cursor) :
    ∃ (path : List input.Atom)
      (hpath : SimpleFrom input.moleculeGraph cursor.occurrence.1.root path)
      (inc : Nodes input.moleculeGraph cursor.occurrence.1.root),
      input.occurrenceCarrierNode singleBonded cursor.occurrence = .real path ∧
        input.occurrenceCarrierNode singleBonded target.occurrence = inc.1 ∧
          armChild path ⟨.real path, hpath⟩ inc ∧
            sparseEntryCount arm.key.constitutional.rule1a =
              Nat.card {node : Nodes input.moleculeGraph cursor.occurrence.1.root //
                KeptAfterCut path (some inc) node} := by
  obtain ⟨path, hpath, inc, hcursor, htarget, hchild⟩ :=
    input.realExecutableChild_incomingArmChild singleBonded target cursor childMem real
  obtain ⟨_previousEq, focus, incoming, anchor, focusEq, incomingEq, faithful⟩ :=
    input.executableChild_retainedContextArmFaithful_of_carrierFuel singleBonded
      target cursor childMem arm
  have hgraph := rule1aEntryCount_eq_graphCard arm
  have hcut := graphCard_eq_cutCard faithful
  have hfocus : focus = ⟨.real path, hpath⟩ := by
    apply Subtype.ext
    exact focusEq.trans hcursor
  have hincoming : incoming = inc := by
    apply Subtype.ext
    exact incomingEq.trans htarget
  subst hfocus
  subst hincoming
  refine ⟨path, hpath, incoming, hcursor, htarget, hchild, ?_⟩
  rw [hgraph, hcut, cutRetainedArm_real]
  rfl

private theorem carrierExtends_pair {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    {base : List Atom} {node : CarrierNode Atom}
    (hext : CarrierExtends base node) : base <+: pathOf node := by
  rw [carrierExtends_iff] at hext
  exact hext

/-- Two real root arms that tie at Rule 1a separate every actual parent cut from every
outward cut at Rule 1a. The tie is the earlier comparison's case premise. Stages and
readers may differ: the count gap does not use them. -/
theorem rootArmRule1aTie_rootward_rule1a_ne_outward (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {armStage armStage' parentStage outwardStage : LocalizedCumulativeRule45Stage}
    {armRead armRead' parentRead outwardRead :
      input.LocalizedRerootCursor (carrierFuel input) → Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorContextArm (carrierFuel input) armStage armRead armCursor)
    (arm' : input.RuleMajorContextArm (carrierFuel input) armStage' armRead' armCursor')
    (tie : compareSparseLayers compareNat arm.key.constitutional.rule1a
        arm'.key.constitutional.rule1a = Ordering.eq)
    (targetCursor : input.LocalizedRerootCursor (carrierFuel input))
    (targetReal : targetCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (targetOnArm : armCursor.occurrence.1.node.history.reverse <+:
      targetCursor.occurrence.1.node.history.reverse)
    (parentCursor : input.LocalizedRerootCursor (carrierFuel input))
    (parentMem : parentCursor ∈ input.executableLocalizedRerootChildren targetCursor)
    (parentAddress : parentCursor.occurrence.1.address =
      targetCursor.occurrence.1.address.dropLast)
    (parentArm : input.RuleMajorContextArm (carrierFuel input) parentStage parentRead
      parentCursor)
    (outwardCursor : input.LocalizedRerootCursor (carrierFuel input))
    (outwardMem : outwardCursor ∈ input.executableLocalizedRerootChildren targetCursor)
    (outwardDistinct : outwardCursor.occurrence ≠ parentCursor.occurrence)
    (outwardArm : input.RuleMajorContextArm (carrierFuel input) outwardStage outwardRead
      outwardCursor) :
    compareSparseLayers compareNat parentArm.key.constitutional.rule1a
      outwardArm.key.constitutional.rule1a ≠ Ordering.eq := by
  let molecule := input.moleculeGraph
  let r0 := rootCursor.occurrence.1.root
  obtain ⟨ligand, rootCarrier, armCarrier, armSimple, armRoot⟩ :=
    carrierPath_of_real_root_child input singleBonded rootCursor armCursor rootAddress
      armMem armReal
  obtain ⟨ligand', _rootCarrier', armCarrier', armSimple', armRoot'⟩ :=
    carrierPath_of_real_root_child input singleBonded rootCursor armCursor' rootAddress
      armMem' armReal'
  have hligand : ligand ≠ ligand' := by
    intro heq
    apply armDistinct
    apply Subtype.ext
    exact input.occurrenceFrame_eq_of_carrierNode singleBonded
      (armRoot.trans armRoot'.symm)
      (by rw [armCarrier, armCarrier', heq])
  have ⟨targetCarrier, targetSimple⟩ :=
    real_carrier_path input singleBonded targetCursor targetReal
  have harmPath : armCursor.occurrence.1.node.history.reverse = [r0, ligand] := by
    have hcarrier := (real_carrier_path input singleBonded armCursor armReal).1
    have hjoin := hcarrier.symm.trans armCarrier
    injection hjoin
  have harm'Path : armCursor'.occurrence.1.node.history.reverse = [r0, ligand'] := by
    have hcarrier := (real_carrier_path input singleBonded armCursor' armReal').1
    have hjoin := hcarrier.symm.trans armCarrier'
    injection hjoin
  have htargetRoot : targetCursor.occurrence.1.root = r0 := by
    have hpre : [r0, ligand] <+: targetCursor.occurrence.1.node.history.reverse := by
      rw [← harmPath]
      exact targetOnArm
    have hheads := head?_eq_of_isPrefix hpre (by simp)
    rw [SimpleFrom.head?_eq targetSimple] at hheads
    simp at hheads
    exact hheads.symm
  have hdown : [r0, ligand] <+: targetCursor.occurrence.1.node.history.reverse := by
    rw [← harmPath]
    exact targetOnArm
  have htargetNonroot : targetCursor.occurrence.1.address ≠ [] := by
    have hlen := input.simpleOccurrencePath_history_length
      (input.simpleOccurrencePath_of_carrier_real singleBonded targetCursor.occurrence targetReal)
    have hge : 2 ≤ targetCursor.occurrence.1.node.history.reverse.length :=
      le_trans (by simp : 2 ≤ ([r0, ligand] : List input.Atom).length)
        (length_le_of_isPrefix hdown)
    have hhist : 2 ≤ targetCursor.occurrence.1.node.history.length := by
      rw [← List.length_reverse]
      exact hge
    have hpos : 0 < targetCursor.occurrence.1.address.length := by
      omega
    exact List.ne_nil_of_length_pos hpos
  obtain ⟨certificate⟩ :=
    input.exists_localizedParentFrameHistory targetCursor.occurrence htargetNonroot
  have hparentRoot := executableChild_root_eq input targetCursor parentCursor parentMem
  have hparentFrame : parentCursor.occurrence.1 = certificate.parent.1 :=
    input.declarativeLocalizedOccurrence_functional_at_root_address
      ((input.mem_localizedOccurrences_iff (carrierFuel input) parentCursor.occurrence.1).mp
        parentCursor.occurrence.2)
      ((input.mem_localizedOccurrences_iff (carrierFuel input) certificate.parent.1).mp
        certificate.parent.2)
      (hparentRoot.trans certificate.parent_root.symm)
      (parentAddress.trans certificate.parent_address.symm)
  have parentReal : parentCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [hparentFrame]
    exact LocalizedParentFrameHistory.parent_provenance input certificate
  have hparentPath : parentCursor.occurrence.1.node.history.reverse ++ [certificate.current] =
      targetCursor.occurrence.1.node.history.reverse := by
    have hrev := congrArg List.reverse certificate.history_eq
    rw [List.reverse_cons] at hrev
    have hsame : parentCursor.occurrence.1.node.history =
        certificate.parent.1.node.history := by
      rw [hparentFrame]
    rw [← hsame] at hrev
    exact hrev.symm
  obtain ⟨armPath, harmFocus, armInc, _armCursorCarrier, armIncoming, _armChild, armCount⟩ :=
    entryCount_eq_incomingCut input singleBonded rootCursor armCursor armMem armReal arm
  obtain ⟨armPath', harmFocus', armInc', _armCursorCarrier', armIncoming', _armChild',
      armCount'⟩ :=
    entryCount_eq_incomingCut input singleBonded rootCursor armCursor' armMem' armReal' arm'
  have harmPathEq : armPath = [r0, ligand] := by
    have hcarrier := (real_carrier_path input singleBonded armCursor armReal).1
    have hjoin := hcarrier.symm.trans _armCursorCarrier
    injection hjoin with hrev
    exact hrev.symm.trans harmPath
  have harm'PathEq : armPath' = [r0, ligand'] := by
    have hcarrier := (real_carrier_path input singleBonded armCursor' armReal').1
    have hjoin := hcarrier.symm.trans _armCursorCarrier'
    injection hjoin with hrev
    exact hrev.symm.trans harm'Path
  have harmDrop : armInc.1 = .real armPath.dropLast := by
    rw [← armIncoming, rootCarrier, harmPathEq]
    simp
    rfl
  have harm'Drop : armInc'.1 = .real armPath'.dropLast := by
    rw [← armIncoming', rootCarrier, harm'PathEq]
    simp
    rfl
  have harm'Len : 1 < armPath'.length := by
    rw [harm'PathEq]
    simp
  have harmLen : 1 < armPath.length := by
    rw [harmPathEq]
    simp
  have hlists : arm.key.constitutional.rule1a = arm'.key.constitutional.rule1a :=
    (compareSparseLayers_compareNat_eq_iff _ _).mp tie
  have htieCount : sparseEntryCount arm.key.constitutional.rule1a =
      sparseEntryCount arm'.key.constitutional.rule1a := by
    rw [hlists]
  -- The remainder joins the cone cardinalities. The rootward cut deletes the target
  -- cone; each outward cut is that cone or a one-node ring.
  obtain ⟨parentPath, hparentFocus, parentInc, hparentCarrier, hparentIncoming, hparentChild,
      parentCount⟩ :=
    entryCount_eq_incomingCut input singleBonded targetCursor parentCursor parentMem
      parentReal parentArm
  have hparentShape : parentPath ++ [certificate.current] =
      targetCursor.occurrence.1.node.history.reverse := by
    have hparentReal := (real_carrier_path input singleBonded parentCursor parentReal).1
    rw [hparentReal] at hparentCarrier
    injection hparentCarrier with hrev
    rw [← hrev]
    exact hparentPath
  have htargetNode : parentInc.1 =
      .real (parentPath ++ [certificate.current]) := by
    rw [← hparentIncoming, targetCarrier, ← hparentShape]
  rcases (armChild_focus_iff hparentFocus parentInc).1 hparentChild with hchild | ⟨_, hshort⟩
  · have hchildPath : parentPath ++ [certificate.current] =
        targetCursor.occurrence.1.node.history.reverse := hparentShape
    have hsimpleChild : SimpleFrom molecule parentCursor.occurrence.1.root
        (parentPath ++ [certificate.current]) := by
      rw [hparentRoot, hchildPath]
      exact targetSimple
    have hparentSimple : SimpleFrom molecule r0 parentPath := by
      have hvalid := input.occurrenceCarrierNode_valid singleBonded parentCursor.occurrence
      rw [hparentCarrier] at hvalid
      rw [hparentRoot, htargetRoot] at hvalid
      simpa using hvalid
    have hparentCountCone : sparseEntryCount parentArm.key.constitutional.rule1a =
        Nat.card (Avoiding molecule r0 (parentPath ++ [certificate.current])) := by
      have hincEq : parentInc =
          ⟨.real (parentPath ++ [certificate.current]), hsimpleChild⟩ :=
        Subtype.ext htargetNode
      rw [parentCount, hincEq]
      have hcard := natCard_extension_cut hparentFocus rfl hsimpleChild
      have htransport : Nat.card (Avoiding molecule parentCursor.occurrence.1.root
          (parentPath ++ [certificate.current])) =
          Nat.card (Avoiding molecule r0 (parentPath ++ [certificate.current])) := by
        rw [hparentRoot, htargetRoot]
      exact hcard.trans htransport
    have harmCone : sparseEntryCount arm.key.constitutional.rule1a =
        Nat.card (Extending molecule r0 [r0, ligand]) := by
      have hincEq : armInc =
          ⟨.real armPath.dropLast, SimpleFrom.dropLast harmFocus harmLen⟩ :=
        Subtype.ext harmDrop
      rw [armCount, hincEq]
      have hcard := natCard_predecessor_cut harmFocus harmLen
      have htransport : Nat.card (Extending molecule armCursor.occurrence.1.root armPath) =
          Nat.card (Extending molecule r0 [r0, ligand]) := by
        rw [armRoot, harmPathEq]
      exact hcard.trans htransport
    have harm'Cone : sparseEntryCount arm'.key.constitutional.rule1a =
        Nat.card (Extending molecule r0 [r0, ligand']) := by
      have hincEq : armInc' =
          ⟨.real armPath'.dropLast, SimpleFrom.dropLast harmFocus' harm'Len⟩ :=
        Subtype.ext harm'Drop
      rw [armCount', hincEq]
      have hcard := natCard_predecessor_cut harmFocus' harm'Len
      have htransport : Nat.card (Extending molecule armCursor'.occurrence.1.root armPath') =
          Nat.card (Extending molecule r0 [r0, ligand']) := by
        rw [armRoot', harm'PathEq]
      exact hcard.trans htransport
    have hrootward_gt : Nat.card (Extending molecule r0 [r0, ligand']) <
        Nat.card (Avoiding molecule r0 (parentPath ++ [certificate.current])) := by
      haveI := extending_finite molecule r0 [r0, ligand']
      haveI := avoiding_finite molecule r0 (parentPath ++ [certificate.current])
      let embed : Extending molecule r0 [r0, ligand'] →
          Avoiding molecule r0 (parentPath ++ [certificate.current]) := fun node =>
        ⟨node.1, by
          intro hext
          have harm' := carrierExtends_pair node.2
          have htargetPrefix : parentPath ++ [certificate.current] <+: pathOf node.1.1 :=
            carrierExtends_pair hext
          rw [hparentShape] at htargetPrefix
          exact hligand (pair_prefix_eq (hdown.trans htargetPrefix) harm')⟩
      have hinj : Function.Injective embed := by
        intro a b hab
        exact Subtype.ext (congrArg (fun node : Avoiding molecule r0
          (parentPath ++ [certificate.current]) => node.1) hab)
      let parentNode : Nodes molecule r0 := ⟨.real parentPath, hparentSimple⟩
      have hparentAvoid : ¬ CarrierExtends (parentPath ++ [certificate.current]) parentNode.1 := by
        intro hext
        apply not_extends_of_shorter (path := parentPath)
          (base := parentPath ++ [certificate.current])
        · simp [List.length_append]
        · have hpre := carrierExtends_pair hext
          simpa [parentNode, pathOf] using hpre
      have hparentNotArm' : ¬ CarrierExtends [r0, ligand'] parentNode.1 := by
        intro hext
        have hprefix : [r0, ligand'] <+: parentPath := carrierExtends_pair hext
        have hparentPrefix : parentPath <+:
            targetCursor.occurrence.1.node.history.reverse := by
          rw [← hparentShape]
          exact prefix_append_singleton _ _
        exact hligand (pair_prefix_eq hdown (hprefix.trans hparentPrefix))
      let miss : Avoiding molecule r0 (parentPath ++ [certificate.current]) :=
        ⟨parentNode, hparentAvoid⟩
      have hmiss : ∀ node, embed node ≠ miss := by
        intro node heq
        have hval : node.1.1 = parentNode.1 := by
          have := congrArg (fun item : Avoiding molecule r0
            (parentPath ++ [certificate.current]) => item.1.1) heq
          simpa [embed, miss] using this
        apply hparentNotArm'
        rw [← hval]
        exact node.2
      exact natCard_lt_of_injective_miss embed hinj miss hmiss
    have houtward_lt : sparseEntryCount outwardArm.key.constitutional.rule1a <
        sparseEntryCount arm.key.constitutional.rule1a := by
      rcases input.carrierOccurrence_provenance_simple_or_ring singleBonded
          outwardCursor.occurrence with outwardReal | ⟨distance, outwardRing⟩
      · obtain ⟨outPath, houtFocus, outInc, outCarrier, outIncoming, outChild, outCount⟩ :=
          entryCount_eq_incomingCut input singleBonded targetCursor outwardCursor outwardMem
            outwardReal outwardArm
        rcases (armChild_focus_iff houtFocus outInc).1 outChild with hchild | ⟨hlenOut, hlong⟩
        · have hchildCarrier : CarrierNode.Child (.real outPath) outInc.1 := hchild
          rw [← outIncoming, targetCarrier] at hchildCarrier
          obtain ⟨step, hjoin⟩ := hchildCarrier
          have hsamePath : parentCursor.occurrence.1.node.history.reverse = outPath := by
            have hboth : parentCursor.occurrence.1.node.history.reverse ++
                [certificate.current] = outPath ++ [step] := by
              rw [hparentPath, hjoin]
            have hdrop := congrArg List.dropLast hboth
            simpa [List.dropLast_concat] using hdrop
          have hsameCarrier : input.occurrenceCarrierNode singleBonded parentCursor.occurrence =
              input.occurrenceCarrierNode singleBonded outwardCursor.occurrence := by
            rw [(real_carrier_path input singleBonded parentCursor parentReal).1, outCarrier,
              hsamePath]
          exact False.elim (outwardDistinct (Subtype.ext
            (input.occurrenceFrame_eq_of_carrierNode singleBonded
              (hparentRoot.trans
                (executableChild_root_eq input targetCursor outwardCursor outwardMem).symm)
              hsameCarrier)).symm)
        · have htargetDrop : outPath.dropLast =
              targetCursor.occurrence.1.node.history.reverse := by
            have hinc : outInc.1 = .real outPath.dropLast := hlong
            rw [← outIncoming, targetCarrier] at hinc
            injection hinc with hrev
            exact hrev.symm
          have houtShape : outPath =
              targetCursor.occurrence.1.node.history.reverse ++ [outPath.getLast
                (SimpleFrom.ne_nil houtFocus)] := by
            have hsplit : outPath = outPath.dropLast ++ [outPath.getLast
                (SimpleFrom.ne_nil houtFocus)] :=
              (List.dropLast_concat_getLast (SimpleFrom.ne_nil houtFocus)).symm
            rw [htargetDrop] at hsplit
            exact hsplit
          have houtCountCone : sparseEntryCount outwardArm.key.constitutional.rule1a =
              Nat.card (Extending molecule r0 outPath) := by
            have hlenOut' : 1 < outPath.length := hlenOut
            have hincEq : outInc =
                ⟨.real outPath.dropLast, SimpleFrom.dropLast houtFocus hlenOut'⟩ :=
              Subtype.ext (by
                have hinc : outInc.1 = .real outPath.dropLast := hlong
                exact hinc)
            rw [outCount, hincEq]
            have hcard := natCard_predecessor_cut houtFocus hlenOut'
            have hrootCut : outwardCursor.occurrence.1.root = r0 :=
              (executableChild_root_eq input targetCursor outwardCursor outwardMem).trans
                htargetRoot
            have htransport : Nat.card (Extending molecule outwardCursor.occurrence.1.root
                outPath) = Nat.card (Extending molecule r0 outPath) := by
              rw [hrootCut]
            exact hcard.trans htransport
          have hltCone : Nat.card (Extending molecule r0 outPath) <
              Nat.card (Extending molecule r0 [r0, ligand]) := by
            haveI := extending_finite molecule r0 outPath
            haveI := extending_finite molecule r0 [r0, ligand]
            have houtExtends : [r0, ligand] <+: outPath := by
              rw [houtShape]
              exact hdown.trans (prefix_append_singleton _ _)
            let embed : Extending molecule r0 outPath → Extending molecule r0 [r0, ligand] :=
              fun node => ⟨node.1, extends_trans houtExtends node.2⟩
            have hinj : Function.Injective embed := by
              intro a b hab
              exact Subtype.ext (congrArg (fun node : Extending molecule r0 [r0, ligand] =>
                node.1) hab)
            let targetNode : Nodes molecule r0 :=
              ⟨.real targetCursor.occurrence.1.node.history.reverse, by
                rw [← htargetRoot]; exact targetSimple⟩
            have htargetExt : CarrierExtends [r0, ligand] targetNode.1 := by
              simpa [CarrierExtends] using hdown
            have htargetNot : ¬ CarrierExtends outPath targetNode.1 := by
              intro hext
              apply not_extends_of_shorter
                (path := targetCursor.occurrence.1.node.history.reverse) (base := outPath)
              · rw [houtShape]
                simp [List.length_append]
              · have hpre := carrierExtends_pair hext
                simpa [targetNode, pathOf] using hpre
            let miss : Extending molecule r0 [r0, ligand] := ⟨targetNode, htargetExt⟩
            have hmiss : ∀ node, embed node ≠ miss := by
              intro node heq
              apply htargetNot
              have hval : node.1.1 = targetNode.1 := by
                have := congrArg (fun item : Extending molecule r0 [r0, ligand] => item.1.1) heq
                simpa [embed, miss] using this
              rw [← hval]
              exact node.2
            exact natCard_lt_of_injective_miss embed hinj miss hmiss
          rw [houtCountCone, harmCone]
          exact hltCone
      · obtain ⟨_previousEq, ringPath, ringAtom, ringValid, hringCarrier, hringTarget,
            faithful⟩ :=
          input.ringExecutableChild_retainedContextArmFaithful singleBonded targetCursor
            outwardCursor outwardMem outwardArm outwardRing
        have hgraph := rule1aEntryCount_eq_graphCard outwardArm
        have hcut := graphCard_eq_cutCard faithful
        have hringCount : sparseEntryCount outwardArm.key.constitutional.rule1a = 1 := by
          rw [hgraph, hcut, cutRetainedArm_ringParent, natCard_ringTerminal]
        have hge : 2 ≤ Nat.card (Extending molecule r0 [r0, ligand]) := by
          haveI := extending_finite molecule r0 [r0, ligand]
          let realNode : Extending molecule r0 [r0, ligand] :=
            ⟨⟨.real targetCursor.occurrence.1.node.history.reverse, by
                rw [← htargetRoot]; exact targetSimple⟩,
              by simpa [CarrierExtends] using hdown⟩
          have hringRoot : outwardCursor.occurrence.1.root = r0 :=
            (executableChild_root_eq input targetCursor outwardCursor outwardMem).trans
              htargetRoot
          let ringNode : Extending molecule r0 [r0, ligand] :=
            ⟨⟨.ring ringPath ringAtom, by
                rw [← hringRoot]
                exact ringValid⟩, by
              have hpath : [r0, ligand] <+: ringPath := by
                have htarget : input.occurrenceCarrierNode singleBonded
                    targetCursor.occurrence = .real ringPath := hringTarget
                rw [targetCarrier] at htarget
                injection htarget with hrev
                rw [← hrev]
                exact hdown
              simpa [CarrierExtends] using hpath⟩
          have hne : (realNode : Extending molecule r0 [r0, ligand]) ≠ ringNode := by
            intro heq
            have := congrArg (fun node : Extending molecule r0 [r0, ligand] => node.1.1) heq
            simp [realNode, ringNode] at this
          exact natCard_ge_two realNode ringNode hne
        rw [hringCount, harmCone] at *
        omega
    intro hcmp
    have hcountEq : sparseEntryCount parentArm.key.constitutional.rule1a =
        sparseEntryCount outwardArm.key.constitutional.rule1a := by
      rw [(compareSparseLayers_compareNat_eq_iff _ _).mp hcmp]
    have hchain : sparseEntryCount outwardArm.key.constitutional.rule1a <
        sparseEntryCount parentArm.key.constitutional.rule1a := by
      calc
        sparseEntryCount outwardArm.key.constitutional.rule1a <
            sparseEntryCount arm.key.constitutional.rule1a := houtward_lt
        _ = sparseEntryCount arm'.key.constitutional.rule1a := htieCount
        _ = Nat.card (Extending molecule r0 [r0, ligand']) := harm'Cone
        _ < Nat.card (Avoiding molecule r0 (parentPath ++ [certificate.current])) :=
            hrootward_gt
        _ = sparseEntryCount parentArm.key.constitutional.rule1a := hparentCountCone.symm
    omega
  · exact False.elim (by
      have hshortPath : parentInc.1 = .real parentPath.dropLast := hshort
      rw [htargetNode] at hshortPath
      injection hshortPath with hlenPath
      have := congrArg List.length hlenPath
      simp at this
      omega)

end

end LocalizedRootwardConstitutionalSeparation
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedRootwardConstitutionalSeparation.rootArmRule1aTie_rootward_rule1a_ne_outward
assert_kernel_only TetraStereo.OneCenter.LocalizedRootwardConstitutionalSeparation.inArmSubtree_predecessor_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRootwardConstitutionalSeparation.inArmSubtree_extension_iff
