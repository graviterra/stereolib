import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey
import TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext
import TetraStereo.OneCenter.LocalizedRuleMajorObservedCanonicalBridge
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedActualOrderedRootIndependentPriority
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The actual promoted marker is the independent canonical marker

`LocalizedMarkedRetainedPromotedKey.build?` sorts actual reroot children by the full ordinary
compound key of the fixed original target and view, then by the recursively built marker.
`DeclarativeCIP.PromotedCanonical.markerKey` is the independent construction on a finite rooted
hierarchy: children are ordered by the complete key `(earlier key, marker)` with no runtime
comparator.

Take any decorated tree realized from any reader, its own rooted hierarchy, and any linearly
ordered independent earlier key `prior` on that hierarchy. Suppose only that, for every pair of
siblings, the actual ordinary comparison of their built ordinary keys is `compare` of `prior`
(`SiblingPriorAgreement`). Then every successful actual marker build at every node and every fuel
is exactly the independent canonical marker at that node, for every layout `W D`.

Thus marker agreement is reduced to a statement about the earlier rules alone. Ring-duplicate
leaves, tied siblings with equal markers, arbitrary depth and every reference atom are covered.
No successful sort, chosen order, desired marker or reference-selection result is assumed; the
remaining premise does not mention the marker. Parents with at most one child satisfy it for
every `prior`, using the derived reflexivity of the actual comparator.

This file proves operational agreement with an independent construction. It does not assert
that the experimental promotion policy is official CIP semantics.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker

open CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.PromotedCanonical Rule4aTableBridge
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedSubtreeContext
open LocalizedCumulativeDecoratedTree

/-! ## List helpers -/

private theorem mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
      List.Forall₂ (fun x y => f x = some y) xs ys
  | [], ys, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact .nil
  | x :: xs, ys, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at h
      obtain ⟨y, hy, rest, hrest, rfl⟩ := h
      exact .cons hy (mapM_forall₂ f xs rest hrest)

private theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, (∀ a ∈ l, ∀ b, R a b → S a b) →
      List.Forall₂ R l m → List.Forall₂ S l m
  | [], [], _, _ => .nil
  | a :: _, _ :: _, h, .cons hab rest =>
      .cons (h a (by simp) _ hab)
        (forall₂_imp_mem (fun x hx y hy => h x (by simp [hx]) y hy) rest)

private theorem exists_of_mem_forall₂_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ b ∈ m, ∃ a ∈ l, R a b
  | [], [], _, b, hb => by simp at hb
  | a :: _, _ :: _, .cons h rest, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨a, by simp, h⟩
      · obtain ⟨a', ha', h'⟩ := exists_of_mem_forall₂_right rest b hb
        exact ⟨a', by simp [ha'], h'⟩

private theorem map_eq_of_forall₂ {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ (fun a b => f a = g b) l m → l.map f = m.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h rest => by
      simp only [List.map_cons, h, map_eq_of_forall₂ rest]

/-! ## Marker comparison laws -/

private theorem natList_compare_lt_iff (left right : List Nat) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => compare_eq_iff_eq) left right

private theorem natList_compare_eq_iff (left right : List Nat) :
    compare left right = .eq ↔ left = right :=
  compareLex_eq_eq_iff_of compare (fun _ _ => compare_eq_iff_eq) left right

private theorem marker_compare_lt_iff (left right : MarkerKey) :
    compare left right = .lt ↔ left < right :=
  compareLex_eq_lt_iff_of compare natList_compare_lt_iff natList_compare_eq_iff left right

section Sorting

variable (input : CertifiedLocalizedCIPInput) {P : Type*} [LinearOrder P]

/-- With an independent prior order, the actual promoted test is the complete-key order. -/
theorem compareKeys_ne_lt_iff (x y : PromotedKey input) (p q : P)
    (prior : (input.compareLocalizedRerootCompoundThroughRule5 x.prior y.prior).ordering =
      compare p q) :
    compareKeys input x y ≠ .lt ↔ toLex (q, y.marker) ≤ toLex (p, x.marker) := by
  unfold compareKeys
  rw [prior, Ne, then_eq_lt_iff_lex compare compare (fun _ _ => compare_lt_iff_lt)
    (fun _ _ => compare_eq_iff_eq) marker_compare_lt_iff, not_lt]

/-- The actual stable insertion sort projects to the independent descending sort, whatever
order the actual tied keys take. -/
theorem sortKeys_marker_eq (keys : List (PromotedKey input))
    (φ : PromotedKey input → Lex (P × MarkerKey))
    (markerEq : ∀ x, (ofLex (φ x)).2 = x.marker)
    (order : ∀ x ∈ keys, ∀ y ∈ keys, compareKeys input x y ≠ .lt ↔ φ y ≤ φ x) :
    (sortKeys input keys).map PromotedKey.marker =
      (Certificate.CanonicalSphereKey.sortDesc (keys.map φ)).map
        fun complete => (ofLex complete).2 := by
  have mapped : (sortKeys input keys).map φ =
      Certificate.CanonicalSphereKey.sortDesc (keys.map φ) :=
    List.map_insertionSort (fun a b => compareKeys input a b ≠ .lt)
      Certificate.CanonicalSphereKey.Desc φ keys order
  rw [← mapped, List.map_map]
  exact List.map_congr_left fun x _ => (markerEq x).symm

end Sorting

/-! ## Realized trees -/

section Tree

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
  (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target)
  (reference : input.Atom) (W D : Nat)
  (tree : LocalizedCumulativeDecoratedTree input carrierFuel)

/-- The actual cursor at a node of the tree's own rooted hierarchy. -/
def nodeSource (node : (ruleMajorTreeGraph tree).Node) : input.LocalizedRerootCursor carrierFuel :=
  ((subtreeAt? tree node.1).map LocalizedCumulativeDecoratedTree.source).getD tree.source

theorem nodeSource_of_lookup {node : (ruleMajorTreeGraph tree).Node}
    {sub : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree node.1 = some sub) :
    nodeSource input tree node = sub.source := by
  simp [nodeSource, lookup]

theorem nodeSource_root : nodeSource input tree (ruleMajorTreeGraph tree).root = tree.source :=
  nodeSource_of_lookup input tree (node := (ruleMajorTreeGraph tree).root) (subtreeAt?_nil tree)

/-- The reference observation at every hierarchy node, read from its actual cursor. -/
def referenceMark (node : (ruleMajorTreeGraph tree).Node) : Nat :=
  referenceBit input reference (nodeSource input tree node)

/-- The only premise: the actual ordinary order of siblings is an independent linear order.
It mentions no marker, sort result, reference selection or descriptor. -/
def SiblingPriorAgreement {P : Type*} [LinearOrder P]
    (prior : (ruleMajorTreeGraph tree).Node → P) : Prop :=
  ∀ parent left right, (ruleMajorTreeGraph tree).child parent left →
    (ruleMajorTreeGraph tree).child parent right →
    ∀ leftKey rightKey,
      ordinaryKey? input target view (nodeSource input tree left) = some leftKey →
      ordinaryKey? input target view (nodeSource input tree right) = some rightKey →
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey).ordering =
        compare (prior left) (prior right)

theorem key_eq_marker {P : Type*} [LinearOrder P] (prior : (ruleMajorTreeGraph tree).Node → P)
    (mark : (ruleMajorTreeGraph tree).Node → Nat) (node : (ruleMajorTreeGraph tree).Node) :
    key (ruleMajorTreeGraph tree) prior mark W D node =
      toLex (prior node, markerKey (ruleMajorTreeGraph tree) prior mark W D node) := by
  rw [key_eq, markerKey_eq]

variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-- The node's children in slot order carry exactly the realized children's cursors. -/
theorem slot_children (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (node : (ruleMajorTreeGraph tree).Node)
    (sub : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? tree node.1 = some sub) :
    ∃ slots : List (ruleMajorTreeGraph tree).Node,
      slots.Perm ((ruleMajorTreeGraph tree).childList node) ∧
      (slots.map (nodeSource input tree)).Perm
        (input.executableLocalizedRerootChildren sub.source) := by
  have subRealizes := realizes_of_subtree realizes lookup
  have execPerm := (exists_sourcePerm_executable subRealizes).1
  have hdense := observedTree_denseAt_of_lookup tree node sub
    (by rw [decoratedSubtreeAt?_eq_subtreeAt?]; exact lookup)
  refine ⟨slotList (toOfficialSourceTree tree).declarativeAddressing node sub.children.length,
    slotList_perm hdense, ?_⟩
  have slotLength : (slotList (toOfficialSourceTree tree).declarativeAddressing node
      sub.children.length).length = sub.children.length := by simp [slotList]
  have sources : (slotList (toOfficialSourceTree tree).declarativeAddressing node
      sub.children.length).map (nodeSource input tree) =
        sub.children.map LocalizedCumulativeDecoratedTree.source := by
    apply List.ext_getElem (by simp [slotLength])
    intro i h₁ h₂
    have hi : i < sub.children.length := by simpa using h₂
    obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt
      (addressing := (toOfficialSourceTree tree).declarativeAddressing)
      (parent := node) (count := sub.children.length) hdense hi
    have addrFlat : child.1 = node.1 ++ [i] := by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address,
        (toOfficialSourceTree tree).declarativeAddressing_address] at addr
      exact addr
    have childLookup : subtreeAt? tree child.1 = some sub.children[i] := by
      rw [addrFlat, subtreeAt?_append, lookup]
      simp [subtreeAt?, List.getElem?_eq_getElem hi]
    have slotGet : (slotList (toOfficialSourceTree tree).declarativeAddressing node
        sub.children.length)[i]'(by rw [slotLength]; exact hi) = child :=
      Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotSome)
    rw [List.getElem_map, List.getElem_map, slotGet, nodeSource_of_lookup input tree childLookup]
  rw [sources]
  exact execPerm

/-- **Actual promoted marker = independent canonical marker.** At every node of a realized tree,
every successful actual build at any fuel returns the independent canonical marker of that node
for the independent prior, at every layout. The sibling agreement is the only premise. -/
theorem build?_marker_eq_markerKey (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {P : Type*} [LinearOrder P] (prior : (ruleMajorTreeGraph tree).Node → P)
    (agree : SiblingPriorAgreement input target view tree prior) :
    ∀ node fuel result,
      build? input target view reference W D fuel (nodeSource input tree node) = some result →
      result.marker = markerKey (ruleMajorTreeGraph tree) prior
        (referenceMark input reference tree) W D node := by
  refine node_induction (ruleMajorTreeGraph tree) ?_
  intro node ih fuel result built
  obtain ⟨sub, lookup⟩ := exists_local_subtree tree node
  have source := nodeSource_of_lookup input tree lookup
  obtain ⟨slots, slotsPerm, execPerm⟩ := slot_children input tree realizes node sub lookup
  have childOf : ∀ a ∈ slots, (ruleMajorTreeGraph tree).child node a := fun a member =>
    ((ruleMajorTreeGraph tree).mem_childList).1 (slotsPerm.subset member)
  rw [markerKey_eq]
  unfold rankedKeys
  rw [← Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
    (slotsPerm.map (key (ruleMajorTreeGraph tree) prior (referenceMark input reference tree) W D))]
  rw [source] at built
  cases fuel with
  | zero =>
      simp only [build?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        executableLocalizedRerootChildren?_eq_some, Option.some.injEq] at built
      obtain ⟨prior₀, _, children, childrenEq, rest⟩ := built
      split at rest
      · rename_i empty
        cases Option.some.inj rest
        subst childrenEq
        rw [empty] at execPerm
        have noSlots : slots = [] := List.map_eq_nil_iff.1 execPerm.eq_nil
        subst noSlots
        simp [referenceMark, source, Certificate.CanonicalSphereKey.sortDesc]
      · cases rest
  | succ fuel =>
      classical
      simp only [build?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        executableLocalizedRerootChildren?_eq_some, Option.some.injEq] at built
      obtain ⟨prior₀, _, children, childrenEq, keys, keysEq, same⟩ := built
      subst childrenEq
      subst same
      have related := mapM_forall₂ _ _ _ keysEq
      obtain ⟨keys₀, related₀, perm₀⟩ := List.perm_comp_forall₂ execPerm related
      have slotRelated : List.Forall₂ (fun a x =>
          build? input target view reference W D fuel (nodeSource input tree a) = some x)
          slots keys₀ := List.forall₂_map_left_iff.1 related₀
      let priorOf : PromotedKey input → P := fun x =>
        if h : ∃ a ∈ slots, build? input target view reference W D fuel
            (nodeSource input tree a) = some x then prior (Classical.choose h) else prior node
      have priorOf_eq : ∀ a ∈ slots, ∀ x,
          build? input target view reference W D fuel (nodeSource input tree a) = some x →
            priorOf x = prior a := by
        intro a member x builtA
        have present : ∃ a ∈ slots, build? input target view reference W D fuel
            (nodeSource input tree a) = some x := ⟨a, member, builtA⟩
        simp only [priorOf]
        rw [dif_pos present]
        obtain ⟨member', built'⟩ := Classical.choose_spec present
        have ordA := build?_prior input target view reference W D _ _ _ builtA
        have ordA' := build?_prior input target view reference W D _ _ _ built'
        have cross := agree node _ a (childOf _ member') (childOf a member) _ _ ordA' ordA
        have self := agree node a a (childOf a member) (childOf a member) _ _ ordA ordA
        rw [show compare (prior a) (prior a) = .eq from compare_eq_iff_eq.2 rfl] at self
        exact compare_eq_iff_eq.1 (cross.symm.trans self)
      let φ : PromotedKey input → Lex (P × MarkerKey) := fun x => toLex (priorOf x, x.marker)
      have keyMembers : ∀ x ∈ keys, ∃ a ∈ slots,
          build? input target view reference W D fuel (nodeSource input tree a) = some x :=
        fun x member => exists_of_mem_forall₂_right slotRelated x (perm₀.symm.subset member)
      have order : ∀ x ∈ keys, ∀ y ∈ keys, compareKeys input x y ≠ .lt ↔ φ y ≤ φ x := by
        intro x xMember y yMember
        obtain ⟨a, aMember, builtA⟩ := keyMembers x xMember
        obtain ⟨b, bMember, builtB⟩ := keyMembers y yMember
        have ordA := build?_prior input target view reference W D _ _ _ builtA
        have ordB := build?_prior input target view reference W D _ _ _ builtB
        have pairwise := agree node a b (childOf a aMember) (childOf b bMember) _ _ ordA ordB
        simp only [φ, priorOf_eq a aMember x builtA, priorOf_eq b bMember y builtB]
        exact compareKeys_ne_lt_iff input x y (prior a) (prior b) pairwise
      have sorted := sortKeys_marker_eq input keys φ (fun _ => rfl) order
      have keyed : keys₀.map φ = slots.map
          (key (ruleMajorTreeGraph tree) prior (referenceMark input reference tree) W D) := by
        symm
        apply map_eq_of_forall₂
        refine forall₂_imp_mem ?_ slotRelated
        intro a member x builtA
        rw [key_eq_marker, ← ih a (childOf a member) fuel x builtA]
        simp only [φ, priorOf_eq a member x builtA]
      simp only [referenceMark, source]
      congr 1
      rw [sorted, Certificate.CanonicalSphereKey.sortDesc_eq_of_perm (perm₀.map φ).symm, keyed]

/-- At the tree's root: the actual marker of the ligand is the independent canonical marker of
its realized hierarchy. -/
theorem root_marker_eq_markerKey (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {P : Type*} [LinearOrder P] (prior : (ruleMajorTreeGraph tree).Node → P)
    (agree : SiblingPriorAgreement input target view tree prior) (fuel : Nat)
    (result : PromotedKey input)
    (built : build? input target view reference W D fuel tree.source = some result) :
    result.marker = markerKey (ruleMajorTreeGraph tree) prior
      (referenceMark input reference tree) W D (ruleMajorTreeGraph tree).root := by
  apply build?_marker_eq_markerKey input target view reference W D tree realizes prior agree
  rw [nodeSource_root]
  exact built

/-- The actual comparator is reflexive on every key. -/
theorem compareThroughRule5_self (k : input.LocalizedRerootCompoundRule45Key) :
    (input.compareLocalizedRerootCompoundThroughRule5 k k).ordering = .eq := by
  rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
  letI := input.compareLocalizedRerootCompoundRule45Keys_transCmp
  exact Std.ReflCmp.compare_self

/-- Siblings agree whenever both are the same node. Hence a parent with at most one child
imposes no condition on `prior`. -/
theorem agreement_self {P : Type*} [LinearOrder P] (prior : (ruleMajorTreeGraph tree).Node → P)
    (node : (ruleMajorTreeGraph tree).Node) (k : input.LocalizedRerootCompoundRule45Key) :
    (input.compareLocalizedRerootCompoundThroughRule5 k k).ordering =
      compare (prior node) (prior node) := by
  rw [compareThroughRule5_self, compare_eq_iff_eq.2 rfl]

end Tree

end TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker.compareKeys_ne_lt_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker.sortKeys_marker_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker.slot_children
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker.build?_marker_eq_markerKey
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker.root_marker_eq_markerKey
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker.compareThroughRule5_self
