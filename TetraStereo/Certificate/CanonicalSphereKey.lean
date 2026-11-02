import Mathlib.Data.List.Lex
import Mathlib.Data.List.Sort
import Mathlib.Order.WithBot

set_option autoImplicit false

namespace TetraStereo
namespace Certificate
namespace CanonicalSphereKey

universe u




































/-- A finite rooted tree whose children are listed in an arbitrary, semantically irrelevant
order. -/
inductive HTree (α : Type u) where
  | node (label : α) (children : List (HTree α))

namespace HTree

variable {α : Type u}

/-- Induction with a hypothesis for every listed child. -/
theorem induction {motive : HTree α → Prop}
    (step : ∀ label children,
      (∀ child ∈ children, motive child) → motive (node label children)) :
    ∀ tree, motive tree
  | node label children => step label children fun child _ => induction step child
termination_by tree => sizeOf tree
decreasing_by
  have := List.sizeOf_lt_of_mem ‹child ∈ children›
  simp only [node.sizeOf_spec]
  omega

end HTree

variable {α : Type u} [LinearOrder α]

/-- One hierarchy sphere: `W ^ k` dense slots at sphere `k`. -/
abbrev Level (α : Type u) := List (WithBot α)

/-- Spheres `0, …, D` of a tree. -/
abbrev Key (α : Type u) := List (Level α)

/-- The observations of an absent subtree at sphere `k`. -/
def pad (W k : ℕ) : Level α :=
  List.replicate (W ^ k) ⊥

section Sorting

variable {K : Type*} [LinearOrder K]

/-- Descending key order on any linearly ordered key carrier. -/
def Desc (x y : K) : Prop :=
  y ≤ x

instance : DecidableRel (Desc (K := K)) :=
  fun x y => inferInstanceAs (Decidable (y ≤ x))

instance : Std.Total (Desc (K := K)) :=
  ⟨fun x y => le_total y x⟩

instance : IsTrans K Desc :=
  ⟨fun _ _ _ h₁ h₂ => le_trans h₂ h₁⟩

instance : Std.Antisymm (Desc (K := K)) :=
  ⟨fun _ _ h₁ h₂ => le_antisymm h₂ h₁⟩

/-- Descending order of child keys.  Ties may be listed in either order.  Insertion sort is
structurally recursive, so canonical keys of concrete trees reduce in the kernel. -/
def sortDesc (keys : List K) : List K :=
  keys.insertionSort Desc

theorem sortDesc_perm (keys : List K) : (sortDesc keys).Perm keys :=
  List.perm_insertionSort _ _

theorem sortDesc_pairwise (keys : List K) :
    (sortDesc keys).Pairwise fun x y => y ≤ x :=
  List.pairwise_insertionSort Desc keys

theorem sortDesc_eq_of_perm {keys keys' : List K} (h : keys.Perm keys') :
    sortDesc keys = sortDesc keys' :=
  List.Perm.eq_of_pairwise' (r := Desc) (sortDesc_pairwise keys) (sortDesc_pairwise keys')
    (((sortDesc_perm keys).trans h).trans (sortDesc_perm keys').symm)

theorem sortDesc_of_pairwise {keys : List K} (h : keys.Pairwise fun x y => y ≤ x) :
    sortDesc keys = keys :=
  List.Pairwise.insertionSort_eq (r := Desc) h

theorem sortDesc_mem {keys : List K} {key : K} (h : key ∈ sortDesc keys) : key ∈ keys :=
  (sortDesc_perm keys).subset h

theorem sortDesc_length (keys : List K) : (sortDesc keys).length = keys.length :=
  (sortDesc_perm keys).length_eq

end Sorting

/-- Sphere-major layout of a node label above its listed child keys.  Sphere `k + 1` concatenates
sphere `k` of the first `W` children in list order, padding absent children with `⊥`. -/
def assemble (W D : ℕ) (label : α) (keys : List (Key α)) : Key α :=
  [(label : WithBot α)] :: (List.range D).map fun k =>
    (List.range W).flatMap fun slot => (keys.getD slot []).getD k (pad W k)

mutual
/-- The canonical key: children are ranked by their own canonical keys before layout. -/
def ckey (W D : ℕ) : HTree α → Key α
  | .node label children => assemble W D label (sortDesc (ckeyList W D children))

/-- Canonical keys of a child list, in list order. -/
def ckeyList (W D : ℕ) : List (HTree α) → List (Key α)
  | [] => []
  | child :: children => ckey W D child :: ckeyList W D children
end

mutual
/-- The key observed through the tree's own sibling order, without ranking. -/
def orderedKey (W D : ℕ) : HTree α → Key α
  | .node label children => assemble W D label (orderedKeyList W D children)

/-- Ordered keys of a child list, in list order. -/
def orderedKeyList (W D : ℕ) : List (HTree α) → List (Key α)
  | [] => []
  | child :: children => orderedKey W D child :: orderedKeyList W D children
end

theorem ckeyList_eq_map (W D : ℕ) (children : List (HTree α)) :
    ckeyList W D children = children.map (ckey W D) := by
  induction children with
  | nil => rfl
  | cons child children ih => simp [ckeyList, ih]

omit [LinearOrder α] in
theorem orderedKeyList_eq_map (W D : ℕ) (children : List (HTree α)) :
    orderedKeyList W D children = children.map (orderedKey W D) := by
  induction children with
  | nil => rfl
  | cons child children ih => simp [orderedKeyList, ih]

theorem ckey_node (W D : ℕ) (label : α) (children : List (HTree α)) :
    ckey W D (.node label children) =
      assemble W D label (sortDesc (children.map (ckey W D))) := by
  rw [ckey, ckeyList_eq_map]

omit [LinearOrder α] in
theorem orderedKey_node (W D : ℕ) (label : α) (children : List (HTree α)) :
    orderedKey W D (.node label children) =
      assemble W D label (children.map (orderedKey W D)) := by
  rw [orderedKey, orderedKeyList_eq_map]

/-! ## Representation independence -/

/-- Permuting the children of a node does not change its canonical key. -/
theorem ckey_perm (W D : ℕ) (label : α) {children children' : List (HTree α)}
    (h : children.Perm children') :
    ckey W D (.node label children) = ckey W D (.node label children') := by
  rw [ckey_node, ckey_node, sortDesc_eq_of_perm (h.map _)]

/-- Congruence for unordered-tree isomorphism: matched children with equal keys, listed in any
order, give the parent the same key.  Induction on any isomorphism notion reduces to this step. -/
theorem ckey_congr (W D : ℕ) (label : α) {children matched children' : List (HTree α)}
    (hmatch : List.Forall₂ (fun left right => ckey W D left = ckey W D right) children matched)
    (hperm : matched.Perm children') :
    ckey W D (.node label children) = ckey W D (.node label children') := by
  have hmap : children.map (ckey W D) = matched.map (ckey W D) := by
    clear hperm
    induction hmatch with
    | nil => rfl
    | cons hhead _ ih => simp [hhead, ih]
  rw [ckey_node, hmap, ← ckey_node]
  exact ckey_perm W D label hperm

/-! ## Uniform shape and observations -/

/-- A key has spheres `0, …, D`, and sphere `k` has exactly `W ^ k` slots. -/
def WellShaped (W D : ℕ) (key : Key α) : Prop :=
  key.length = D + 1 ∧ ∀ k (hk : k < key.length), key[k].length = W ^ k

omit [LinearOrder α] in
theorem slotLevel_length {W D : ℕ} {keys : List (Key α)}
    (hkeys : ∀ key ∈ keys, WellShaped W D key) {k : ℕ} (hk : k < D) (slot : ℕ) :
    ((keys.getD slot []).getD k (pad W k)).length = W ^ k := by
  by_cases hs : slot < keys.length
  · have hmem : keys[slot] ∈ keys := List.getElem_mem hs
    obtain ⟨hlen, hlevel⟩ := hkeys _ hmem
    have hkl : k < keys[slot].length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs,
      List.getElem?_eq_getElem hkl, hlevel k hkl]
  · simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : keys.length ≤ slot), pad]

omit [LinearOrder α] in
theorem assemble_wellShaped (W D : ℕ) (label : α) (keys : List (Key α))
    (hkeys : ∀ key ∈ keys, WellShaped W D key) :
    WellShaped W D (assemble W D label keys) := by
  refine ⟨by simp [assemble], ?_⟩
  intro k hk
  cases k with
  | zero => simp [assemble]
  | succ k =>
      have hkD : k < D := by simpa [assemble] using hk
      simp only [assemble, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
      have hslot : ∀ slot ∈ List.range W,
          ((keys.getD slot []).getD k (pad W k)).length = W ^ k :=
        fun slot _ => slotLevel_length hkeys hkD slot
      rw [List.length_flatMap, List.map_congr_left hslot]
      simp [Nat.pow_succ, Nat.mul_comm]

theorem ckey_wellShaped (W D : ℕ) : ∀ tree : HTree α, WellShaped W D (ckey W D tree) := by
  refine HTree.induction ?_
  intro label children ih
  rw [ckey_node]
  apply assemble_wellShaped
  intro key hkey
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.1 (sortDesc_mem hkey)
  exact ih child hchild

/-- The observation at sphere `k`, dense slot `slot`. -/
def observation (W D : ℕ) (tree : HTree α) (k slot : ℕ) : WithBot α :=
  ((ckey W D tree).getD k []).getD slot ⊥

omit [LinearOrder α] in
theorem eq_of_wellShaped_of_getD {W D : ℕ} {left right : Key α}
    (hleft : WellShaped W D left) (hright : WellShaped W D right)
    (hobs : ∀ k slot, (left.getD k []).getD slot ⊥ = (right.getD k []).getD slot ⊥) :
    left = right := by
  obtain ⟨hll, hlk⟩ := hleft
  obtain ⟨hrl, hrk⟩ := hright
  apply List.ext_getElem (by omega)
  intro k hkl hkr
  apply List.ext_getElem (by rw [hlk k hkl, hrk k hkr])
  intro slot hsl hsr
  have := hobs k slot
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl,
    List.getElem?_eq_getElem hkr, List.getElem?_eq_getElem hsl,
    List.getElem?_eq_getElem hsr] using this

/-- Ties of the canonical priority are exactly equality of every sphere-major observation. -/
theorem ckey_eq_iff_observation (W D : ℕ) (left right : HTree α) :
    ckey W D left = ckey W D right ↔
      ∀ k slot, observation W D left k slot = observation W D right k slot := by
  constructor
  · intro h k slot
    simp [observation, h]
  · intro h
    exact eq_of_wellShaped_of_getD (ckey_wellShaped W D left) (ckey_wellShaped W D right) h

/-! ## Sphere-major first difference -/

/-- Strict lexicographic order on equal-length lists is decided at the first differing position. -/
theorem list_lt_iff_first_difference {β : Type*} [LinearOrder β] {l₁ l₂ : List β}
    (hlen : l₁.length = l₂.length) :
    l₁ < l₂ ↔ ∃ i, ∃ (h₁ : i < l₁.length) (h₂ : i < l₂.length),
      (∀ j (hj : j < i), l₁[j] = l₂[j]) ∧ l₁[i] < l₂[i] := by
  have h := List.lt_iff_exists (l₁ := l₁) (l₂ := l₂)
  constructor
  · intro hlt
    rcases h.1 hlt with ⟨_, hshort⟩ | hex
    · omega
    · exact hex
  · intro hex
    exact h.2 (Or.inr hex)

/-- Observation `slot` of sphere `k` of a key, `⊥` outside its slots. -/
def keyObservation (key : Key α) (k slot : ℕ) : WithBot α :=
  (key.getD k []).getD slot ⊥

omit [LinearOrder α] in
theorem keyObservation_of_lt {key : Key α} {k slot : ℕ} (hk : k < key.length)
    (hs : slot < key[k].length) : keyObservation key k slot = key[k][slot] := by
  simp [keyObservation, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hs]

omit [LinearOrder α] in
theorem keyObservation_of_not_lt {key : Key α} {k slot : ℕ}
    (h : ¬ (∃ hk : k < key.length, slot < key[k].length)) : keyObservation key k slot = ⊥ := by
  by_cases hk : k < key.length
  · have hs : ¬ slot < key[k].length := fun hs => h ⟨hk, hs⟩
    simp [keyObservation, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      List.getElem?_eq_none (by omega : key[k].length ≤ slot)]
  · simp [keyObservation, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : key.length ≤ k)]

omit [LinearOrder α] in
theorem level_eq_of_keyObservation {left right : Key α} {k : ℕ} (hl : k < left.length)
    (hr : k < right.length) (hlen : left[k].length = right[k].length)
    (hobs : ∀ slot, keyObservation left k slot = keyObservation right k slot) :
    left[k] = right[k] := by
  apply List.ext_getElem hlen
  intro slot hsl hsr
  rw [← keyObservation_of_lt hl hsl, ← keyObservation_of_lt hr hsr]
  exact hobs slot

/-- On well-shaped keys, the key order is the sphere-major first difference of observations:
spheres are compared in order of distance, and dense slots in order within a sphere. -/
theorem key_lt_iff_first_difference {W D : ℕ} {left right : Key α}
    (hleft : WellShaped W D left) (hright : WellShaped W D right) :
    left < right ↔ ∃ k slot,
      keyObservation left k slot < keyObservation right k slot ∧
        (∀ k' < k, ∀ slot', keyObservation left k' slot' = keyObservation right k' slot') ∧
        (∀ slot' < slot, keyObservation left k slot' = keyObservation right k slot') := by
  obtain ⟨hll, hlk⟩ := hleft
  obtain ⟨hrl, hrk⟩ := hright
  rw [list_lt_iff_first_difference (by omega)]
  constructor
  · rintro ⟨k, hkl, hkr, hbefore, hlevel⟩
    have hlen : left[k].length = right[k].length := by rw [hlk k hkl, hrk k hkr]
    obtain ⟨slot, hsl, hsr, hslots, hslot⟩ :=
      (list_lt_iff_first_difference hlen).1 hlevel
    refine ⟨k, slot, ?_, ?_, ?_⟩
    · rw [keyObservation_of_lt hkl hsl, keyObservation_of_lt hkr hsr]
      exact hslot
    · intro k' hk' slot'
      have hk'l : k' < left.length := by omega
      have hk'r : k' < right.length := by omega
      simp only [keyObservation, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'l,
        List.getElem?_eq_getElem hk'r, Option.getD_some, hbefore k' hk']
    · intro slot' hslot'
      have hs'l : slot' < left[k].length := by omega
      have hs'r : slot' < right[k].length := by omega
      rw [keyObservation_of_lt hkl hs'l, keyObservation_of_lt hkr hs'r]
      exact hslots slot' hslot'
  · rintro ⟨k, slot, hslot, hbefore, hslots⟩
    have hin : ∃ hk : k < left.length, slot < left[k].length := by
      by_contra hout
      by_cases hinr : ∃ hk : k < right.length, slot < right[k].length
      · obtain ⟨hkr, hsr⟩ := hinr
        exact hout ⟨by omega, by rw [hlk k (by omega)]; rw [hrk k hkr] at hsr; exact hsr⟩
      · rw [keyObservation_of_not_lt hout, keyObservation_of_not_lt hinr] at hslot
        exact lt_irrefl _ hslot
    obtain ⟨hkl, hsl⟩ := hin
    have hkr : k < right.length := by omega
    have hlen : left[k].length = right[k].length := by rw [hlk k hkl, hrk k hkr]
    have hsr : slot < right[k].length := by omega
    refine ⟨k, hkl, hkr, ?_, ?_⟩
    · intro j hj
      exact level_eq_of_keyObservation (by omega) (by omega)
        (by rw [hlk j (by omega), hrk j (by omega)]) (hbefore j hj)
    · apply (list_lt_iff_first_difference hlen).2
      refine ⟨slot, hsl, hsr, ?_, ?_⟩
      · intro j hj
        rw [← keyObservation_of_lt hkl (by omega), ← keyObservation_of_lt hkr (by omega)]
        exact hslots j hj
      · rw [← keyObservation_of_lt hkl hsl, ← keyObservation_of_lt hkr hsr]
        exact hslot

/-- Canonical priority is decided by the first sphere-major observation at which two trees differ.
No traversal history, opponent, fuel or chosen addressing enters this statement. -/
theorem ckey_lt_iff_first_difference (W D : ℕ) (left right : HTree α) :
    ckey W D left < ckey W D right ↔ ∃ k slot,
      observation W D left k slot < observation W D right k slot ∧
        (∀ k' < k, ∀ slot', observation W D left k' slot' = observation W D right k' slot') ∧
        (∀ slot' < slot, observation W D left k slot' = observation W D right k slot') :=
  key_lt_iff_first_difference (ckey_wellShaped W D left) (ckey_wellShaped W D right)

/-! ## The induced priority -/

/-- Strict canonical priority of `left` over `right`. -/
def Higher (W D : ℕ) (left right : HTree α) : Prop :=
  ckey W D right < ckey W D left

/-- Canonical tie. -/
def Tied (W D : ℕ) (left right : HTree α) : Prop :=
  ckey W D left = ckey W D right

instance (W D : ℕ) : DecidableRel (Higher (α := α) W D) :=
  fun left right => inferInstanceAs (Decidable (ckey W D right < ckey W D left))

instance (W D : ℕ) : DecidableRel (Tied (α := α) W D) :=
  fun left right => inferInstanceAs (Decidable (ckey W D left = ckey W D right))

theorem higher_irrefl (W D : ℕ) (tree : HTree α) : ¬ Higher W D tree tree :=
  lt_irrefl _

theorem higher_asymm (W D : ℕ) {left right : HTree α}
    (h : Higher W D left right) : ¬ Higher W D right left :=
  lt_asymm h

theorem higher_trans (W D : ℕ) {first second third : HTree α}
    (h₁ : Higher W D first second) (h₂ : Higher W D second third) : Higher W D first third :=
  lt_trans h₂ h₁

theorem higher_trichotomous (W D : ℕ) (left right : HTree α) :
    Higher W D left right ∨ Tied W D left right ∨ Higher W D right left := by
  rcases lt_trichotomy (ckey W D right) (ckey W D left) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h)

/-- A tie is preserved by later observations: tied trees are indistinguishable at every sphere. -/
theorem tied_observation (W D : ℕ) {left right : HTree α} (h : Tied W D left right)
    (k slot : ℕ) : observation W D left k slot = observation W D right k slot :=
  (ckey_eq_iff_observation W D left right).1 h k slot

/-! ## The admissible addressing family -/

mutual
/-- At every node, the listed children are in descending canonical order.  Order inside a tie class
is unconstrained. -/
def CanonicallyOrdered (W D : ℕ) : HTree α → Prop
  | .node _ children =>
      (children.map (ckey W D)).Pairwise (fun x y => y ≤ x) ∧ AllCanonicallyOrdered W D children

/-- Every listed child is canonically ordered. -/
def AllCanonicallyOrdered (W D : ℕ) : List (HTree α) → Prop
  | [] => True
  | child :: children => CanonicallyOrdered W D child ∧ AllCanonicallyOrdered W D children
end

theorem allCanonicallyOrdered_iff (W D : ℕ) (children : List (HTree α)) :
    AllCanonicallyOrdered W D children ↔
      ∀ child ∈ children, CanonicallyOrdered W D child := by
  induction children with
  | nil => simp [AllCanonicallyOrdered]
  | cons child children ih => simp [AllCanonicallyOrdered, ih]

theorem canonicallyOrdered_node (W D : ℕ) (label : α) (children : List (HTree α)) :
    CanonicallyOrdered W D (.node label children) ↔
      (children.map (ckey W D)).Pairwise (fun x y => y ≤ x) ∧
        ∀ child ∈ children, CanonicallyOrdered W D child := by
  rw [CanonicallyOrdered, allCanonicallyOrdered_iff]

/-- Every admissible addressing observes exactly the canonical key.  Different admissible
addressings of one tree differ only inside tie classes, so they cannot be distinguished. -/
theorem orderedKey_eq_ckey (W D : ℕ) :
    ∀ tree : HTree α, CanonicallyOrdered W D tree → orderedKey W D tree = ckey W D tree := by
  refine HTree.induction ?_
  intro label children ih hordered
  obtain ⟨hsorted, hchildren⟩ := (canonicallyOrdered_node W D label children).1 hordered
  have hmap : children.map (orderedKey W D) = children.map (ckey W D) :=
    List.map_congr_left fun child hchild => ih child hchild (hchildren child hchild)
  rw [orderedKey_node, ckey_node, hmap, sortDesc_of_pairwise hsorted]

/-- Descending canonical-key order of trees. -/
def TreeDesc (W D : ℕ) (x y : HTree α) : Prop :=
  Desc (ckey W D x) (ckey W D y)

instance (W D : ℕ) : DecidableRel (TreeDesc (α := α) W D) :=
  fun x y => inferInstanceAs (Decidable (Desc (ckey W D x) (ckey W D y)))

/-- Rank the children of every node by canonical key. -/
def canonicalize (W D : ℕ) : HTree α → HTree α
  | .node label children =>
      .node label ((children.attach.map fun child => canonicalize W D child.1).insertionSort
        (TreeDesc W D))
termination_by tree => sizeOf tree
decreasing_by
  have := List.sizeOf_lt_of_mem child.2
  simp only [HTree.node.sizeOf_spec]
  omega

theorem canonicalize_node (W D : ℕ) (label : α) (children : List (HTree α)) :
    canonicalize W D (.node label children) =
      .node label ((children.map (canonicalize W D)).insertionSort (TreeDesc W D)) := by
  rw [canonicalize]
  congr 2
  exact List.attach_map_val

/-- Canonicalization preserves the canonical key. -/
theorem ckey_canonicalize (W D : ℕ) :
    ∀ tree : HTree α, ckey W D (canonicalize W D tree) = ckey W D tree := by
  refine HTree.induction ?_
  intro label children ih
  rw [canonicalize_node, ckey_node, ckey_node]
  have hperm := List.perm_insertionSort (TreeDesc W D) (children.map (canonicalize W D))
  rw [sortDesc_eq_of_perm (hperm.map (ckey W D)), List.map_map]
  congr 2
  exact List.map_congr_left fun child hchild => ih child hchild

/-- Canonicalization chooses an admissible addressing, so the admissible family is inhabited. -/
theorem canonicalize_canonicallyOrdered (W D : ℕ) :
    ∀ tree : HTree α, CanonicallyOrdered W D (canonicalize W D tree) := by
  refine HTree.induction ?_
  intro label children ih
  rw [canonicalize_node, canonicallyOrdered_node]
  constructor
  · rw [List.map_insertionSort (TreeDesc W D) Desc (ckey W D) _ (fun _ _ _ _ => Iff.rfl)]
    exact List.pairwise_insertionSort Desc _
  · intro child hchild
    have hmem := (List.perm_insertionSort _ _).subset hchild
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.1 hmem
    exact ih original horiginal

theorem orderedKey_canonicalize (W D : ℕ) (tree : HTree α) :
    orderedKey W D (canonicalize W D tree) = ckey W D tree := by
  rw [orderedKey_eq_ckey W D _ (canonicalize_canonicallyOrdered W D tree),
    ckey_canonicalize]

/-! ## Hierarchy addresses -/

/-- The label reached by following child indices from the root; `⊥` once the path leaves the
tree. -/
def labelAt : HTree α → List ℕ → WithBot α
  | .node label _, [] => label
  | .node _ children, slot :: path =>
      match children[slot]? with
      | some child => labelAt child path
      | none => ⊥

/-- Dense slot of an address: the first child index is the most significant base-`W` digit. -/
def slotOf (W : ℕ) : List ℕ → ℕ
  | [] => 0
  | slot :: path => slot * W ^ path.length + slotOf W path

theorem slotOf_lt {W : ℕ} :
    ∀ {path : List ℕ}, (∀ i ∈ path, i < W) → slotOf W path < W ^ path.length
  | [], _ => by simp [slotOf]
  | slot :: path, h => by
      have hs : slot < W := h slot (by simp)
      have ih := slotOf_lt (path := path) fun i hi => h i (by simp [hi])
      have hstep : (slot + 1) * W ^ path.length ≤ W * W ^ path.length :=
        Nat.mul_le_mul_right _ hs
      rw [Nat.succ_mul] at hstep
      simp only [slotOf, List.length_cons, Nat.pow_succ]
      rw [Nat.mul_comm (W ^ path.length) W]
      omega

/-- Within one sphere, the dense slot order is the lexicographic order of addresses. -/
theorem slotOf_lt_slotOf_iff {W : ℕ} :
    ∀ {left right : List ℕ}, left.length = right.length →
      (∀ i ∈ left, i < W) → (∀ i ∈ right, i < W) →
        (slotOf W left < slotOf W right ↔ left < right)
  | [], [], _, _, _ => by simp [slotOf]
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | i :: left, j :: right, hlen, hleft, hright => by
      have hl : left.length = right.length := by simpa using hlen
      have ih := slotOf_lt_slotOf_iff (W := W) hl (fun a ha => hleft a (by simp [ha]))
        (fun a ha => hright a (by simp [ha]))
      have bl := slotOf_lt (W := W) (path := left) fun a ha => hleft a (by simp [ha])
      have br := slotOf_lt (W := W) (path := right) fun a ha => hright a (by simp [ha])
      rw [List.cons_lt_cons_iff, ← ih]
      simp only [slotOf]
      rw [hl] at bl ⊢
      constructor
      · intro h
        rcases lt_trichotomy i j with hij | rfl | hij
        · exact Or.inl hij
        · exact Or.inr ⟨rfl, by omega⟩
        · exfalso
          have hmul := Nat.mul_le_mul_right (W ^ right.length) (Nat.succ_le_of_lt hij)
          rw [Nat.succ_mul] at hmul
          omega
      · rintro (hij | ⟨rfl, h⟩)
        · have hmul := Nat.mul_le_mul_right (W ^ right.length) (Nat.succ_le_of_lt hij)
          rw [Nat.succ_mul] at hmul
          omega
        · omega

/-- The address of dense slot `slot` at sphere `k`: its base-`W` digits, most significant first. -/
def pathOf (W : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, slot => slot / W ^ k :: pathOf W k (slot % W ^ k)

theorem pathOf_length (W : ℕ) : ∀ k slot, (pathOf W k slot).length = k
  | 0, _ => rfl
  | k + 1, slot => by simp [pathOf, pathOf_length W k]

theorem pathOf_digits {W : ℕ} : ∀ {k slot}, slot < W ^ k → ∀ digit ∈ pathOf W k slot, digit < W
  | 0, _, _ => by simp [pathOf]
  | k + 1, slot, hslot => by
      have hpos : 0 < W ^ k := by
        rcases Nat.eq_zero_or_pos (W ^ k) with h | h
        · rw [Nat.pow_succ, h, Nat.zero_mul] at hslot; omega
        · exact h
      intro digit hdigit
      simp only [pathOf, List.mem_cons] at hdigit
      rcases hdigit with rfl | hdigit
      · rw [Nat.div_lt_iff_lt_mul hpos]
        rw [Nat.pow_succ, Nat.mul_comm] at hslot
        exact hslot
      · exact pathOf_digits (Nat.mod_lt _ hpos) digit hdigit

theorem slotOf_pathOf {W : ℕ} : ∀ {k slot}, slot < W ^ k → slotOf W (pathOf W k slot) = slot
  | 0, slot, hslot => by simp at hslot; simp [pathOf, slotOf, hslot]
  | k + 1, slot, hslot => by
      have hpos : 0 < W ^ k := by
        rcases Nat.eq_zero_or_pos (W ^ k) with h | h
        · rw [Nat.pow_succ, h, Nat.zero_mul] at hslot; omega
        · exact h
      simp only [pathOf, slotOf, pathOf_length]
      rw [slotOf_pathOf (Nat.mod_lt _ hpos)]
      exact Nat.div_add_mod' slot (W ^ k)

theorem pathOf_slotOf {W : ℕ} : ∀ {path : List ℕ}, (∀ digit ∈ path, digit < W) →
    pathOf W path.length (slotOf W path) = path
  | [], _ => rfl
  | digit :: path, h => by
      have hpath : ∀ i ∈ path, i < W := fun i hi => h i (by simp [hi])
      have hbound := slotOf_lt hpath
      have hpos : 0 < W ^ path.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hbound
      simp only [List.length_cons, pathOf, slotOf]
      rw [Nat.add_comm (digit * _), Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hbound,
        Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbound, pathOf_slotOf hpath]

omit [LinearOrder α] in
theorem getD_flatMap_range {β : Type*} {n : ℕ} (f : ℕ → List β) (d : β) :
    ∀ W, (∀ i < W, (f i).length = n) → ∀ {i j : ℕ}, i < W → j < n →
      ((List.range W).flatMap f).getD (i * n + j) d = (f i).getD j d
  | 0, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | W + 1, hf, i, j, hi, hj => by
      have hlen : ((List.range W).flatMap f).length = W * n := by
        rw [List.length_flatMap, List.map_congr_left (fun k hk => hf k (by
          simp only [List.mem_range] at hk; omega))]
        simp
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rcases Nat.lt_or_ge i W with hiW | hiW
      · have hmul := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hiW)
        rw [Nat.succ_mul] at hmul
        have hidx : i * n + j < ((List.range W).flatMap f).length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hidx,
          ← List.getD_eq_getElem?_getD]
        exact getD_flatMap_range f d W (fun k hk => hf k (by omega)) hiW hj
      · have hiW' : i = W := by omega
        subst hiW'
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen,
          ← List.getD_eq_getElem?_getD]
        congr 1
        omega

omit [LinearOrder α] in
theorem orderedKey_wellShaped (W D : ℕ) :
    ∀ tree : HTree α, WellShaped W D (orderedKey W D tree) := by
  refine HTree.induction ?_
  intro label children ih
  rw [orderedKey_node]
  apply assemble_wellShaped
  intro key hkey
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.1 hkey
  exact ih child hchild

omit [LinearOrder α] in
/-- Along any listed sibling order, the observation at dense slot `slotOf W path` of sphere
`path.length` is the label at hierarchy address `path`. -/
theorem keyObservation_orderedKey_eq_labelAt (W D : ℕ) :
    ∀ (path : List ℕ) (tree : HTree α), (∀ i ∈ path, i < W) → path.length ≤ D →
      keyObservation (orderedKey W D tree) path.length (slotOf W path) = labelAt tree path
  | [], .node label children, _, _ => by
      simp [keyObservation, orderedKey_node, assemble, slotOf, labelAt]
  | slot :: path, .node label children, hdig, hlen => by
      have hs : slot < W := hdig slot (by simp)
      have hpath : ∀ i ∈ path, i < W := fun i hi => hdig i (by simp [hi])
      have hpl : path.length < D := by simp at hlen; omega
      have hbound := slotOf_lt hpath
      have hkeys : ∀ key ∈ children.map (orderedKey W D), WellShaped W D key := by
        intro key hkey
        obtain ⟨child, _, rfl⟩ := List.mem_map.1 hkey
        exact orderedKey_wellShaped W D child
      rw [orderedKey_node]
      simp only [keyObservation, assemble, List.length_cons, slotOf, List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range hpl, Option.map_some, Option.getD_some,
        getD_flatMap_range _ _ W (fun i _ => slotLevel_length hkeys hpl i) hs hbound]
      cases hchild : children[slot]? with
      | none =>
          have hnone : (children.map (orderedKey W D))[slot]? = none := by simp [hchild]
          simp only [labelAt, hchild, List.getD_eq_getElem?_getD, hnone, Option.getD_none,
            List.getElem?_nil, pad, List.getElem?_replicate]
          split <;> rfl
      | some child =>
          have hsome : (children.map (orderedKey W D))[slot]? = some (orderedKey W D child) := by
            simp [hchild]
          have ih := keyObservation_orderedKey_eq_labelAt W D path child hpath (by omega)
          simp only [labelAt, hchild]
          rw [← ih]
          have hk : path.length < (orderedKey W D child).length := by
            rw [(orderedKey_wellShaped W D child).1]
            omega
          simp [keyObservation, List.getD_eq_getElem?_getD, hsome, List.getElem?_eq_getElem hk]

/-- Canonical observations are the labels of every admissible addressing at the corresponding
hierarchy address: sphere `path.length`, dense slot `slotOf W path`. -/
theorem observation_eq_labelAt (W D : ℕ) (tree : HTree α) (ordered : CanonicallyOrdered W D tree)
    (path : List ℕ) (hdigits : ∀ i ∈ path, i < W) (hdepth : path.length ≤ D) :
    observation W D tree path.length (slotOf W path) = labelAt tree path := by
  change keyObservation (ckey W D tree) path.length (slotOf W path) = labelAt tree path
  rw [← orderedKey_eq_ckey W D tree ordered]
  exact keyObservation_orderedKey_eq_labelAt W D path tree hdigits hdepth

/-- In particular, canonicalization realizes the canonical observations as hierarchy labels. -/
theorem observation_eq_labelAt_canonicalize (W D : ℕ) (tree : HTree α)
    (path : List ℕ) (hdigits : ∀ i ∈ path, i < W) (hdepth : path.length ≤ D) :
    observation W D tree path.length (slotOf W path) =
      labelAt (canonicalize W D tree) path := by
  rw [← observation_eq_labelAt W D _ (canonicalize_canonicallyOrdered W D tree) path hdigits
    hdepth]
  simp [observation, ckey_canonicalize]

/-! ## Path observations of keys -/

/-- Shortlex address order: nearer spheres first, then lexicographic order of addresses. -/
def AddressBefore (earlier later : List ℕ) : Prop :=
  earlier.length < later.length ∨ (earlier.length = later.length ∧ earlier < later)

/-- The observation of a `(W, D)` key at address `path`; addresses leaving the layout read `⊥`. -/
def pathObservationOf (W D : ℕ) (key : Key α) (path : List ℕ) : WithBot α :=
  if (∀ digit ∈ path, digit < W) ∧ path.length ≤ D then
    keyObservation key path.length (slotOf W path)
  else ⊥

omit [LinearOrder α] in
theorem keyObservation_eq_bot_of_out {W D : ℕ} {key : Key α} (hkey : WellShaped W D key)
    {k slot : ℕ} (hout : ¬ (k ≤ D ∧ slot < W ^ k)) : keyObservation key k slot = ⊥ := by
  apply keyObservation_of_not_lt
  rintro ⟨hk, hs⟩
  apply hout
  have hlevel := hkey.2 k hk
  have hlength := hkey.1
  rw [hlevel] at hs
  exact ⟨by omega, hs⟩

omit [LinearOrder α] in
theorem pathObservationOf_pathOf {W D : ℕ} (key : Key α) {k slot : ℕ} (hk : k ≤ D)
    (hslot : slot < W ^ k) :
    pathObservationOf W D key (pathOf W k slot) = keyObservation key k slot := by
  unfold pathObservationOf
  rw [if_pos ⟨pathOf_digits hslot, by rw [pathOf_length]; exact hk⟩, pathOf_length,
    slotOf_pathOf hslot]

omit [LinearOrder α] in
/-- Well-shaped keys are equal exactly when all their path observations agree. -/
theorem key_eq_iff_pathObservation {W D : ℕ} {left right : Key α}
    (hleft : WellShaped W D left) (hright : WellShaped W D right) :
    left = right ↔ ∀ path, pathObservationOf W D left path = pathObservationOf W D right path := by
  constructor
  · rintro rfl _
    rfl
  · intro h
    apply eq_of_wellShaped_of_getD hleft hright
    intro k slot
    change keyObservation left k slot = keyObservation right k slot
    by_cases hin : k ≤ D ∧ slot < W ^ k
    · rw [← pathObservationOf_pathOf left hin.1 hin.2, ← pathObservationOf_pathOf right hin.1 hin.2]
      exact h _
    · rw [keyObservation_eq_bot_of_out hleft hin, keyObservation_eq_bot_of_out hright hin]

/-- Well-shaped keys are ordered by the first path observation, in shortlex address order, at
which they differ.  The statement no longer mentions dense slots or the layout width. -/
theorem key_lt_iff_pathObservation {W D : ℕ} {left right : Key α}
    (hleft : WellShaped W D left) (hright : WellShaped W D right) :
    left < right ↔ ∃ path,
      pathObservationOf W D left path < pathObservationOf W D right path ∧
        ∀ earlier, AddressBefore earlier path →
          pathObservationOf W D left earlier = pathObservationOf W D right earlier := by
  rw [key_lt_iff_first_difference hleft hright]
  constructor
  · rintro ⟨k, slot, hlt, hbefore, hslots⟩
    have hin : k ≤ D ∧ slot < W ^ k := by
      by_contra hout
      rw [keyObservation_eq_bot_of_out hleft hout, keyObservation_eq_bot_of_out hright hout] at hlt
      exact lt_irrefl _ hlt
    refine ⟨pathOf W k slot, ?_, ?_⟩
    · rw [pathObservationOf_pathOf left hin.1 hin.2, pathObservationOf_pathOf right hin.1 hin.2]
      exact hlt
    · intro earlier hearlier
      unfold pathObservationOf
      split
      · rename_i hguard
        rcases hearlier with hshort | ⟨hsame, hlex⟩
        · rw [pathOf_length] at hshort
          exact hbefore _ hshort _
        · rw [pathOf_length] at hsame
          have hdigits := pathOf_digits hin.2
          have hslot : slotOf W earlier < slotOf W (pathOf W k slot) :=
            (slotOf_lt_slotOf_iff (by rw [pathOf_length]; exact hsame) hguard.1 hdigits).2 hlex
          rw [slotOf_pathOf hin.2] at hslot
          rw [hsame]
          exact hslots _ hslot
      · rfl
  · rintro ⟨path, hlt, hbefore⟩
    have hguard : (∀ digit ∈ path, digit < W) ∧ path.length ≤ D := by
      by_contra hout
      unfold pathObservationOf at hlt
      rw [if_neg hout, if_neg hout] at hlt
      exact lt_irrefl _ hlt
    unfold pathObservationOf at hlt
    rw [if_pos hguard, if_pos hguard] at hlt
    have hbound := slotOf_lt hguard.1
    refine ⟨path.length, slotOf W path, hlt, ?_, ?_⟩
    · intro k hk slot
      by_cases hin : k ≤ D ∧ slot < W ^ k
      · have h := hbefore (pathOf W k slot) (Or.inl (by rw [pathOf_length]; exact hk))
        rwa [pathObservationOf_pathOf left hin.1 hin.2,
          pathObservationOf_pathOf right hin.1 hin.2] at h
      · rw [keyObservation_eq_bot_of_out hleft hin, keyObservation_eq_bot_of_out hright hin]
    · intro slot hslot
      have hlt' : slot < W ^ path.length := lt_trans hslot hbound
      have hearlier : AddressBefore (pathOf W path.length slot) path := by
        refine Or.inr ⟨pathOf_length _ _ _, ?_⟩
        apply (slotOf_lt_slotOf_iff (pathOf_length _ _ _) (pathOf_digits hlt') hguard.1).1
        rw [slotOf_pathOf hlt']
        exact hslot
      have h := hbefore _ hearlier
      rwa [pathObservationOf_pathOf left hguard.2 hlt',
        pathObservationOf_pathOf right hguard.2 hlt'] at h

/-- A vector of `m` well-shaped keys, compared lexicographically component by component. -/
def VectorWellShaped (m W D : ℕ) (vector : List (Key α)) : Prop :=
  vector.length = m ∧ ∀ r < m, WellShaped W D (vector.getD r [])

omit [LinearOrder α] in
theorem vector_eq_iff_pathObservation {m W D : ℕ} {left right : List (Key α)}
    (hleft : VectorWellShaped m W D left) (hright : VectorWellShaped m W D right) :
    left = right ↔ ∀ r < m, ∀ path,
      pathObservationOf W D (left.getD r []) path = pathObservationOf W D (right.getD r []) path := by
  constructor
  · rintro rfl _ _ _
    rfl
  · intro h
    apply List.ext_getElem (by rw [hleft.1, hright.1])
    intro r hrl hrr
    have hr : r < m := by rw [← hleft.1]; exact hrl
    have heq := (key_eq_iff_pathObservation (hleft.2 r hr) (hright.2 r hr)).2 (h r hr)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl,
      List.getElem?_eq_getElem hrr] using heq

/-- Vector keys are ordered by the first rule component that differs, and inside it by the first
differing path observation. -/
theorem vector_lt_iff_pathObservation {m W D : ℕ} {left right : List (Key α)}
    (hleft : VectorWellShaped m W D left) (hright : VectorWellShaped m W D right) :
    left < right ↔ ∃ r < m, ∃ path,
      pathObservationOf W D (left.getD r []) path < pathObservationOf W D (right.getD r []) path ∧
        (∀ r' < r, ∀ path',
          pathObservationOf W D (left.getD r' []) path' =
            pathObservationOf W D (right.getD r' []) path') ∧
        ∀ earlier, AddressBefore earlier path →
          pathObservationOf W D (left.getD r []) earlier =
            pathObservationOf W D (right.getD r []) earlier := by
  have hgetl : ∀ r (h : r < left.length), left.getD r [] = left[r] := fun r h => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  have hgetr : ∀ r (h : r < right.length), right.getD r [] = right[r] := fun r h => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rw [list_lt_iff_first_difference (by rw [hleft.1, hright.1])]
  constructor
  · rintro ⟨r, hrl, hrr, hbefore, hlt⟩
    have hr : r < m := by rw [← hleft.1]; exact hrl
    rw [← hgetl r hrl, ← hgetr r hrr] at hlt
    obtain ⟨path, hpath, hearlier⟩ :=
      (key_lt_iff_pathObservation (hleft.2 r hr) (hright.2 r hr)).1 hlt
    refine ⟨r, hr, path, hpath, ?_, hearlier⟩
    intro r' hr' path'
    have hr'm : r' < m := lt_trans hr' hr
    have heq := hbefore r' hr'
    rw [← hgetl r' (by omega), ← hgetr r' (by rw [hright.1]; omega)] at heq
    rw [heq]
  · rintro ⟨r, hr, path, hpath, hrules, hearlier⟩
    have hrl : r < left.length := by rw [hleft.1]; exact hr
    have hrr : r < right.length := by rw [hright.1]; exact hr
    refine ⟨r, hrl, hrr, ?_, ?_⟩
    · intro r' hr'
      rw [← hgetl r' (by omega), ← hgetr r' (by rw [hright.1]; omega)]
      exact (key_eq_iff_pathObservation (hleft.2 r' (by omega)) (hright.2 r' (by omega))).2
        (hrules r' hr')
    · rw [← hgetl r hrl, ← hgetr r hrr]
      exact (key_lt_iff_pathObservation (hleft.2 r hr) (hright.2 r hr)).2 ⟨path, hpath, hearlier⟩

end CanonicalSphereKey
end Certificate
end TetraStereo
