import TetraStereo.Engine.RingPairSpheres

set_option autoImplicit false
namespace TetraStereo.Engine.RingChemicalPriority.Hierarchy
variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
private theorem filter_split (keep : α → Bool) (xs : List α)
    (sorted : xs.Pairwise (fun a b => keep b = true → keep a = true)) :
    xs.filter keep ++ xs.filter (fun a => !keep a) = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp sorted
    cases h : keep a with
    | true => simpa [h] using congrArg (List.cons a) (ih tail)
    | false =>
      have absent : ∀ x ∈ xs, keep x = false := by
        intro x hx
        cases hxk : keep x with
        | false => rfl
        | true => exact (Bool.noConfusion (h.symm.trans (head x hx hxk)))
      have no : xs.filter keep = [] := List.filter_eq_nil_iff.mpr (by simp_all)
      have all : xs.filter (fun a => !keep a) = xs := List.filter_eq_self.mpr (by simp_all)
      simp [h,no,all]

/-- Any linear order of all occurrences obeying independently established
precedence can only permute members *within* the ordered blocks. No choice
of order, traversal, or serialization inside a block is assumed. -/
theorem split_linearization (higher : α → α → Prop) (irrefl : ∀ a, ¬ higher a a)
    (blocks : List (List α)) (actual : List α)
    (separate : blocks.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, higher a b))
    (complete : blocks.flatten.Perm actual)
    (legal : actual.Pairwise (fun a b => ¬ higher b a)) :
    ∃ order, List.Forall₂ List.Perm blocks order ∧ order.flatten = actual := by
  induction blocks generalizing actual with
  | nil =>
    have empty : actual = [] := List.Perm.eq_nil complete.symm
    exact ⟨[],.nil,empty.symm⟩
  | cons first rest ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp separate
    have senior (a) (ha : a ∈ first) (b) (hb : b ∈ rest.flatten) : higher a b := by
      obtain ⟨r,hr,member⟩ := List.mem_flatten.mp hb
      exact head r hr a ha b member
    have notFirst (b) (hb : b ∈ rest.flatten) : b ∉ first :=
      fun member => irrefl b (senior b member b hb)
    let keep (x : α) := decide (x ∈ first)
    have sorted : actual.Pairwise (fun a b => keep b = true → keep a = true) := by
      apply legal.imp_of_mem
      intro a b ha _ ordered selected
      have hb : b ∈ first := of_decide_eq_true selected
      have mem := complete.mem_iff.mpr ha
      rcases List.mem_append.mp mem with yes | no
      · exact decide_eq_true yes
      · exact (ordered (senior b hb a no)).elim
    have keepFirst : first.filter keep = first := List.filter_eq_self.mpr (by simp [keep])
    have omitRest : rest.flatten.filter keep = [] := List.filter_eq_nil_iff.mpr (by simpa [keep] using notFirst)
    have omitFirst : first.filter (fun x => !keep x) = [] := List.filter_eq_nil_iff.mpr (by simp [keep])
    have keepRest : rest.flatten.filter (fun x => !keep x) = rest.flatten :=
      List.filter_eq_self.mpr (by simpa [keep] using notFirst)
    have front := complete.filter keep
    have back := complete.filter (fun x => !keep x)
    simp only [List.flatten_cons,List.filter_append,keepFirst,omitRest,List.append_nil] at front
    simp only [List.flatten_cons,List.filter_append,omitFirst,keepRest,List.nil_append] at back
    obtain ⟨order,perms,items⟩ := ih _ tail back (legal.filter _)
    exact ⟨actual.filter keep :: order,.cons front perms,by
      simp only [List.flatten_cons,items,filter_split keep actual sorted]⟩

section
omit [DecidableEq α]
theorem append_strict {a b : List Nat} (len : a.length = b.length) (lt : a < b)
    (x y : List Nat) : a ++ x < b ++ y := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons h t ih =>
    cases b with
    | nil => simp at len
    | cons k s =>
      rcases List.cons_lt_cons_iff.mp lt with less | ⟨rfl,tail⟩
      · exact List.cons_lt_cons_iff.mpr (.inl less)
      · exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,ih (by simpa using len) tail⟩)

private theorem prefix_strict (p : List Nat) {a b : List Nat} (h : a < b) : p ++ a < p ++ b := by
  induction p with
  | nil => exact h
  | cons x _ ih => exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,ih⟩)

/-- For blocks of matching lengths the first unequal observation also decides
the complete flattened molecular word. -/
theorem flatten_strict {a b : List (List Nat)} (shape : a.map List.length = b.map List.length)
    (strict : a < b) : a.flatten < b.flatten := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons h t ih =>
    cases b with
    | nil => simp at shape
    | cons k s =>
      obtain ⟨len,tail⟩ := List.cons.inj shape
      rcases List.cons_lt_cons_iff.mp strict with less | ⟨rfl,rest⟩
      · exact append_strict len less _ _
      · exact prefix_strict h (ih tail rest)

end

end TetraStereo.Engine.RingChemicalPriority.Hierarchy
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Hierarchy.split_linearization
