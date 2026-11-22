import TetraStereo.Engine.RingChemicalPriority

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.PairSpheres

/-- Bounds for the like/unlike word at a fixed distance, over every possible
hierarchical ordering of the occurrences at that distance. Like is senior. -/
def lower (row : List Bool) : List Nat :=
  List.replicate (row.count false) 0 ++ List.replicate (row.count true) 1

def upper (row : List Bool) : List Nat :=
  List.replicate (row.count true) 1 ++ List.replicate (row.count false) 0

theorem lower_le (row : List Bool) : lower row ≤ row.map Bool.toNat := by
  induction row with
  | nil => exact le_rfl
  | cons b row ih =>
    cases b with
    | false => simpa [lower,List.count_cons,List.replicate_succ] using List.cons_le_cons 0 ih
    | true =>
      cases h : row.count false with
      | zero => simpa [lower,List.count_cons,h,List.replicate_succ] using List.cons_le_cons 1 ih
      | succ n =>
        apply le_of_lt
        simp [lower,h,List.replicate_succ,List.cons_lt_cons_iff]

theorem le_upper (row : List Bool) : row.map Bool.toNat ≤ upper row := by
  induction row with
  | nil => exact le_rfl
  | cons b row ih =>
    cases b with
    | true => simpa [upper,List.count_cons,List.replicate_succ] using List.cons_le_cons 1 ih
    | false =>
      cases h : row.count true with
      | zero => simpa [upper,List.count_cons,h,List.replicate_succ] using List.cons_le_cons 0 ih
      | succ n =>
        apply le_of_lt
        simp [upper,h,List.replicate_succ,List.cons_lt_cons_iff]

abbrev Layers := List (List Bool)
def ranks (rows : Layers) := rows.map (List.map Bool.toNat)

theorem cons_mono {a b : List Nat} {xs ys : List (List Nat)}
    (h : a ≤ b) (t : xs ≤ ys) : a :: xs ≤ b :: ys := by
  rcases lt_or_eq_of_le h with lt | rfl
  · exact le_of_lt (List.cons_lt_cons_iff.mpr (Or.inl lt))
  · exact List.cons_le_cons _ t

/-- Each possible chemical hierarchy retains every pair in its sphere. -/
theorem bounds {rows actual : Layers} (h : List.Forall₂ List.Perm rows actual) :
    rows.map lower ≤ ranks actual ∧ ranks actual ≤ rows.map upper := by
  induction h with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | @cons a b xs ys p _ ih =>
    have lo : lower a = lower b := by simp only [lower,p.count_eq]
    have hi : upper a = upper b := by simp only [upper,p.count_eq]
    exact ⟨cons_mono (lo ▸ lower_le b) ih.1,cons_mono (hi ▸ le_upper b) ih.2⟩

/-- A strict ordering independent of how any tied sphere is linearized.
Overlapping intervals leave the comparison to a more detailed hierarchy. -/
def seniorLeft? (l r : Layers) : Option Bool := do
  guard (l.map List.length == r.map List.length)
  if r.map upper < l.map lower then return true
  if l.map upper < r.map lower then return false
  none

theorem seniorLeft_sound {l r la ra : Layers} {winner : Bool}
    (result : seniorLeft? l r = some winner)
    (lh : List.Forall₂ List.Perm l la) (rh : List.Forall₂ List.Perm r ra) :
    if winner then ranks ra < ranks la else ranks la < ranks ra := by
  by_cases shape : l.map List.length = r.map List.length
  · by_cases first : r.map upper < l.map lower
    · simp [seniorLeft?,shape,first] at result
      subst winner
      exact lt_of_le_of_lt (bounds rh).2 (lt_of_lt_of_le first (bounds lh).1)
    · by_cases second : l.map upper < r.map lower
      · simp [seniorLeft?,shape,first,second] at result
        subst winner
        exact lt_of_le_of_lt (bounds lh).2 (lt_of_lt_of_le second (bounds rh).1)
      · simp [seniorLeft?,shape,first,second] at result
  · simp [seniorLeft?,shape] at result

private def extreme (high : Bool) (row : List Bool) :=
  List.replicate (row.count high) high ++ List.replicate (row.count (!high)) (!high)

private theorem extreme_perm (high : Bool) (row : List Bool) : row.Perm (extreme high row) := by
  rw [List.perm_iff_count]
  intro b
  cases high <;> cases b <;> simp [extreme,List.count_replicate]

private theorem extreme_hierarchy (high : Bool) (rows : Layers) :
    List.Forall₂ List.Perm rows (rows.map (extreme high)) := by
  induction rows with
  | nil => exact .nil
  | cons row _ ih => exact .cons (extreme_perm high row) ih

private theorem ranks_extreme (high : Bool) (rows : Layers) :
    ranks (rows.map (extreme high)) = rows.map (if high then upper else lower) := by
  cases high <;> simp [ranks,List.map_map,Function.comp_def,extreme,lower,upper]

/-- Sharpness: the two endpoints occur as actual within-sphere permutations.
A universally strict preference exists exactly when the two intervals are disjoint
in the indicated direction. Any stronger decision requires molecular hierarchy. -/
theorem strict_for_every_hierarchy_iff (l r : Layers) :
    (∀ la ra, List.Forall₂ List.Perm l la → List.Forall₂ List.Perm r ra → ranks ra < ranks la) ↔
      r.map upper < l.map lower := by
  constructor
  · intro all
    simpa only [ranks_extreme,Bool.false_eq_true,if_false,if_true] using
      all _ _ (extreme_hierarchy false l) (extreme_hierarchy true r)
  · intro gap la ra lh rh
    exact lt_of_le_of_lt (bounds rh).2 (lt_of_lt_of_le gap (bounds lh).1)

end TetraStereo.Engine.RingChemicalPriority.PairSpheres
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.PairSpheres.seniorLeft_sound
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.PairSpheres.strict_for_every_hierarchy_iff
