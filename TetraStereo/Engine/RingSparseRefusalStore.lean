import TetraStereo.Engine.RingSphereStore
import Batteries.Tactic.OpenPrivate

/-! Exact compression of sphere stores by omitting known refusals.
Failed evaluations and successful descriptor assignments retain their rows. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSparseRefusalStore
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Rule Cell View)
open RingSphereQueue (viewOf reader stored)
open private row_iff_entry from TetraStereo.Engine.RingSphereStore

variable {i : Input}
abbrev Rows (i : Input) := List (Site i × Cell)

/-- A skipped publication has the same value as an untouched address. -/
def guarded (keep : Site i → Bool) (rule : Rule i) : Rule i :=
  fun q r => if keep q then rule q r else some none

def compact (keep : Site i → Bool) (xs : Rows i) := xs.filter (fun row => keep row.1)

private theorem lookup_cons (p : Site i × Cell) (ps : Rows i) (q : Site i) :
    viewOf (p :: ps) q = if p.1 = q then p.2 else viewOf ps q := by
  by_cases h : p.1 = q <;> simp [viewOf,h]

private theorem filtered_lookup (keep : Site i → Bool) (xs : Rows i) (q : Site i) :
    viewOf (compact keep xs) q = if keep q then viewOf xs q else some none := by
  induction xs with
  | nil => simp [compact,viewOf]
  | cons p ps ih =>
    by_cases h : p.1 = q <;> cases hp : keep p.1 <;> cases hq : keep q <;>
      simp_all [compact,lookup_cons]

private theorem only_refusals (keep : Site i → Bool) (rule : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) (top k : Nat) (q : Site i) (cell : Cell)
    (row : (q,cell) ∈ stored (guarded keep rule) root queue top k) (skip : keep q = false) :
    cell = some none := by
  induction k with
  | zero => simp [stored] at row
  | succ n ih =>
    rw [stored,List.mem_append] at row
    rcases row with new | old
    · obtain ⟨t,_,eq⟩ := List.mem_map.mp new
      cases eq
      simp [guarded,skip]
    · exact ih old

private theorem off_value {xs : Rows i} {q : Site i}
    (absent : ∀ c, (q,c) ∈ xs → c = some none) : viewOf xs q = some none := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    rw [lookup_cons]
    split
    · rename_i eq
      exact absent p.2 (by simp [← eq])
    · exact ih (fun c h => absent c (List.mem_cons_of_mem _ h))

/-- The sparse schedule never calls the primitive rule at the omitted sites. -/
def rows (keep : Site i → Bool) (rule : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) (top k : Nat) :=
  stored rule root (fun d => (queue d).filter keep) top k

private theorem batch (keep : Site i → Bool) (rule : Rule i) (r : View i) (qs : List (Site i)) :
    (qs.filter keep).map (fun q => (q,rule q r)) =
      compact keep (qs.map fun q => (q,guarded keep rule q r)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    cases h : keep q <;> simp [compact,h,guarded] at ih ⊢ <;> exact ih

/-- Simultaneous induction preserves the literal retained rows and every readable address,
even for arbitrary scheduling, repeated visits and non-total primitives. -/
theorem exact_rows (keep : Site i → Bool) (rule : Rule i) (root : i.certified.Atom)
    (queue : Nat → List (Site i)) (top k : Nat) :
    rows keep rule root queue top k = compact keep (stored (guarded keep rule) root queue top k) ∧
    viewOf (rows keep rule root queue top k) = viewOf (stored (guarded keep rule) root queue top k) := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    have step : rows keep rule root queue top (k+1) =
        compact keep (stored (guarded keep rule) root queue top (k+1)) := by
      change ((queue (top-k)).filter keep).map (fun q =>
        (q,rule q (reader root (viewOf (rows keep rule root queue top k))))) ++
        rows keep rule root queue top k = _
      simp only [stored,compact,List.filter_append]
      rw [ih.2]
      exact congrArg₂ List.append (batch keep rule _ _) ih.1
    refine ⟨step,?_⟩
    funext q
    rw [step,filtered_lookup]
    cases h : keep q with
    | true => rfl
    | false =>
      exact (off_value (fun c m => only_refusals keep rule root queue top (k+1) q c m h)).symm


theorem restore {keep : Site i → Bool} {rule : Rule i} {root : i.certified.Atom}
    {queue : Nat → List (Site i)} {top k : Nat}
    (unique : ((stored (guarded keep rule) root queue top k).map Prod.fst).Nodup) :
    ((stored (guarded keep rule) root queue top k).map Prod.fst).map
      (fun q => (q,viewOf (rows keep rule root queue top k) q)) =
      stored (guarded keep rule) root queue top k := by
  rw [(exact_rows ..).2,List.map_map]
  conv_rhs => rw [← List.map_id (stored (guarded keep rule) root queue top k)]
  apply List.map_congr_left
  rintro ⟨q,c⟩ mem
  have found := (row_iff_entry _ unique q c).mp mem
  simp [viewOf,found]

end TetraStereo.Engine.RingSparseRefusalStore
assert_kernel_only TetraStereo.Engine.RingSparseRefusalStore.exact_rows
assert_kernel_only TetraStereo.Engine.RingSparseRefusalStore.restore
