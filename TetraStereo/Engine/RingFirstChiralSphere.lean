import TetraStereo.Engine.RingPathRankTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingFirstChiralSphere

open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingFullPathPairs
open RingPathRankTransport (stepKey_lt stepKey_eq snoc_lt)

/-- Actual edge keys for an ancestor path whose descriptor bits are neutral. -/
def neutral (ds : Path) : Path := ds.map (fun d => stepKey d none)

/-- Neutral encoding retains the complete through-4a priority path. -/
theorem neutral_injective : Function.Injective neutral := by
  intro a b h
  have h' := congrArg (List.map stripBit) h
  simpa [neutral, List.map_map, Function.comp_def, stripBit_step] using h'

/-- Fixed-width edge priorities are compared before the neutral bit appended at each edge. -/
theorem neutral_lt_iff {a b : Path} (same : a.length = b.length)
    (wa : ∀ d ∈ a, d.length = 4) (wb : ∀ d ∈ b, d.length = 4) :
    neutral a < neutral b ↔ a < b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at same
  | cons d ds ih =>
    cases b with
    | nil => simp at same
    | cons e es =>
      have lengths : ds.length = es.length := by simpa using same
      have widths : d.length = e.length := (wa d (by simp)).trans (wb e (by simp)).symm
      have tail := ih lengths (fun x hx => wa x (by simp [hx]))
        (fun x hx => wb x (by simp [hx]))
      simp only [neutral, List.map_cons, List.cons_lt_cons_iff] at *
      rw [stepKey_lt widths, stepKey_eq widths, tail]
      simp

/-- The complete key of a first chiral hit: all ancestor bits neutral, its own bit last. -/
def firstKey (ancestors : Path) (deep : List Word) (bit : Bool) : Path :=
  neutral ancestors ++ [stepKey deep (some bit)]

/-- On one sphere, first chiral hits are ordered by their entire through-4a path, then
by like before unlike within an equal path. Ancestor bits contribute no earlier distinction. -/
theorem firstKey_lt_iff {a b : Path} {d e : List Word} (x y : Bool)
    (same : a.length = b.length)
    (wa : ∀ w ∈ a, w.length = 4) (wb : ∀ w ∈ b, w.length = 4)
    (wd : d.length = 4) (we : e.length = 4) :
    firstKey a d x < firstKey b e y ↔
      a ++ [d] < b ++ [e] ∨ (a ++ [d] = b ++ [e] ∧ x = false ∧ y = true) := by
  have neutralLengths : (neutral a).length = (neutral b).length := by simpa [neutral] using same
  have eqn : neutral a = neutral b ↔ a = b := ⟨fun h => neutral_injective h, congrArg neutral⟩
  have de : d.length = e.length := wd.trans we.symm
  have appendEq : a ++ [d] = b ++ [e] ↔ a = b ∧ d = e := by
    constructor
    · intro h
      obtain ⟨hab, hde⟩ := List.append_inj h same
      exact ⟨hab, by simpa using hde⟩
    · rintro ⟨rfl, rfl⟩; rfl
  rw [firstKey, firstKey, snoc_lt neutralLengths, neutral_lt_iff same wa wb,
    eqn, stepKey_lt de, snoc_lt same, appendEq]
  cases x <;> cases y <;> simp [likeCode]
  all_goals tauto

/-- A descending full key forces descending through-4a priority, and true before false
inside an equal-priority block. -/
theorem firstKey_descending {a b : Path} {d e : List Word} {x y : Bool}
    (same : a.length = b.length)
    (wa : ∀ w ∈ a, w.length = 4) (wb : ∀ w ∈ b, w.length = 4)
    (wd : d.length = 4) (we : e.length = 4)
    (descending : firstKey b e y ≤ firstKey a d x) :
    b ++ [e] ≤ a ++ [d] ∧ (a ++ [d] = b ++ [e] → y = true → x = true) := by
  have noReverse := not_lt_of_ge descending
  constructor
  · apply le_of_not_gt
    intro h
    exact noReverse ((firstKey_lt_iff x y same wa wb wd we).mpr (.inl h))
  · intro equal hy
    cases hx : x with
    | true => rfl
    | false =>
      exact False.elim (noReverse ((firstKey_lt_iff x y same wa wb wd we).mpr
        (.inr ⟨equal, hx, hy⟩)))

private theorem prefix_lt_iff (front a b : Path) :
    front ++ a < front ++ b ↔ a < b := by
  induction front with
  | nil => rfl
  | cons p ps ih =>
    simpa only [List.cons_append, List.cons_lt_cons_iff, lt_self_iff_false,
      true_and, or_false, false_or] using ih

/-- Directly applies to each globally sorted sphere in `FullTrace`. A common root key
is permitted. Each visit in the selected row must be a first chiral hit on that sphere;
neutral ancestors and width four are explicit, checkable path hypotheses. -/
theorem legal_first_chiral_sphere {α : Type} (key : α → Path)
    {children row : List α} (legal : RingStereoSiblingPass.Legal key children row)
    (ancestors : α → Path) (deep : α → List Word) (bit : α → Bool)
    (front : Path) (depth : Nat)
    (shape : ∀ v ∈ row, key v = front ++ firstKey (ancestors v) (deep v) (bit v))
    (sphere : ∀ v ∈ row, (ancestors v).length = depth)
    (widths : ∀ v ∈ row, (∀ w ∈ ancestors v, w.length = 4) ∧ (deep v).length = 4) :
    row.Pairwise (fun v w =>
      ancestors w ++ [deep w] ≤ ancestors v ++ [deep v] ∧
      (ancestors v ++ [deep v] = ancestors w ++ [deep w] → bit w = true → bit v = true)) := by
  have sorted : row.Pairwise (fun v w => key w ≤ key v) := List.pairwise_map.mp legal.descending
  apply List.Pairwise.imp_of_mem (fun {v w} hv hw ordered => ?_) sorted
  have desc : firstKey (ancestors w) (deep w) (bit w) ≤
      firstKey (ancestors v) (deep v) (bit v) := by
    apply le_of_not_gt
    intro reversed
    have bigger : key v < key w := by
      rw [shape v hv, shape w hw]
      exact (prefix_lt_iff _ _ _).mpr reversed
    exact not_lt_of_ge ordered bigger
  exact firstKey_descending ((sphere v hv).trans (sphere w hw).symm)
    (widths v hv).1 (widths w hw).1 (widths v hv).2 (widths w hw).2 desc

end TetraStereo.Engine.RingFirstChiralSphere

assert_kernel_only TetraStereo.Engine.RingFirstChiralSphere.neutral_injective
assert_kernel_only TetraStereo.Engine.RingFirstChiralSphere.neutral_lt_iff
assert_kernel_only TetraStereo.Engine.RingFirstChiralSphere.firstKey_lt_iff
assert_kernel_only TetraStereo.Engine.RingFirstChiralSphere.firstKey_descending
assert_kernel_only TetraStereo.Engine.RingFirstChiralSphere.legal_first_chiral_sphere
