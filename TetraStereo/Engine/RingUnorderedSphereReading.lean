import TetraStereo.Engine.RingFullPathPairs

/-! Unordered complete spheres, with ordering confined to visible keys. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingUnorderedSphereReading
open RingStereoSiblingPass
open private mapM_perm from TetraStereo.Engine.RingActivePairs

/-- Expand every occurrence, including occurrences which emit no bit. -/
def layers? {α : Type} (next : α → Option (List α)) :
    Nat → List α → Option (List (List α))
  | _, [] => some []
  | 0, _::_ => none
  | n+1, x::xs => do
    let blocks ← (x::xs).mapM next
    return (x::xs) :: (← layers? next n blocks.flatten)

/-- Only visible keys are sorted; neutral occurrences remain in the traversal. -/
def readRow {α κ : Type} [LinearOrder κ] (key : α → κ) (see : κ → Option Bool)
    (row : List α) : List Bool :=
  (order id ((row.map key).filter fun k => (see k).isSome)).filterMap see

private theorem order_perm {κ : Type} [LinearOrder κ] {xs ys : List κ} (p : xs.Perm ys) :
    order id xs = order id ys := by
  have a := legal_order id xs
  have b := legal_order id ys
  simpa using List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
    a.descending b.descending (((a.perm.trans p).trans b.perm.symm).map id)

theorem readRow_perm {α κ : Type} [LinearOrder κ] (key : α → κ) (see : κ → Option Bool)
    {xs ys : List α} (p : xs.Perm ys) : readRow key see xs = readRow key see ys := by
  unfold readRow
  rw [order_perm ((p.map key).filter _)]

theorem readRow_map {α β κ : Type} [LinearOrder κ] (image : α → β)
    (key : β → κ) (see : κ → Option Bool) (row : List α) :
    readRow (key ∘ image) see row = readRow key see (row.map image) := by
  simp [readRow,List.map_map,Function.comp_def]

theorem readRow_filter {α κ : Type} [LinearOrder κ] (key : α → κ)
    (see : κ → Option Bool) (row : List α) :
    readRow key see (row.filter fun x => (see (key x)).isSome) = readRow key see row := by
  unfold readRow
  congr 2
  induction row with
  | nil => rfl
  | cons x xs ih =>
    cases h : see (key x) <;> simp_all

private theorem filterMap_visible {κ : Type} (see : κ → Option Bool) (xs : List κ) :
    (xs.filter fun k => (see k).isSome).filterMap see = xs.filterMap see := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : see x <;> simp [h,ih]

private theorem readRow_sorted {β κ : Type} [LinearOrder κ] (key : β → κ)
    (see : κ → Option Bool) (row : List β) (sorted : (row.map key).Pairwise (· ≥ ·)) :
    readRow key see row = row.filterMap (see ∘ key) := by
  unfold readRow
  have eqn : order id ((row.map key).filter fun k => (see k).isSome) =
      (row.map key).filter fun k => (see k).isSome := by
    have a := legal_order id ((row.map key).filter fun k => (see k).isSome)
    have s := sorted.filter (fun k => (see k).isSome)
    simpa using List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
      a.descending (by simpa using s) (a.perm.map id)
  rw [eqn,filterMap_visible]
  simp

private theorem mapM_image {α β : Type} (image : α → β)
    (edges : α → Option (List α)) (next : β → Option (List β))
    (commute : ∀ x, (edges x).map (List.map image) = next (image x)) (row : List α) :
    (row.mapM edges).map (List.map (List.map image)) = (row.map image).mapM next := by
  induction row with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,List.map_cons]
    rw [← commute x,← ih]
    cases edges x <;> cases xs.mapM edges <;> rfl

private theorem read_rows {α β κ : Type} [LinearOrder κ]
    (image : α → β) (key : β → κ) (see : κ → Option Bool)
    (edges : α → Option (List α)) (next : β → Option (List β))
    (commute : ∀ x, (edges x).map (List.map image) = next (image x)) :
    ∀ n row row', (row.map image).Perm row' → (row'.map key).Pairwise (· ≥ ·) →
      (layers? edges n row).map (fun layers => layers.flatMap (readRow (key ∘ image) see)) =
      (RingFullPathPairs.sphereRun key next n row').map (List.filterMap (see ∘ key)) := by
  intro n
  induction n with
  | zero =>
    intro row row' perm sorted
    cases row with
    | nil => obtain rfl := perm.symm.eq_nil; rfl
    | cons x xs =>
      cases row' with
      | nil => simp at perm
      | cons y ys => rfl
  | succ n ih =>
    intro row row' perm sorted
    cases row with
    | nil => obtain rfl := perm.symm.eq_nil; rfl
    | cons x xs =>
      cases row' with
      | nil => simp at perm
      | cons y ys =>
        have mapped := mapM_image image edges next commute (x::xs)
        cases hb : (x::xs).mapM edges with
        | none =>
          have hn : (y::ys).mapM next = none := by
            cases hn : (y::ys).mapM next with
            | none => rfl
            | some bs =>
              obtain ⟨cs,hc,_⟩ := mapM_perm perm hn
              simp only [hb,Option.map_none] at mapped
              rw [← mapped] at hc
              contradiction
          simp [layers?,RingFullPathPairs.sphereRun,hb,hn]
        | some bs =>
          have hm : ((x::xs).map image).mapM next = some (bs.map (List.map image)) := by
            rw [hb] at mapped
            exact mapped.symm
          obtain ⟨cs,hc,pc⟩ := mapM_perm perm.symm hm
          have fp : (bs.flatten.map image).Perm (order key cs.flatten) := by
            have p := pc.symm.flatten
            rw [← List.map_flatten] at p
            exact p.trans (legal_order key cs.flatten).perm.symm
          have tail := ih bs.flatten (order key cs.flatten) fp (legal_order key cs.flatten).descending
          have head : readRow (key ∘ image) see (x::xs) =
              (y::ys).filterMap (see ∘ key) := by
            rw [readRow_map,readRow_perm key see perm,readRow_sorted key see _ sorted]
          simp only [layers?,RingFullPathPairs.sphereRun,hb,hc]
          cases hl : layers? edges n bs.flatten <;>
            cases hr : RingFullPathPairs.sphereRun key next n (order key cs.flatten) <;>
            cases hv : see (key y) <;> simp_all [List.filterMap_append]

/-- Mapping a walker and sorting complete spheres gives the same visible reading.
All expansion failures and the exact depth budget are retained. -/
theorem read_exact {α β κ : Type} [LinearOrder κ]
    (image : α → β) (key : β → κ) (see : κ → Option Bool)
    (edges : α → Option (List α)) (next : β → Option (List β))
    (commute : ∀ x, (edges x).map (List.map image) = next (image x)) (x : α) (n : Nat) :
    (layers? edges n [x]).map (fun layers => layers.flatMap (readRow (key ∘ image) see)) =
      (RingFullPathPairs.sphereRun key next n [image x]).map (List.filterMap (see ∘ key)) :=
  read_rows image key see edges next commute n [x] [image x] (List.Perm.refl _) (by simp)

end TetraStereo.Engine.RingUnorderedSphereReading

assert_kernel_only TetraStereo.Engine.RingUnorderedSphereReading.read_exact
