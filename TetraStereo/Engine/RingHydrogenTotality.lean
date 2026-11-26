import TetraStereo.Engine.RingHydrogenCompletion
import TetraStereo.OneCenter.RawHydrogenExpansionClosure

set_option autoImplicit false

namespace TetraStereo.Engine.RingHydrogenCompletion

open OneCenter


theorem plan_parent_lt (m : RawMolecule) {e : Nat × Nat} (he : e ∈ plan m) :
    e.1 < m.atomCount := by
  obtain ⟨i, hi, h⟩ := List.mem_filterMap.mp he
  unfold plan at he
  split at h
  · cases h
  · cases Option.some.inj h
    exact List.mem_range.mp hi

private theorem mapM_positions_exists (ps : List Point) (ids : List Nat)
    (bounded : ∀ j ∈ ids, j < ps.length) :
    ∃ points, ids.mapM (fun j => ps[j]?) = some points := by
  induction ids with
  | nil => exact ⟨[], rfl⟩
  | cons i rest ih =>
    obtain ⟨tail, ht⟩ := ih (fun j hj => bounded j (by simp [hj]))
    have hi := bounded i (by simp)
    refine ⟨ps[i] :: tail, ?_⟩
    simp [List.mapM_cons, List.getElem?_eq_getElem hi, ht]

/-- Full original coordinates make placement total for every planned parent. -/
theorem placeAt?_exists (m : RawMolecule) (xyz : SpatialConfiguration)
    (full : xyz.positions.length = m.atomCount) {e : Nat × Nat} (he : e ∈ plan m) :
    ∃ ps, placeAt? m xyz e = some ps ∧ ps.length = e.2 := by
  have hp : e.1 < xyz.positions.length := by rw [full]; exact plan_parent_lt m he
  obtain ⟨ps, hps⟩ := mapM_positions_exists xyz.positions (neighbors m e.1) (by
    intro j hj
    rw [full]
    exact List.mem_range.mp (List.mem_filter.mp hj).1)
  unfold placeAt?
  simp only [List.getElem?_eq_getElem hp, hps]
  dsimp only [Bind.bind, Option.bind]
  split
  · rename_i h
    have one : e.2 = 1 := by simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
    split
    · split
      · exact ⟨_, rfl, by simp [one]⟩
      · exact ⟨_, rfl, placed_length _ _ _⟩
    · exact ⟨_, rfl, placed_length _ _ _⟩
  · exact ⟨_, rfl, placed_length _ _ _⟩

private theorem placements_exists (m : RawMolecule) (xyz : SpatialConfiguration)
    (entries : List (Nat × Nat))
    (available : ∀ e ∈ entries, ∃ ps, placeAt? m xyz e = some ps ∧ ps.length = e.2) :
    ∃ blocks, entries.mapM (placeAt? m xyz) = some blocks ∧
      blocks.flatten.length = (entries.flatMap (fun e => List.replicate e.2 e.1)).length := by
  induction entries with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons e rest ih =>
    obtain ⟨ps, hps, length⟩ := available e (by simp)
    obtain ⟨blocks, hb, hl⟩ := ih (fun e he => available e (by simp [he]))
    refine ⟨ps :: blocks, ?_, ?_⟩
    · simp [List.mapM_cons, hps, hb]
    · simp [List.flatten_cons, length, hl]

/-- Coordinate generation never refuses when every original atom has a position;
it produces exactly one position for each added hydrogen. -/
theorem addedPositions?_exists (m : RawMolecule) (xyz : SpatialConfiguration)
    (full : xyz.positions.length = m.atomCount) :
    ∃ extra, addedPositions? m xyz = some extra ∧ extra.length = (addedParents m).length := by
  obtain ⟨blocks, hb, hl⟩ := placements_exists m xyz (plan m)
    (fun _ he => placeAt?_exists m xyz full he)
  exact ⟨blocks.flatten, by simp [addedPositions?, hb], hl⟩

/-- The structural candidate always exists on complete coordinates. Its positions retain the
entire original coordinate prefix. This statement concerns construction before the certificate gate. -/
theorem candidate?_exists (m : RawMolecule) (xyz : SpatialConfiguration)
    (full : xyz.positions.length = m.atomCount) :
    ∃ out pos, candidate? m xyz = some (out, pos) ∧
      pos.positions.take m.atomCount = xyz.positions := by
  by_cases empty : (plan m).isEmpty = true
  · exact ⟨m, xyz, by simp [candidate?, empty], by simp [← full]⟩
  · obtain ⟨extra, h, _⟩ := addedPositions?_exists m xyz full
    refine ⟨(closeHydrogenVertices m).withExplicitHydrogens, { positions := xyz.positions ++ extra }, ?_, ?_⟩
    · simp [candidate?, empty, h]
    · simp [← full]


/-- Suppressing attached hydrogens at hydrogen vertices leaves a closed graph closed. -/
theorem plan_eq_nil_of_hydrogenClosed (m : RawMolecule) (closed : m.HydrogenClosed) :
    plan m = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry he
  obtain ⟨i, hi, h⟩ := List.mem_filterMap.mp he
  have bound := List.mem_range.mp hi
  obtain ⟨a, ha⟩ := listGet?_exists_of_lt m.atoms i bound
  have before : m.atomAt? i = some a := ha
  have after : (closeHydrogenVertices m).atomAt? i = some (closeAtom a) := by
    rw [atomAt?_eq_getElem?, closeHydrogenVertices, List.getElem?_map, ← atomAt?_eq_getElem?, before]
    rfl
  have zero := closed i bound
  have gone : missing m i = 0 := by
    simp only [missing, RawMolecule.hydrogenCountAt, after, before] at zero ⊢
    by_cases hydrogen : a.element = Element.H
    · simp [closeAtom, hydrogen]
    · simpa [closeAtom, hydrogen, closeHydrogenVertices, RawMolecule.incidentBondOrderSum] using zero
  simp [gone] at h


theorem candidate?_closed {m out : RawMolecule} {g pos : SpatialConfiguration}
    (h : candidate? m g = some (out,pos)) : plan out = [] := by
  unfold candidate? at h
  split at h
  · rename_i empty
    cases h
    simpa using empty
  · obtain ⟨extra, _, eqn⟩ := Option.map_eq_some_iff.mp h
    cases eqn
    exact plan_eq_nil_of_hydrogenClosed _ (RawHydrogenExpansionClosure.hydrogenClosed_withExplicitHydrogens _)

theorem prepare?_closed {m out : RawMolecule} {g pos : SpatialConfiguration}
    (h : prepare? m g = some (out,pos)) : plan out = [] := by
  obtain ⟨⟨m',g'⟩, cand, passed⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨eqn,_⟩ := gate_eq_some passed
  cases eqn
  exact candidate?_closed cand

end TetraStereo.Engine.RingHydrogenCompletion

assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.plan_parent_lt
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.placeAt?_exists
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.addedPositions?_exists
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.candidate?_exists
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.prepare?_closed
