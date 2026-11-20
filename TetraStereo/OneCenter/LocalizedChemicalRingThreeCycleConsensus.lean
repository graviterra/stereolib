import TetraStereo.OneCenter.LocalizedChemicalRingFixedParentParity
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! On the three outward slots, an even nontrivial fixed-parent action is transitive.
If actual reading transport supplies invariance under that action, all eligible readings
agree, including absence. Thus disagreement of successful readings is impossible, and
consensus refusal reduces to a failed reading. Reading invariance is an explicit premise
of this finite algebra; the physical residual-reading transport supplies it separately. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus

open LocalizedGenericMarkedRecalculation (consensus)
open LocalizedChemicalRingSenseTransport (consensus_eq_some_iff)

/-- Changing frame slots preserves the even sign forced by an action of order dividing three. -/
theorem sign_one_of_conjugate_cube (frame p : Equiv.Perm (Fin 4))
    (cube : ((frame.trans p).trans frame.symm) ^ 3 = 1) : p.sign = 1 := by
  have finite : ∀ (frame p : Equiv.Perm (Fin 4)),
      ((frame.trans p).trans frame.symm) ^ 3 = 1 → p.sign = 1 := by
    decide +kernel
  exact finite frame p cube

/-- A proper invariant population with at least two slots must be the moving orbit.
This form avoids choosing the incoming slot in advance. -/
theorem eligible_orbit (p : Equiv.Perm (Fin 4)) (cube : p ^ 3 = 1) (nontrivial : p ≠ 1)
    (eligible : Finset (Fin 4)) (proper : ∃ i, i ∉ eligible)
    (two : ∃ i ∈ eligible, ∃ j ∈ eligible, i ≠ j)
    (closed : ∀ i ∈ eligible, p i ∈ eligible) :
    ∃ parent, p parent = parent ∧ (∀ i, i ≠ parent → p i ≠ i) ∧
      ∀ i ∈ eligible, i ≠ parent := by
  have finite : ∀ (p : Equiv.Perm (Fin 4)) (eligible : Finset (Fin 4)),
      p ^ 3 = 1 → p ≠ 1 → (∃ i, i ∉ eligible) →
      (∃ i ∈ eligible, ∃ j ∈ eligible, i ≠ j) → (∀ i ∈ eligible, p i ∈ eligible) →
      ∃ parent, p parent = parent ∧ (∀ i, i ≠ parent → p i ≠ i) ∧
        ∀ i ∈ eligible, i ≠ parent := by
    decide +kernel
  exact finite p eligible cube nontrivial proper two closed

theorem outward_orbit (p : Equiv.Perm (Fin 4)) (parent : Fin 4)
    (fixed : p parent = parent) (moved : ∀ i, i ≠ parent → p i ≠ i)
    (i j : Fin 4) (iOut : i ≠ parent) (jOut : j ≠ parent) :
    j = i ∨ j = p i ∨ j = p (p i) := by
  have finite : ∀ (p : Equiv.Perm (Fin 4)) (parent : Fin 4),
      p parent = parent → (∀ i, i ≠ parent → p i ≠ i) →
      ∀ i j, i ≠ parent → j ≠ parent → j = i ∨ j = p i ∨ j = p (p i) := by
    decide +kernel
  exact finite p parent fixed moved i j iOut jOut

theorem readings_eq {α : Type*} (p : Equiv.Perm (Fin 4)) (parent : Fin 4)
    (fixed : p parent = parent) (moved : ∀ i, i ≠ parent → p i ≠ i)
    (reading : Fin 4 → α) (transport : ∀ i, reading (p i) = reading i)
    (i j : Fin 4) (iOut : i ≠ parent) (jOut : j ≠ parent) :
    reading j = reading i := by
  rcases outward_orbit p parent fixed moved i j iOut jOut with same | same | same
  · rw [same]
  · rw [same, transport]
  · rw [same, transport, transport]

/-- Any nonempty eligible subpopulation outside the parent gives the same consensus,
without requiring success of any reading. -/
theorem consensus_eq_reading (p : Equiv.Perm (Fin 4)) (parent : Fin 4)
    (fixed : p parent = parent) (moved : ∀ i, i ≠ parent → p i ≠ i)
    (reading : Fin 4 → Option RS) (transport : ∀ i, reading (p i) = reading i)
    (eligible : List (Fin 4)) (nonempty : eligible ≠ [])
    (outside : ∀ i ∈ eligible, i ≠ parent) (i : Fin 4) (iOut : i ≠ parent) :
    consensus (eligible.map reading) = reading i := by
  have same : ∀ j ∈ eligible, reading j = reading i :=
    fun j member => readings_eq p parent fixed moved reading transport i j iOut (outside j member)
  cases readAt : reading i with
  | none =>
      obtain ⟨j, member⟩ := List.exists_mem_of_ne_nil eligible nonempty
      cases result : consensus (eligible.map reading) with
      | none => rfl
      | some answer =>
          have all := ((consensus_eq_some_iff _ _).mp result).2
          have impossible := all (reading j) (List.mem_map.mpr ⟨j, member, rfl⟩)
          rw [same j member, readAt] at impossible
          cases impossible
  | some answer =>
      apply (consensus_eq_some_iff _ _).mpr
      refine ⟨?_, ?_⟩
      · cases eligible with
        | nil => exact False.elim (nonempty rfl)
        | cons head tail => simp
      · intro entry entryMem
        obtain ⟨j, jMem, rfl⟩ := List.mem_map.mp entryMem
        exact (same j jMem).trans readAt

theorem no_successful_disagreement (p : Equiv.Perm (Fin 4)) (parent : Fin 4)
    (fixed : p parent = parent) (moved : ∀ i, i ≠ parent → p i ≠ i)
    (reading : Fin 4 → Option RS) (transport : ∀ i, reading (p i) = reading i)
    (i j : Fin 4) (iOut : i ≠ parent) (jOut : j ≠ parent)
    (a b : RS) (first : reading i = some a) (second : reading j = some b) : a = b := by
  have equal := readings_eq p parent fixed moved reading transport i j iOut jOut
  rw [first, second, Option.some.injEq] at equal
  exact equal.symm

end TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus.outward_orbit
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus.sign_one_of_conjugate_cube
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus.eligible_orbit
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus.readings_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus.consensus_eq_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus.no_successful_disagreement
