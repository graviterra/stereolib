import TetraStereo.Engine.RingRetainedStereoDecision

set_option autoImplicit false

namespace TetraStereo.Engine.RingSeedEqualityTransport
open RingStereoSiblingPass

/-- Compare two FIFO runs with the same earlier child priorities. An accepted
bit locates the hand on an uppercase vertex. All other vertices still occupy
their positions in the queue. Recover the opposite-seed value at each parent
after its children have been recovered. -/
theorem transport {α κ β : Type} {legal : α → List α → List α → Prop}
    (prior : α → κ) (bit : α → Option Bool) (other : α → β)
    (node : ∀ a b sa da sb db, legal a sa da → legal b sb db → prior a = prior b →
      da.map prior = db.map prior ∧ (bit a).isSome = (bit b).isSome ∧
      (bit a = bit b → da.map other = db.map other → other a = other b))
    {xs ys out} (left : Visits legal xs ys out) :
    ∀ {us vs word}, Visits legal us vs word → xs.map prior = us.map prior → ys.map prior = vs.map prior →
      (out.filterMap bit).length = (word.filterMap bit).length ∧
      (out.filterMap bit = word.filterMap bit → xs.map other = us.map other ∧ ys.map other = vs.map other) := by
  induction left with
  | stop =>
    intro us vs word right xeq yeq
    have hu : us = [] := by simpa using xeq.symm
    have hv : vs = [] := by simpa using yeq.symm
    subst us; subst vs; cases right
    exact ⟨rfl,fun _ => ⟨rfl,rfl⟩⟩
  | @rotate a xs out next ih =>
    intro us vs word right xeq yeq
    have hu : us = [] := by simpa using xeq.symm
    subst us
    cases right with
    | stop => simp at yeq
    | rotate w =>
      obtain ⟨sizes,restore⟩ := ih w yeq rfl
      exact ⟨sizes,fun eqn => ⟨rfl,(restore eqn).1⟩⟩
  | @pop a xs ys sa da out la next ih =>
    intro us vs word right xeq yeq
    cases right with
    | stop | rotate => simp at xeq
    | @pop b us vs sb db word lb more =>
      obtain ⟨head,tail⟩ := List.cons.inj xeq
      obtain ⟨children,occupied,recover⟩ := node a b sa da sb db la lb head
      obtain ⟨size,restore⟩ := ih more tail (by simp only [List.map_append,yeq,children])
      have prefixSize : (ys.map other).length = (vs.map other).length := by
        simpa using congrArg List.length yeq
      have finish (h : bit a = bit b) (rest : out.filterMap bit = word.filterMap bit) :
          (a :: xs).map other = (b :: us).map other ∧ ys.map other = vs.map other := by
        obtain ⟨ts,full⟩ := restore rest
        simp only [List.map_append] at full
        have old := List.append_inj_left full prefixSize
        rw [old] at full
        exact ⟨congrArg₂ List.cons (recover h (List.append_cancel_left full)) ts,old⟩
      cases ha : bit a <;> cases hb : bit b <;> simp_all

end TetraStereo.Engine.RingSeedEqualityTransport

assert_kernel_only TetraStereo.Engine.RingSeedEqualityTransport.transport
