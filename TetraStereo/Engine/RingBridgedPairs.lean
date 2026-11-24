import TetraStereo.Engine.RingOrientation

set_option autoImplicit false

namespace TetraStereo.Engine.RingBridgedPairs
open OneCenter
open RingActivePairReport (Slot)
open RingGroupedCentre (Arms)
open RingRetainedChemicalTrace (Word)
open RingGroupedOrders (marks wins)
attribute [local instance] lexOrd

/-- An ordered presentation of two tied, strictly separated ordinary classes. -/
structure Pairs {i f fr read} (arms : @Arms i f fr read) where
  a : Slot
  b : Slot
  c : Slot
  d : Slot
  frame : [a,b,c,d].Perm (List.finRange 4)
  senior : arms.key false a = arms.key false b
  junior : arms.key false c = arms.key false d
  blocks : compare (arms.key false a) (arms.key false c) = .gt

/-- A surviving tie contributes zero. Two strict comparisons have the reference
hand if their preferences agree and its opposite if they disagree. -/
def contribution (p q : Ordering) : Int :=
  if p = .eq ∨ q = .eq then 0 else if p = q then 1 else -1

private def model (p q : Ordering) : Nat → Nat
  | 0 => if p = .lt then 2 else 3
  | 1 => if p = .gt then 2 else 3
  | 2 => if q = .lt then 0 else 1
  | _ => if q = .gt then 0 else 1

private theorem orientation_congr {α β : Type} [Ord α] [Ord β] (u : Slot → α) (v : Slot → β)
    (same : ∀ j k, compare (u j) (u k) = compare (v j) (v k)) :
    RingOrientation.orientation u = RingOrientation.orientation v := by
  unfold RingOrientation.orientation
  simp_rw [same]

private theorem slot_mem {a b c d : Slot} (h : [a,b,c,d].Perm (List.finRange 4)) (k : Slot) :
    k = a ∨ k = b ∨ k = c ∨ k = d := by simpa using h.mem_iff.mpr (List.mem_finRange k)

private theorem exhaustive {i f fr read arms} (p : @Pairs i f fr read arms) :
    marks arms = List.finRange 4 := by
  have distinct := p.frame.nodup_iff.mpr (List.nodup_finRange 4)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at distinct
  have all (s : Slot) : s ∈ marks arms := by
    apply (RingGroupedOrders.marked_iff arms s false).mpr
    rcases slot_mem p.frame s with h | h | h | h <;> subst s
    · exact ⟨_,distinct.1.1,p.senior⟩
    · exact ⟨_,Ne.symm distinct.1.1,p.senior.symm⟩
    · exact ⟨_,distinct.2.2.1,p.junior⟩
    · exact ⟨_,Ne.symm distinct.2.2.1,p.junior.symm⟩
  apply List.filter_eq_self.mpr
  intro s _
  exact (List.mem_filter.mp (all s)).2

/-- This sign only accounts for writing the two senior directions first and
the junior directions second in the frame. -/
def Pairs.sign {i f fr read arms} (p : @Pairs i f fr read arms) : Int :=
  if RawMolecule.permutationIsEven ([p.a,p.b,p.c,p.d].map Fin.val) then 1 else -1

private theorem model_sign : ∀ ss ∈ (List.finRange 4).permutations', ∀ l r : Ordering,
    RingOrientation.orientation (fun s => model l r (ss.idxOf s)) =
      (if RawMolecule.permutationIsEven (ss.map Fin.val) then 1 else -1) * contribution l r := by
  decide +kernel

theorem Pairs.orientation {i f fr read arms} (p : @Pairs i f fr read arms) (w : Slot → Word) :
    RingOrientation.orientation (wins arms false w) = p.sign *
      contribution (compare (w p.a) (w p.b)) (compare (w p.c) (w p.d)) := by
  let ss := [p.a,p.b,p.c,p.d]
  let l := compare (w p.a) (w p.b)
  let r := compare (w p.c) (w p.d)
  apply Eq.trans _ (model_sign ss (List.mem_permutations'.mpr p.frame) l r)
  apply orientation_congr
  have nd := p.frame.nodup_iff.mpr (List.nodup_finRange 4)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at nd
  have i0 : ss.idxOf p.a = 0 := by simp [ss]
  have i1 : ss.idxOf p.b = 1 := by simp [ss,nd.1.1]
  have i2 : ss.idxOf p.c = 2 := by simp [ss,nd.1.2.1,nd.2.1.1]
  have i3 : ss.idxOf p.d = 3 := by simp [ss,nd.1.2.2,nd.2.1.2,nd.2.2.1]
  have opposite {α : Type} [Ord α] [Std.OrientedOrd α] (x y : α) :
      compare y x = (compare x y).swap := Std.OrientedCmp.eq_swap ..
  have prod (j k : Slot) : compare (wins arms false w j) (wins arms false w k) =
      (compare (arms.key false j) (arms.key false k)).then (compare (w j) (w k)) := rfl
  have separated : compare (arms.key false p.c) (arms.key false p.a) = .lt := by
    rw [opposite _ _,p.blocks]; rfl
  have lw := opposite (w p.a) (w p.b)
  have rw' := opposite (w p.c) (w p.d)
  intro j k
  rcases slot_mem p.frame j with h | h | h | h <;> subst j <;>
    rcases slot_mem p.frame k with h | h | h | h <;> subst k <;>
    simp only [prod,← p.senior,← p.junior,p.blocks,separated,Std.ReflCmp.compare_self,Ordering.eq_then,
      Ordering.gt_then,Ordering.lt_then,i0,i1,i2,i3,l,r,lw,rw'] <;>
    cases hl : compare (w p.a) (w p.b) <;> cases hr : compare (w p.c) (w p.d) <;> decide

def Pairs.coupling {i f fr read arms} (p : @Pairs i f fr read arms) (s : Slot) : Int :=
  let w := RingOrientation.markedWord fr read s
  contribution (compare (w p.a) (w p.b)) (compare (w p.c) (w p.d))

/-- The four marked path comparisons characterize both success and refusal,
including partial survival and exact cancellation in a bridged ring. -/
theorem Pairs.index {i f fr read arms} (p : @Pairs i f fr read arms) :
    RingOrientation.index arms = p.sign * ((List.finRange 4).map p.coupling).sum := by
  simp only [RingOrientation.index,exhaustive p,List.length_finRange,show ¬ (4 < 3) by decide,if_false]
  have each (s : Slot) := p.orientation (RingOrientation.markedWord fr read s)
  simp only [each]
  change ((List.finRange 4).map (fun s => p.sign * p.coupling s)).sum = _
  exact List.sum_map_mul_left ..

theorem Pairs.refusal_iff {i f fr read arms m} (p : @Pairs i f fr read arms)
    (decision : RingGroupedTrials.Decision arms m) (ready : RingGroupedStereo.Ready f read)
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    decision.letters = none ↔ ((List.finRange 4).map p.coupling).sum = 0 := by
  rw [RingOrientation.refusal_iff decision ready coords,p.index,mul_eq_zero]
  have nz : p.sign ≠ 0 := by unfold Pairs.sign; split <;> decide
  simp [nz]

end TetraStereo.Engine.RingBridgedPairs
assert_kernel_only TetraStereo.Engine.RingBridgedPairs.Pairs.refusal_iff
