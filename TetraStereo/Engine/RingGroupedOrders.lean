import TetraStereo.Engine.RingGroupedMark

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedOrders
open OneCenter LocalizedGenericMarkedRecalculation
open RingActivePairReport (Slot Score Matrix Ranking)
open RingOrdinaryPairRefusal (score)
open RingSingleTieCompletion (unitScore)
open RingGroupedCentre (Arms)
open RingRetainedChemicalTrace (Word)
attribute [local instance] lexOrd

/-- Append a common Rule 6 word only to a genuine two-geometry tie. An
empty word at every slot gives the ordinary table. -/
def refine (ordinary : Score) (x y : Word) : Score :=
  if ordinary = (0,0) then let k := unitScore (compare x y); (k,k) else ordinary

def refined {r} (m : Matrix r) (w : Slot → Word) (x y : Slot) := refine (m.get x y) (w x) (w y)

def trialMatrix {r} (m : Matrix r) (w : Slot → Word) : Matrix (fun x y => some (refined m w x y)) :=
  ⟨refined m w,fun _ _ _ => rfl⟩

def wins {i f fr read} (a : @Arms i f fr read) (rev : Bool) (w : Slot → Word) (j : Slot) :=
  (a.key rev j,w j)

theorem trial_order {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (rev : Bool)
    (w : Slot → Word) (j k : Slot) :
    compare (score (trialMatrix m w) rev j k) 0 = compare (wins a rev w j) (wins a rev w k) := by
  by_cases ne : j = k
  · subst k; simp [score]
  have before := a.matrix_order m rev j k
  change compare (score _ _ _ _) 0 = (compare (a.key rev j) (a.key rev k)).then (compare (w j) (w k))
  rw [← before]
  obtain ⟨z,allowed,got,_⟩ := a.represented j k
  have val := Option.some.inj ((m.found j k ne).symm.trans got)
  simp only [RingActivePairs.molecularValues,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with h | h | h | h | h <;> cases rev <;> cases compareW : compare (w j) (w k) <;>
    simp [score,trialMatrix,refined,refine,ne,val,h,compareW,unitScore] <;> rfl

theorem shared {i f fr read} (a : @Arms i f fr read) (w : Slot → Word) (j k : Slot) :
    wins a false w j = wins a false w k ↔ wins a true w j = wins a true w k := by
  simp only [wins,Prod.mk.injEq,a.shared_tie]

theorem coherent {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (rev : Bool) (w : Slot → Word) :
    RingChemicalPriority.ReferenceFrame.coherent RingOrdinaryPairRefusal.ids
      (RingOrdinaryPairRefusal.table (trialMatrix m w) rev) false = true :=
  RingSingleTieCompletion.keys_coherent (wins a rev w) _ rev fun j k => by
    rw [RingOrdinaryPairRefusal.read_table,trial_order]

theorem crossings {r} (m : Matrix r) (w : Slot → Word) :
    RingActivePairReport.reversals (trialMatrix m w) = RingActivePairReport.reversals m := by
  apply (List.Perm.refl _).countP_congr
  intro p _
  change (decide (0 < (refine _ _ _).1) != decide (0 < (refine _ _ _).2)) = _
  by_cases z : m.get p.1 p.2 = (0,0)
  · simp [refine,z]
  · simp [refine,z]

theorem doubled_crossings {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) :
    RingActivePairReport.reversals m = RingActivePairReport.doubled m := by
  apply (List.Perm.refl _).countP_congr
  intro p mem
  have different := ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp mem)
  obtain ⟨z,allowed,got,_⟩ := a.represented p.1 p.2
  have val := Option.some.inj ((m.found _ _ different).symm.trans got)
  change (decide (0 < (m.get p.1 p.2).1) != decide (0 < (m.get p.1 p.2).2)) = ((m.get p.1 p.2).1.natAbs == 2)
  rw [val]
  simp only [RingActivePairs.molecularValues,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with h | h | h | h | h <;> rw [h] <;> decide

/-- The ranker returns the unique strict permutation precisely when every
two distinct slots have different priorities. -/
theorem rank_iff {α : Type} [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]
    {r} (m : Matrix r) (rev : Bool) (key : Slot → α)
    (obs : ∀ a b, compare (score m rev a b) 0 = compare (key a) (key b)) :
    (RingActivePairReport.rank? m rev).isSome = true ↔ Function.Injective key := by
  constructor
  · intro ok j k eqn
    let rank := (RingActivePairReport.rank? m rev).get ok
    by_contra ne
    have diff : rank.slots.idxOf j ≠ rank.slots.idxOf k := fun h =>
      ne ((List.idxOf_inj (rank.perm.mem_iff.mpr (by simp : j ∈ List.finRange 4))).mp h)
    have no {a b : Slot} (ab : a ≠ b) (e : key a = key b) (pos : rank.slots.idxOf a < rank.slots.idxOf b) : False := by
      have positive := (rank.before_iff ab).mp pos
      have z := obs a b
      simp only [e,Std.ReflCmp.compare_self] at z
      have zero := Std.compare_eq_eq_iff_eq.mp z
      change 0 < (if rev then (m.get a b).2 else (m.get a b).1) at positive
      simp only [score,if_neg ab] at zero
      omega
    rcases lt_or_gt_of_ne diff with h | h
    · exact no ne eqn h
    · exact no (Ne.symm ne) eqn.symm h
  · intro injective
    let ge := fun (a b : Slot) => (compare (key a) (key b)).isGE
    let sorted := (List.finRange 4).mergeSort ge
    have perm : sorted.Perm (List.finRange 4) := List.mergeSort_perm ..
    have total (a b : Slot) : ge a b || ge b a := by
      unfold ge
      rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := key b) (b := key a)]
      cases compare (key a) (key b) <;> rfl
    have ordered : sorted.Pairwise (fun j k => ge j k = true) :=
      List.pairwise_mergeSort (le := ge) (fun _ _ _ => Std.TransCmp.isGE_trans) total _
    have distinct := perm.nodup_iff.mpr (List.nodup_finRange 4)
    have lawful : sorted.Pairwise (RingActivePairReport.Wins m rev) := by
      apply (List.pairwise_and_iff.mpr (And.intro distinct ordered)).imp
      rintro j k ⟨ne,nonlower⟩
      have gt : compare (key j) (key k) = .gt := by
        cases h : compare (key j) (key k) with
        | lt => exact False.elim ((Ordering.isGE_iff_ne_lt.mp nonlower) h)
        | eq => exact False.elim (ne (injective (Std.compare_eq_eq_iff_eq.mp h)))
        | gt => rfl
      have lt : compare (key k) (key j) = .lt := by rw [Std.OrientedCmp.eq_swap (cmp := compare),gt]; rfl
      have x := Int.compare_eq_gt.mp ((obs j k).trans gt)
      have y := Int.compare_eq_lt.mp ((obs k j).trans lt)
      change 0 < (if rev then (m.get j k).2 else (m.get j k).1) ∧ (if rev then (m.get k j).2 else (m.get k j).1) < 0
      simpa only [score,if_neg ne,if_neg ne.symm] using And.intro x y
    let rank : Ranking m rev := ⟨sorted,perm,lawful⟩
    rw [RingActivePairReport.rank_of rank]; rfl

def marks {i f fr read} (a : @Arms i f fr read) : List Slot :=
  (List.finRange 4).filter fun j => (List.finRange 4).any fun k => j != k && a.key false j == a.key false k

theorem marked_iff {i f fr read} (a : @Arms i f fr read) (s : Slot) (rev : Bool) :
    s ∈ marks a ↔ ∃ t, s ≠ t ∧ a.key rev s = a.key rev t := by
  cases rev <;> simp [marks,bne_iff_ne,a.shared_tie]

/-- The least slot identifies a tie class. It is used only to count
multiplicities and never determines a molecular priority. -/
def representative {i f fr read} (a : @Arms i f fr read) (s : Slot) : Slot :=
  (Finset.univ.filter fun t => a.key false s == a.key false t).min' ⟨s,by simp⟩

theorem representative_iff {i f fr read} (a : @Arms i f fr read) (s t : Slot) (rev : Bool) :
    representative a s = representative a t ↔ a.key rev s = a.key rev t := by
  have member (j : Slot) : a.key false j = a.key false (representative a j) := by
    let cls := Finset.univ.filter fun k : Slot => a.key false j == a.key false k
    have nonempty : cls.Nonempty := ⟨j, by simp [cls]⟩
    have mem : cls.min' nonempty ∈ cls := Finset.min'_mem cls nonempty
    exact beq_iff_eq.mp ((Finset.mem_filter.mp mem).2)
  suffices h : representative a s = representative a t ↔ a.key false s = a.key false t by
    cases rev; exact h; exact h.trans (a.shared_tie s t)
  constructor
  · intro h
    exact (member s).trans ((congrArg (a.key false) h).trans (member t).symm)
  · intro h
    unfold representative
    simp only [h]

theorem partition {i f fr read} (a : @Arms i f fr read) :
    (RingRetainedChemicalPreorder.blockSizes (representative a),(marks a).length) ∈
      ([([1,1,1,1],0),([1,1,2],2),([1,3],3),([2,2],4),([4],4)] : List (List Nat × Nat)) := by
  let eligible (c : Slot → Slot) := (List.finRange 4).filter fun j =>
    (List.finRange 4).any fun k => j != k && c j == c k
  have same : marks a = eligible (representative a) := by
    unfold marks eligible
    apply List.filter_congr
    intro j _
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,representative_iff a _ _ false]
  rw [same]
  have four : ∀ w x y z : Slot, let c : Slot → Slot := ![w,x,y,z]
      (RingRetainedChemicalPreorder.blockSizes c,(eligible c).length) ∈
        ([([1,1,1,1],0),([1,1,2],2),([1,3],3),([2,2],4),([4],4)] : List (List Nat × Nat)) := by decide +kernel
  let c := representative a
  have eta : representative a = ![c 0,c 1,c 2,c 3] := by funext k; fin_cases k <;> rfl
  rw [eta]
  exact four (c 0) (c 1) (c 2) (c 3)

end TetraStereo.Engine.RingGroupedOrders

assert_kernel_only TetraStereo.Engine.RingGroupedOrders.trial_order
assert_kernel_only TetraStereo.Engine.RingGroupedOrders.coherent
assert_kernel_only TetraStereo.Engine.RingGroupedOrders.rank_iff
assert_kernel_only TetraStereo.Engine.RingGroupedOrders.crossings
