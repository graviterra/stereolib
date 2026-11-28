import TetraStereo.Engine.RingBinaryPairScore

/-! Two paths may visit the same chiral donors in opposite order with every
hand reversed. Classify their native Rule 4b and Rule 5 comparisons at any
length, including the empty path and ties passed on to a nomination. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOppositeHandSequences
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
attribute [local instance] lexOrd

/-- A bit records whether the donor has hand R. Changing the reference
complements every bit. -/
def complement (w : List Bool) := w.map Bool.not
def paired (w : List Bool) := max w (complement w)
def opposite (w : List Bool) := complement w.reverse

@[simp] theorem complement_twice (w : List Bool) : complement (complement w) = w := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp_all [complement]

@[simp] theorem paired_complement (w : List Bool) : paired (complement w) = paired w := by
  simp [paired,max_comm]

theorem paired_eq_iff (a b : List Bool) : paired a = paired b ↔ a = b ∨ a = complement b := by
  constructor
  · intro eqn
    rcases max_choice a (complement a) with A|A <;> rcases max_choice b (complement b) with B|B <;>
      change max a (complement a) = max b (complement b) at eqn <;> rw [A,B] at eqn
    · exact Or.inl eqn
    · exact Or.inr eqn
    · exact Or.inr (by simpa using congrArg complement eqn)
    · exact Or.inl (by simpa using congrArg complement eqn)
  · rintro (rfl|rfl) <;> simp

/-- Rule 4b ties precisely when reversing the sequence preserves all
hands, or reverses every hand. -/
theorem fourB_tie (w : List Bool) :
    paired w = paired (opposite w) ↔ w = w.reverse ∨ w = opposite w := by
  rw [paired_eq_iff]
  simp only [opposite,complement_twice,or_comm]

/-- After earlier equal fields, the native trial compares these two signed
stages and then the actual mark. This formula preserves exact ties. -/
theorem trial (a b : List Bool) (x y : Key)
    (prior : x.throughFourA = y.throughFourA) (lower : x.fourC = y.fourC)
    (ax : x.bestFourB = paired a) (ay : y.bestFourB = paired b)
    (fx : x.fixedR = a) (fy : y.fixedR = b) (m n : RingRetainedChemicalTrace.Word) :
    compare (trialKey x m) (trialKey y n) =
      (compare (paired a) (paired b)).then ((compare a b).then (compare m n)) := by
  simp only [trialKey,prior,lower,ax,ay,fx,fy,List.compare_cons_cons,
    RingBinaryPairScore.compare_bits,Std.ReflOrd.compare_self,Ordering.eq_then]
  cases compare (paired a) (paired b) <;> cases compare a b <;> cases compare m n <;> rfl

/-- For opposite traversals, either the first unequal paired sequence wins,
Rule 5 selects the first donor's hand, or the mark alone decides. -/
theorem classify (w : List Bool) (mark : Ordering) :
    (compare (paired w) (paired (opposite w))).then ((compare w (opposite w)).then mark) =
      if w = opposite w then mark else if w = w.reverse then
        (if w.head? = some true then .gt else .lt)
      else compare (paired w) (paired (opposite w)) := by
  by_cases anti : w = opposite w
  · rw [if_pos anti]
    have equal := (fourB_tie w).2 (Or.inr anti)
    rw [equal,Std.ReflOrd.compare_self,Ordering.eq_then]
    rw [Std.compare_eq_eq_iff_eq.mpr anti]
    rfl
  rw [if_neg anti]
  by_cases pal : w = w.reverse
  · rw [if_pos pal,(fourB_tie w).2 (Or.inl pal),Std.ReflOrd.compare_self,Ordering.eq_then]
    have fixed : opposite w = complement w := congrArg complement pal.symm
    rw [fixed]
    cases w with
    | nil => exact (anti rfl).elim
    | cons h t => cases h <;> rfl
  · rw [if_neg pal]
    have neq : paired w ≠ paired (opposite w) := fun eqn => ((fourB_tie w).1 eqn).elim pal anti
    cases c : compare (paired w) (paired (opposite w)) with
    | lt => rfl
    | gt => rfl
    | eq => exact (neq (Std.compare_eq_eq_iff_eq.mp c)).elim

/-- On the actual frozen reader, changing from R to S complements the word,
and the lowercase-refined fixed-R traversal has the same R word. -/
structure Readings {i : LocalizedChemicalRing.Input} (r : RingNestedActivePair.Reader i)
    (rev : Bool) (q : RingActivePairs.Arm i) (w : List Bool) : Prop where
  atR : RingFullPathPairs.stageWords i r rev [] .R q = some w
  atS : RingFullPathPairs.stageWords i r rev [] .S q = some (complement w)
  fixed : RingFullPathPairs.stageWords i r rev [.lowercase] .R q = some w

theorem Readings.fields {i : LocalizedChemicalRing.Input} {r : RingNestedActivePair.Reader i}
    {rev : Bool} {q : RingActivePairs.Arm i} {w : List Bool} (words : Readings r rev q w)
    {x : Key} (got : RingFullPathEligibility.key? i r rev q = some x) :
    x.bestFourB = paired w ∧ x.fixedR = w := by
  unfold RingFullPathEligibility.key? at got
  simp only [RingFullPathPairs.pairs?,RingFullPathRule5.word?,words.atR,words.atS,words.fixed] at got
  cases u : RingRetainedStereoRefinement.priority i r rev [] q <;>
    cases l : RingRetainedStereoRefinement.priority i r rev [.lowercase] q <;> simp [u,l] at got
  subst x
  exact ⟨rfl,rfl⟩

/-- The test applies to any admitted digraph from its native readings.
No assumption identifies a winning ligand or a winning stage. -/
theorem from_readings {i : LocalizedChemicalRing.Input} {r : RingNestedActivePair.Reader i}
    {rev : Bool} {a b : RingActivePairs.Arm i} {w : List Bool} {x y : Key}
    (left : Readings r rev a w) (right : Readings r rev b (opposite w))
    (hx : RingFullPathEligibility.key? i r rev a = some x)
    (hy : RingFullPathEligibility.key? i r rev b = some y)
    (early : x.throughFourA = y.throughFourA) (lower : x.fourC = y.fourC)
    (m n : RingRetainedChemicalTrace.Word) :
    compare (trialKey x m) (trialKey y n) =
      if w = opposite w then compare m n else if w = w.reverse then
        (if w.head? = some true then .gt else .lt)
      else compare (paired w) (paired (opposite w)) := by
  obtain ⟨ax,fx⟩ := left.fields hx
  obtain ⟨ay,fy⟩ := right.fields hy
  exact (trial _ _ _ _ early lower ax ay fx fy m n).trans (classify _ _)

/-- A tie through Rule 5 pairs every R with an S. It can only have even length. -/
theorem tie_length (w : List Bool) (tie : w = opposite w) : w.length % 2 = 0 := by
  have countFlip (xs : List Bool) : (complement xs).count true = xs.count false := by
    induction xs with
    | nil => rfl
    | cons h t ih => cases h <;> simp_all [complement]
  have count := congrArg (List.count true) tie
  rw [opposite,countFlip,List.count_reverse] at count
  have total : w.count true + w.count false = w.length := by
    clear tie count
    induction w with
    | nil => rfl
    | cons h t ih => cases h <;> simp_all <;> omega
  omega

end TetraStereo.Engine.RingOppositeHandSequences
assert_kernel_only TetraStereo.Engine.RingOppositeHandSequences.trial
assert_kernel_only TetraStereo.Engine.RingOppositeHandSequences.classify
assert_kernel_only TetraStereo.Engine.RingOppositeHandSequences.tie_length
assert_kernel_only TetraStereo.Engine.RingOppositeHandSequences.from_readings
