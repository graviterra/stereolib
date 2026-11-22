import TetraStereo.Engine.RingClosedPairAssignment
import TetraStereo.Engine.RingNestedMagnitude

set_option autoImplicit false

namespace TetraStereo.Engine.RingClosedPairAssignment
open OneCenter
open RingActivePairReport (Slot doubled reversals)
open RingNestedActivePair (masked Labels)
open RingActivePairs (molecularValues)
open RingJointObservations (isLower)

/-- A closed mixed-group Rule 4c comparison has equal signed unit magnitude on
both geometries, so adding this source preserves the molecular score alphabet. -/
theorem Assignment.signed_scores {i f read} (o : Assignment i f read) (a b : Slot) (ne : a ≠ b) :
    o.matrix.get a b ∈ molecularValues := by
  rcases o.edge a b ne with earlier | ⟨c,out⟩
  · exact earlier.signed_scores
  · rw [← out]
    rcases (c.first_difference [] []).2 with pos | neg
    · rw [pos]; decide
    · rw [neg]; decide

theorem Assignment.reversals_eq_doubled {i f read} (o : Assignment i f read) :
    reversals o.matrix = doubled o.matrix := by
  apply (List.Perm.refl _).countP_congr
  intro p mem
  have h := o.signed_scores p.1 p.2 (ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp mem))
  let score := o.matrix.get p.1 p.2
  change score ∈ molecularValues at h
  change (decide (0 < score.1) != decide (0 < score.2)) = (score.1.natAbs == 2)
  simp only [molecularValues,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h <;> rw [h] <;> decide

/-- Every assigned grouped molecular frame has the hand of its physical read on
the actual geometry. Its six score magnitudes determine the case. -/
theorem Assignment.casing_by_magnitude {i f read} (o : Assignment i f read) :
    o.labels.1 = if doubled o.matrix % 2 = 0 then .chiral o.hand else .pseudoasymmetric (pseudoRSOfRS o.hand) := by
  rw [← o.reversals_eq_doubled]
  exact o.frame.label_by_reversals o.actual o.reflected o.physical o.mirrorPhysical

theorem Assignment.lower_iff_odd {i f read} (o : Assignment i f read) :
    isLower (some o.labels.1) = true ↔ doubled o.matrix % 2 = 1 := by
  rw [o.casing_by_magnitude]
  split <;> simp_all [isLower]

/-- Identify the actually selected publication branch, the complete two-geometry
matrix that assigned its labels, and the parity of its doubled comparisons. -/
def IssuedOdd {i : LocalizedChemicalRing.Input} {f : RingActivePairs.Site i} (read : RingNestedActivePair.Reader i) (v : Labels) : Prop :=
  (RingNestedActivePair.publish? i f read = some (some v) ∧
    ∃ a : RingNestedActivePair.Assignment i f (masked f read),
      RingNestedActivePair.assign? i f (masked f read) = some a ∧ v = a.labels ∧ doubled a.matrix % 2 = 1) ∨
  (RingNestedActivePair.publish? i f read = none ∧
    ∃ a : Assignment i f (masked f read),
      fromReader? i f (masked f read) = some a ∧ v = a.labels ∧ doubled a.matrix % 2 = 1)

theorem publication_lower_iff {i f read v} (hit : publish? i f read = some (some v)) :
    isLower (some v.1) = true ↔ IssuedOdd (f := f) read v := by
  constructor
  · intro low
    cases old : RingNestedActivePair.publish? i f read with
    | some prior =>
      have val : prior = some v := by simpa [publish?,old] using hit
      subst prior
      exact Or.inl ⟨old,(RingNestedActivePair.publication_lower_iff old).mp low⟩
    | none =>
      have issued : (fromReader? i f (masked f read)).map (some ∘ Assignment.labels) = some (some v) := by
        simpa [publish?,old] using hit
      obtain ⟨a,found,out⟩ := Option.map_eq_some_iff.mp issued
      have eqv : v = a.labels := (Option.some.inj out).symm
      exact Or.inr ⟨old,a,found,eqv,a.lower_iff_odd.mp (eqv ▸ low)⟩
  · rintro (⟨_,a,_,rfl,odd⟩ | ⟨_,a,_,rfl,odd⟩)
    · exact a.lower_iff_odd.mpr odd
    · exact a.lower_iff_odd.mpr odd

/-- The actual/reflected labels in the grouped recursive schedule have lowercase
case exactly when the winning molecular assignment has odd doubled-edge count. -/
theorem atRoot_lower_iff {i : LocalizedChemicalRing.Input} {root : i.certified.Atom}
    {q : RingActivePairs.Site i} (on : q.val.root = root) {v : Labels}
    (hit : atRoot i root q = some (some v)) :
    isLower (some v.1) = true ↔ IssuedOdd (f := q) (atRoot i root) v :=
  publication_lower_iff ((atRoot_eq on).symm.trans hit)

end TetraStereo.Engine.RingClosedPairAssignment

assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.Assignment.signed_scores
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.Assignment.casing_by_magnitude
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.Assignment.lower_iff_odd
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.atRoot_lower_iff
