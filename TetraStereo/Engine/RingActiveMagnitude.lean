import TetraStereo.Engine.RingSeededPairCasing
import TetraStereo.Engine.RingActivePairReport

set_option autoImplicit false

namespace TetraStereo.Engine.RingActivePairs
open OneCenter RingSeededPairs
open LocalizedChemicalRing (Input)

def MagnitudeAgrees (v : Int × Int) : Prop :=
  (decide (0 < v.1) != decide (0 < v.2)) = (v.1.natAbs == 2)

def molecularValues : List (Int × Int) := [(-2,2),(-1,-1),(0,0),(1,1),(2,-2)]

private theorem pair_values {i f l r} (p : OrderedPair i f l r) {a b : Decision}
    (ha : p.decision? false = some a) (hb : p.decision? true = some b) : (score a,score b) ∈ molecularValues := by
  rcases ordered_scores p ha with ⟨_,vals,h⟩ | ⟨_,vals,h⟩ <;>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at vals <;>
    simp only [hb,Option.map_some,Option.some.injEq] at h
  · rcases vals with v | v <;> simp [molecularValues,h,v]
  · rcases vals with v | v | v <;> simp [molecularValues,h,v]

/-- On every molecular pair accepted by the reader, sign reversal is equivalent to doubled
magnitude. The claim includes the diagonal and tied pairs as well as both strict signs. -/
theorem rootScore_values {i : Input} {c : i.certified.TetrahedralCenter} {a b : Fin 4} {v}
    (got : rootScore? i c a b = some v) : v ∈ molecularValues := by
  unfold rootScore? at got
  split at got
  · obtain rfl := Option.some.inj got
    decide
  · obtain ⟨_,_,rest⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨prior,_,read⟩ := Option.bind_eq_some_iff.mp rest
    cases hp : prior.outcome with
    | lt => simp [hp] at read; subst v; decide
    | gt => simp [hp] at read; subst v; decide
    | eq =>
      simp only [hp] at read
      obtain ⟨focus,_,read⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨left,_,read⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨right,_,read⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨p,_,read⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨first,hf,read⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨second,hs,read⟩ := Option.bind_eq_some_iff.mp read
      obtain rfl := Option.some.inj read
      exact pair_values p hf hs

theorem rootScore_magnitude {i : Input} {c : i.certified.TetrahedralCenter} {a b : Fin 4} {v}
    (got : rootScore? i c a b = some v) : MagnitudeAgrees v := by
  have values := rootScore_values got
  simp only [molecularValues,List.mem_cons,List.not_mem_nil,or_false] at values
  rcases values with rfl | rfl | rfl | rfl | rfl <;> rfl

end TetraStereo.Engine.RingActivePairs

namespace TetraStereo.Engine.RingActivePairReport
open OneCenter

/-- All six magnitudes in the matrix are molecular results. Their parity determines the
case, and the order on the original geometry determines the absolute letter. -/
theorem Assignment.exact_letter_casing {i c} (o : Assignment i c)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    o.label = if doubled o.matrix % 2 = 0 then .chiral o.hand
      else .pseudoasymmetric (pseudoRSOfRS o.hand) :=
  o.casing_by_magnitude admit fun a b lt =>
    RingActivePairs.rootScore_magnitude (o.matrix.found a b (ne_of_lt lt))

end TetraStereo.Engine.RingActivePairReport

assert_kernel_only TetraStereo.Engine.RingActivePairs.rootScore_values
assert_kernel_only TetraStereo.Engine.RingActivePairs.rootScore_magnitude
assert_kernel_only TetraStereo.Engine.RingActivePairReport.Assignment.exact_letter_casing
