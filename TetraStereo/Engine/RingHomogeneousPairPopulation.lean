import TetraStereo.Engine.RingFIFOPopulation
import TetraStereo.Engine.RingFIFOAlternatives

set_option autoImplicit false

namespace TetraStereo.Engine.RingHomogeneousPairPopulation
open OneCenter LocalizedChemicalRing RingActivePairs
open RingNestedActivePair (Reader)
open RingClosedPairGroup (FIFO upperAt word)

/-- One complete walk determines a monochromatic population on every complete
walk of the same arm, even with unrelated priority refinements. Only accepted
uppercase publications enter this statement. -/
theorem all_walks {i : Input} {q : Arm i} {lo ro : Arm i → List (Arm i) → Prop}
    (read : Reader i) (rev : Bool) {xs ys} {n : Nat} {hand : RS}
    (one : FIFO i lo [q] xs) (other : FIFO i ro [q] ys)
    (uniform : xs.filterMap (upperAt read rev) = List.replicate n hand) :
    ys.filterMap (upperAt read rev) = List.replicate n hand := by
  have perm := RingFIFOPopulation.accepted_perm read rev (List.Perm.refl [q]) other one
  rw [uniform] at perm
  exact List.eq_replicate_iff.mpr ⟨by simpa using perm.length_eq,
    fun h mem => (List.mem_replicate.mp (perm.mem_iff.mp mem)).2⟩

private theorem compare_const (x y : Bool) (n : Nat) :
    RingSeededPairs.compareBits (List.replicate (n+1) x) (List.replicate (n+1) y) =
      (if x = y then 0 else if x then 1 else -1) := by
  cases x <;> cases y <;> induction n <;> simp_all [RingSeededPairs.compareBits,List.replicate_succ]

/-- Opposite homogeneous populations of equal positive size give an exact
magnitude-two Rule 5 comparison. The number of intervening neutral visits,
ring depth, and ordering of every sibling row are unrestricted. -/
theorem opposite_score {i : Input} {a b : Arm i} (read : Reader i) (rev : Bool) (n : Nat)
    {oldA oldB ar br as' bs' : Arm i → List (Arm i) → Prop}
    {x y xr yr xs ys} (left : FIFO i oldA [a] x) (right : FIFO i oldB [b] y)
    (pos : x.filterMap (upperAt read rev) = List.replicate (n+1) .R)
    (neg : y.filterMap (upperAt read rev) = List.replicate (n+1) .S)
    (pr : FIFO i ar [a] xr) (qr : FIFO i br [b] yr)
    (ps : FIFO i as' [a] xs) (qs : FIFO i bs' [b] ys) :
    (do
      let r ← RingSeededPairs.listSign? .R (xr.map (upperAt read rev)) (yr.map (upperAt read rev))
      let s ← RingSeededPairs.listSign? .S (xs.map (upperAt read rev)) (ys.map (upperAt read rev))
      return CentresRing.PairList.combine r s) = some 2 := by
  simp only [RingSeededPairs.listSign?,List.filterMap_map,Function.comp_def,id_eq,
    all_walks read rev left pr pos,all_walks read rev right qr neg,
    all_walks read rev left ps pos,all_walks read rev right qs neg,
    List.length_replicate,if_true,List.map_replicate,compare_const]
  rfl

/-- Known cells on one traversal cover every traversal at this root. This
removes the universal reader premise from the exhaustive word dichotomy. -/
theorem known_all {i : Input} {q : Arm i} {lo ro : Arm i → List (Arm i) → Prop}
    {xs ys} (read : Reader i) (one : FIFO i lo [q] xs) (other : FIFO i ro [q] ys)
    (known : ∀ t ∈ xs, (read t.occurrence).isSome = true) :
    ∀ t ∈ ys, (read t.occurrence).isSome = true :=
  fun t ht => known t ((RingFIFOPopulation.visits_perm (List.Perm.refl [q]) other one).mem_iff.mp ht)

theorem complete_from_one {i : Input} {q : Arm i} {xs} (read : Reader i) (rev : Bool) (seed : RS)
    (valid : i.certified.LocalizedRerootCursorValid q)
    (one : RingFIFOAlternatives.ChemicalWalk i q xs)
    (known : ∀ t ∈ xs, (read t.occurrence).isSome = true) :
    (∃ b, some b ∈ RingFIFOAlternatives.chemicalPairWords read rev seed q ∧
      ∀ ys, RingFIFOAlternatives.ChemicalWalk i q ys →
        RingFIFOAlternatives.checkedWord read rev seed ys = some b) ∨
    (∃ us vs, RingFIFOAlternatives.ChemicalWalk i q us ∧ RingFIFOAlternatives.ChemicalWalk i q vs ∧
      word read rev seed us ≠ word read rev seed vs) :=
  RingFIFOAlternatives.chemical_dichotomy read rev seed valid (fun _ h => known_all read one h known)

end TetraStereo.Engine.RingHomogeneousPairPopulation
assert_kernel_only TetraStereo.Engine.RingHomogeneousPairPopulation.all_walks
assert_kernel_only TetraStereo.Engine.RingHomogeneousPairPopulation.opposite_score
assert_kernel_only TetraStereo.Engine.RingHomogeneousPairPopulation.known_all
assert_kernel_only TetraStereo.Engine.RingHomogeneousPairPopulation.complete_from_one
