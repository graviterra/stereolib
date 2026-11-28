import TetraStereo.Engine.RingMolecularDonorClasses
import TetraStereo.Engine.RingBinaryPairScore
import TetraStereo.Engine.RingResidualPairDecision

/-! First unequal donor position and the ordinary Rule 4b/4c/5 decision. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMolecularDonorVerdict
open OneCenter RingMolecularDonorClasses
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingFullPathTrialReadings (trialKey bitWord)
open RingFullPathEligibility (Key)
open RingResidualPairDecision (Verdict)
attribute [local instance] lexOrd

/-- Located emitting classes in the same order as the molecular word. -/
abbrev Spheres := List (List Group)
abbrev Located := Nat × Group
def emissions (gs : Spheres) : List Located :=
  gs.zipIdx.flatMap fun (row,d) => row.flatMap fun g => g.word.map fun _ => (d,g)

def bits (gs : Spheres) := gs.flatMap (List.flatMap Group.word)

private theorem signs (gs : Spheres) :
    (emissions gs).map (fun v => v.2.like) = bits gs := by
  unfold emissions bits
  simp only [List.map_flatMap,List.map_map,Function.comp_def]
  have single (g : Group) : (g.word.map fun _ => g.like) = g.word := by simp [Group.word]
  simp only [single]
  have h := congrArg (List.flatMap (List.flatMap Group.word)) (List.zipIdx_map_fst 0 gs)
  simpa only [List.flatMap_map] using h

/-- Number of equal bits before the first mismatch or the end of a word. -/
def offset : List Bool → List Bool → Nat
  | a::as, b::bs => if a = b then (offset as bs).succ else 0
  | _,_ => 0

private theorem at_offset (xs ys : List Bool) :
    let n := offset xs ys
    xs.take n = ys.take n ∧ compare xs ys = compare xs[n]? ys[n]? ∧
      (xs[n]? = ys[n]? ↔ xs = ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [offset]; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp [offset]; rfl
    | cons y ys =>
      by_cases eqn : x = y
      · subst y
        simpa [offset,List.compare_cons_cons] using ih ys
      · cases x <;> cases y <;> simp_all [offset,List.compare_cons_cons] <;> rfl

structure Difference where
  index : Nat
  left : Option Located
  right : Option Located
  deriving Repr, DecidableEq

def difference (a b : Spheres) : Difference :=
  let n := offset (bits a) (bits b)
  ⟨n,(emissions a)[n]?,(emissions b)[n]?⟩

def Difference.order (d : Difference) :=
  compare (d.left.map fun l => l.2.like) (d.right.map fun l => l.2.like)

/-- At the first differing bit, identify the sphere and full donor class on
both arms. A strict prefix has an absent class on the exhausted arm. -/
theorem difference_exact (a b : Spheres) :
    let d := difference a b
    (bits a).take d.index = (bits b).take d.index ∧
    d.order = compare (bits a) (bits b) ∧ (d.order = .eq ↔ bits a = bits b) := by
  obtain ⟨pre,ord,_⟩ := at_offset (bits a) (bits b)
  have dir : (difference a b).order = compare (bits a) (bits b) := by
    rw [ord]
    simp only [difference,Difference.order,← List.getElem?_map,signs]
  exact ⟨pre,dir,dir ▸ Std.compare_eq_eq_iff_eq⟩

theorem molecular_difference {i : Input} {r : Reader i} {rev os seed} {u v : Arm i} {a b : Spheres}
    (left : groups? i r rev os seed u = some a) (right : groups? i r rev os seed v = some b) :
    (RingFullPathPairs.stageWords i r rev os seed u).bind (fun x =>
      (RingFullPathPairs.stageWords i r rev os seed v).map (compare x)) =
      some (difference a b).order := by
  rw [←groups_exact,←groups_exact,left,right]
  exact congrArg some (difference_exact a b).2.1.symm

def field? (i : Input) (r : Reader i) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) (q : Arm i) :=
  (groups? i r rev os seed q).map bits

/-- Construct both stereochemical fields from the molecular donor classes.
Keep the native constitutional, Rule 4a and Rule 4c readings. -/
def key? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option Key := do
  let u ← RingRetainedStereoRefinement.priority i r rev [] q
  let l ← RingRetainedStereoRefinement.priority i r rev [.lowercase] q
  let ar ← field? i r rev [] .R q
  let as' ← field? i r rev [] .S q
  let f ← field? i r rev [.lowercase] .R q
  return ⟨u.deep,max ar as',l.word,f⟩

theorem key_exact (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) :
    key? i r rev q = RingFullPathEligibility.key? i r rev q := by
  have h (os seed) : field? i r rev os seed q = RingFullPathPairs.stageWords i r rev os seed q :=
    groups_exact i r rev os seed q
  simp only [key?,RingFullPathEligibility.key?,RingFullPathPairs.pairs?,RingFullPathRule5.word?,h]

private def whenStrict (o : Ordering) (s : RingLigandFirstDifference.Stage) (next : Verdict) : Verdict :=
  match o with
  | .gt => .left s
  | .lt => .right s
  | .eq => next

def residual (a b : Key) : Verdict :=
  whenStrict (compare a.bestFourB b.bestFourB) .rule4b
    (whenStrict (compare a.fourC b.fourC) .rule4c (whenStrict (compare a.fixedR b.fixedR) .rule5 .tie))

/-- Exact first stage and direction of the residual decision. Equal
populations at the best reference alone do not bypass the Rule 4c field. -/
theorem residual_explains (a b : Key) :
    let x := compare a.bestFourB b.bestFourB
    let y := compare a.fourC b.fourC
    let z := compare a.fixedR b.fixedR
    let v := residual a b
    (v = .tie ↔ x = .eq ∧ y = .eq ∧ z = .eq) ∧
    (v = .left .rule4b ↔ x = .gt) ∧ (v = .right .rule4b ↔ x = .lt) ∧
    (v = .left .rule4c ↔ x = .eq ∧ y = .gt) ∧ (v = .right .rule4c ↔ x = .eq ∧ y = .lt) ∧
    (v = .left .rule5 ↔ x = .eq ∧ y = .eq ∧ z = .gt) ∧
    (v = .right .rule5 ↔ x = .eq ∧ y = .eq ∧ z = .lt) := by
  dsimp only
  unfold residual
  cases compare a.bestFourB b.bestFourB <;> cases compare a.fourC b.fourC <;>
    cases compare a.fixedR b.fixedR <;> decide

/-- Once the earlier fields tie, the two best-seed words, the intervening
Rule 4c comparison, and finally the fixed R words resolve the ordinary pair. -/
theorem residual_order {a b : Key} (early : a.throughFourA = b.throughFourA) :
    compare (trialKey a []) (trialKey b []) = (residual a b).order := by
  simp only [trialKey,early,List.compare_cons_cons,Std.ReflCmp.compare_self,
    RingBinaryPairScore.compare_bits]
  cases h : compare a.bestFourB b.bestFourB <;> cases j : compare a.fourC b.fourC <;>
    cases k : compare a.fixedR b.fixedR <;> simp [residual,whenStrict,h,j,k,Verdict.order]

theorem molecular_residual {i : Input} {r : Reader i} {rev : Bool} {u v : Arm i} {a b : Key}
    (left : key? i r rev u = some a) (right : key? i r rev v = some b)
    (early : a.throughFourA = b.throughFourA) :
    (RingFullPathEligibility.key? i r rev u).bind (fun x =>
      (RingFullPathEligibility.key? i r rev v).map (fun y => compare (trialKey x []) (trialKey y []))) =
      some (residual a b).order := by
  rw [←key_exact,←key_exact,left,right]
  exact congrArg some (residual_order early)

end TetraStereo.Engine.RingMolecularDonorVerdict
assert_kernel_only TetraStereo.Engine.RingMolecularDonorVerdict.difference_exact
assert_kernel_only TetraStereo.Engine.RingMolecularDonorVerdict.molecular_difference
assert_kernel_only TetraStereo.Engine.RingMolecularDonorVerdict.key_exact
assert_kernel_only TetraStereo.Engine.RingMolecularDonorVerdict.molecular_residual
assert_kernel_only TetraStereo.Engine.RingMolecularDonorVerdict.residual_explains
