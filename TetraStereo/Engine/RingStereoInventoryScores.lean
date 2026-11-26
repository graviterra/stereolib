import TetraStereo.Engine.RingStereoSphereInventory
import TetraStereo.Engine.RingStereoRuns

/-! Molecular comparisons from one reference-independent inventory per arm.
Compressed summaries contain only emitted hands, and merge across source classes. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStereoInventoryScores
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingStereoSphereInventory (Inventory inventory? reading)
open RingStereoRuns (BoolRun encode runCompare)

private def sign : Ordering → Int
  | .lt => -1 | .eq => 0 | .gt => 1

def summary (seed : RS) (v : Inventory) : List BoolRun := encode (reading seed v)

private theorem compare_lt (x y : List Bool) : compare x y = .lt ↔ x < y :=
  DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => by decide +revert)
    (fun _ _ => Std.compare_eq_eq_iff_eq) x y

/-- Select the larger of the two fixed-reference summaries using run counts. -/
def best (v : Inventory) : List BoolRun :=
  let r := summary .R v
  let s := summary .S v
  if runCompare r s = .lt then s else r

theorem best_exact (v : Inventory) :
    best v = encode (max (reading .R v) (reading .S v)) := by
  simp only [best,summary,RingStereoRuns.compare_encoded]
  split
  · next h => rw [max_eq_right (le_of_lt ((compare_lt _ _).mp h))]
  · next h => rw [max_eq_left (le_of_not_gt (fun lt => h ((compare_lt _ _).mpr lt)))]

/-- Rule 4b evaluates the best reference on each side. -/
def hanson? (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) : Option Int := do
  let x ← inventory? i r rev [] a
  let y ← inventory? i r rev [] b
  return sign (runCompare (best x) (best y))

/-- Rule 5 uses both fixed references after Rule 4c, preserving its signed magnitude. -/
def rule5? (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) : Option Int := do
  let x ← inventory? i r rev [.lowercase] a
  let y ← inventory? i r rev [.lowercase] b
  return RingOccurrenceStereo.fixedScore (runCompare (summary .R x) (summary .R y))
    (runCompare (summary .S x) (summary .S y))

/-- Equality includes lookup failures, for arbitrary molecular inputs and readers. -/
theorem hanson_exact (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) :
    hanson? i r rev a b = RingFullPathPairs.hanson? i r rev a b := by
  unfold hanson? RingFullPathPairs.hanson? RingFullPathPairs.pairs?
  simp only [← RingStereoSphereInventory.reading_exact]
  cases inventory? i r rev [] a <;> cases inventory? i r rev [] b <;>
    simp [best_exact,RingStereoRuns.compare_encoded,RingOccurrenceStereo.fourLists_order]
  rfl

theorem rule5_exact (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) :
    rule5? i r rev a b = RingFullPathRule5.score? i r rev a b := by
  unfold rule5? RingFullPathRule5.score? RingFullPathRule5.word?
  simp only [← RingStereoSphereInventory.reading_exact]
  cases inventory? i r rev [.lowercase] a <;> cases inventory? i r rev [.lowercase] b <;>
    simp [summary,RingStereoRuns.compare_encoded]

theorem hanson_none_iff (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) :
    hanson? i r rev a b = none ↔
      inventory? i r rev [] a = none ∨ inventory? i r rev [] b = none := by
  cases ha : inventory? i r rev [] a <;> cases hb : inventory? i r rev [] b <;> simp [hanson?,ha,hb]

theorem rule5_none_iff (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) :
    rule5? i r rev a b = none ↔
      inventory? i r rev [.lowercase] a = none ∨ inventory? i r rev [.lowercase] b = none := by
  cases ha : inventory? i r rev [.lowercase] a <;> cases hb : inventory? i r rev [.lowercase] b <;> simp [rule5?,ha,hb]

private theorem sign_zero (o : Ordering) : sign o = 0 ↔ o = .eq := by
  cases o <;> decide

private theorem fixed_zero (x y : Ordering) : RingOccurrenceStereo.fixedScore x y = 0 ↔ x = .eq := by
  cases x <;> cases y <;> decide

/-- The sharp Rule 4b tie criterion compares only emitted best-reference runs;
source-rank and sphere boundaries do not enter it. -/
theorem hanson_tie {i : Input} {r : Reader i} {rev : Bool} {a b : Arm i} {x y : Inventory}
    (left : inventory? i r rev [] a = some x) (right : inventory? i r rev [] b = some y) :
    hanson? i r rev a b = some 0 ↔ best x = best y := by
  simp [hanson?,left,right,sign_zero,best_exact,RingStereoRuns.compare_encoded]

/-- Rule 5 zero is exactly equality of the R reading. The S reading determines
magnitude when R is strict and need not tie when R ties. -/
theorem rule5_tie {i : Input} {r : Reader i} {rev : Bool} {a b : Arm i} {x y : Inventory}
    (left : inventory? i r rev [.lowercase] a = some x)
    (right : inventory? i r rev [.lowercase] b = some y) :
    rule5? i r rev a b = some 0 ↔ summary .R x = summary .R y := by
  simp [rule5?,left,right,fixed_zero,summary,RingStereoRuns.compare_encoded]

end TetraStereo.Engine.RingStereoInventoryScores
assert_kernel_only TetraStereo.Engine.RingStereoInventoryScores.hanson_exact
assert_kernel_only TetraStereo.Engine.RingStereoInventoryScores.rule5_exact
assert_kernel_only TetraStereo.Engine.RingStereoInventoryScores.hanson_tie
assert_kernel_only TetraStereo.Engine.RingStereoInventoryScores.rule5_tie
assert_kernel_only TetraStereo.Engine.RingStereoInventoryScores.best_exact
assert_kernel_only TetraStereo.Engine.RingStereoInventoryScores.hanson_none_iff
assert_kernel_only TetraStereo.Engine.RingStereoInventoryScores.rule5_none_iff
