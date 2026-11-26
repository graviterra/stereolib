import TetraStereo.Engine.RingMolecularPairScore
import TetraStereo.Engine.RingPairwisePublication

set_option autoImplicit false
namespace TetraStereo.Engine.RingTetrahedralNumericRows
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)
open RingGroupedCentre (cursor)
open RingActivePairReport (Slot)
open RingFullPathEligibility (Key)
open RingPairwisePublication (Data Directions directions)
open RingFullPathTrialReadings (markWords? trialKey)
open RingMolecularPairScore (numericKey)

/-- Pair directions computed using the Figure 8 integer readings, on both
ordinary rows and each independently marked row. -/
def data {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (x y : Slot → Key) : Data where
  ordinary rev := directions (fun k => numericKey ((if rev then y else x) k) [])
  marked rev s := (markWords? fr r s).map fun ws =>
    directions (fun k => numericKey ((if rev then y else x) k) (ws k))

def data? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Option Data := do
  let x ← RingFullPathPublication.keys? fr r false
  let y ← RingFullPathPublication.keys? fr r true
  return data fr r x y

private theorem directions_eq {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (rev : Bool) (ks : Slot → Key)
    (got : RingFullPathPublication.keys? fr r rev = some ks)
    (marks : Slot → RingRetainedChemicalTrace.Word) :
    directions (fun k => numericKey (ks k) (marks k)) =
      directions (fun k => trialKey (ks k) (marks k)) := by
  funext a b
  unfold directions
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (RingMolecularPairScore.key_lt ready rev (cursor fr a) (cursor fr b)
    (RingGroupedCentre.valid fr a) (RingGroupedCentre.valid fr b)
    (fr.direction a).property.1 (fr.direction b).property.1
    (RingActivePairReport.four_at got a) (RingActivePairReport.four_at got b)
    (marks a) (marks b)).symm

theorem data_of_keys {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (x y : Slot → Key)
    (hx : RingFullPathPublication.keys? fr r false = some x)
    (hy : RingFullPathPublication.keys? fr r true = some y) :
    data fr r x y = RingPairwisePublication.nativeData fr r x y := by
  have ordinary : (fun rev : Bool => directions (fun k => numericKey ((if rev then y else x) k) [])) =
      (fun rev : Bool => RingPairwisePublication.ordinary (if rev then y else x)) := by
    funext rev
    cases rev
    · exact directions_eq fr ready false x hx (fun _ => [])
    · exact directions_eq fr ready true y hy (fun _ => [])
  have marked : (fun (rev : Bool) s => (markWords? fr r s).map fun ws =>
      directions (fun k => numericKey ((if rev then y else x) k) (ws k))) =
      (fun (rev : Bool) s => (markWords? fr r s).map fun ws =>
      directions (fun k => trialKey ((if rev then y else x) k) (ws k))) := by
    funext rev s
    apply congrArg (Option.map · (markWords? fr r s))
    funext ws
    cases rev
    · exact directions_eq fr ready false x hx ws
    · exact directions_eq fr ready true y hy ws
  exact congrArg₂ Data.mk ordinary marked

/-- The ready molecular reader makes the numeric comparison data exactly
the native comparison data, including unresolved marked coverage. -/
theorem data_exact {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) : data? fr r = RingPairwisePublication.nativeData? fr r := by
  unfold data? RingPairwisePublication.nativeData?
  cases hx : RingFullPathPublication.keys? fr r false with
  | none => rfl
  | some x =>
    cases hy : RingFullPathPublication.keys? fr r true with
    | none => rfl
    | some y => simpa using congrArg some (data_of_keys fr ready x y hx hy)

end TetraStereo.Engine.RingTetrahedralNumericRows
assert_kernel_only TetraStereo.Engine.RingTetrahedralNumericRows.data_exact
