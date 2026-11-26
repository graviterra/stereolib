import TetraStereo.Engine.RingOriginPyramidalTrials
import TetraStereo.Engine.RingPairwisePublication

/-! Full four-coordinate trials from independently rebuilt full keys and
mark words. All ordinary and marked matrices retain failed reads. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTetrahedralTrials
open OneCenter
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot four?)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
open RingOriginPyramidalTrials (KeyReader WordReader key)
open RingPairwisePublication (Data directions ordinary)
open private first first_strictMono from TetraStereo.Engine.RingOriginPyramidalTrials
attribute [local instance] lexOrd

private theorem four_map {α β : Type} (f : Slot → Option α) (g : α → β) :
    four? (fun s => (f s).map g) = (four? f).map (fun row s => g (row s)) := by
  cases a : f 0 <;> cases b : f 1 <;> cases c : f 2 <;> cases d : f 3 <;>
    simp [four?,a,b,c,d,Option.bind_eq_bind]
  funext s
  fin_cases s <;> rfl

/-- Read every actual slot, preserving an unavailable full key. -/
def keysWith {i : Input} {f : Site i} (fr : Frame i f) (keys : KeyReader i) (rev : Bool) :=
  four? fun s => keys rev (RingGroupedCentre.cursor fr s)

/-- Every nominated slot selects its actual molecular atom; an unmarked trial
contains the empty mark word independently of molecular readings. -/
def wordsWith {i : Input} {f : Site i} (fr : Frame i f) (words : WordReader i) :
    Option Slot → Option (Slot → Word)
  | none => some (fun _ => [])
  | some s => four? fun k => words (some (RingGroupedTrials.atom fr s)) (RingGroupedCentre.cursor fr k)

def data (x y : Slot → Key) (marks : Option Slot → Option (Slot → Word)) : Data where
  ordinary rev := ordinary (if rev then y else x)
  marked rev s := (marks s).map fun ws => directions (fun k => trialKey ((if rev then y else x) k) (ws k))

/-- Compute both ordinary matrices and every optional marked matrix from raw
arm readers before asking the coordinate and casing consumers to publish. -/
def dataWith {i : Input} {f : Site i} (fr : Frame i f) (keys : KeyReader i) (words : WordReader i) : Option Data := do
  let x ← keysWith fr keys false
  let y ← keysWith fr keys true
  return data x y (wordsWith fr words)

private theorem directions_recode (ks : Slot → Key) (ws : Slot → Word)
    (g : Nat → Nat) (hg : StrictMono g) :
    directions (fun s => trialKey (key g (ks s)) (ws s)) = directions (fun s => trialKey (ks s) (ws s)) := by
  let transform := first (RingPriorityCoordinate.second (List.map (List.map g)))
  have mono : StrictMono transform := first_strictMono
    (RingPriorityCoordinate.second_strictMono
      (RingPriorityCoordinate.map_strictMono (RingPriorityCoordinate.map_strictMono hg)))
  funext a b
  change decide (transform (trialKey (ks a) (ws a)) < transform (trialKey (ks b) (ws b))) = _
  exact Bool.decide_congr mono.lt_iff_lt

private theorem data_recode (x y : Slot → Key) (marks : Option Slot → Option (Slot → Word))
    (g : Nat → Nat) (hg : StrictMono g) :
    data (fun s => key g (x s)) (fun s => key g (y s)) marks = data x y marks := by
  apply congrArg₂ Data.mk
  · funext rev
    cases rev <;> exact directions_recode _ (fun _ => []) g hg
  · funext rev s
    cases rev <;> cases hm : marks s with
    | none => rfl
    | some ws => exact congrArg some (directions_recode _ ws g hg)

private theorem dataWith_recode {i : Input} {f : Site i} (fr : Frame i f)
    (base : KeyReader i) (words : WordReader i) (g : Nat → Nat) (hg : StrictMono g) :
    dataWith fr (fun rev arm => (base rev arm).map (key g)) words = dataWith fr base words := by
  have rows (rev : Bool) : keysWith fr (fun rev arm => (base rev arm).map (key g)) rev =
      (keysWith fr base rev).map (fun row s => key g (row s)) := four_map _ _
  simp only [dataWith,rows]
  cases hx : keysWith fr base false <;> cases hy : keysWith fr base true <;>
    simp only [Option.map_none,Option.map_some,Option.bind_eq_bind,Option.bind_none,Option.bind_some,Option.pure_def]
  exact congrArg some (data_recode _ _ _ g hg)

private theorem native_words {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) :
    wordsWith fr (RingFrameTransport.markWord? i r) = RingFullPathTrialReadings.markWords? fr r := by
  funext mark
  cases mark with
  | none => rfl
  | some s =>
    change (four? fun k => (RingGroupedMark.arm? i r (RingGroupedTrials.atom fr s)
      (RingGroupedCentre.cursor fr k)).map (fun b => b.2.word)) =
        (RingGroupedTrials.marking? fr r s).map RingGroupedTrials.Marking.word
    rw [four_map]
    generalize h : (four? fun k => RingGroupedMark.arm? i r (RingGroupedTrials.atom fr s)
      (RingGroupedCentre.cursor fr k)) = result
    cases result with
    | none =>
      simp only [RingGroupedTrials.marking?]
      rw [Option.attach_eq_none_iff.mpr h]
      rfl
    | some row =>
      simp only [RingGroupedTrials.marking?]
      rw [Option.attach_eq_some _ ⟨row,h⟩]
      rfl

private theorem native_data {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) :
    dataWith fr (RingFullPathEligibility.key? i r) (RingFrameTransport.markWord? i r) =
      RingPairwisePublication.nativeData? fr r := by
  simp only [dataWith,native_words,RingPairwisePublication.nativeData?,keysWith,RingFullPathPublication.keys?]
  rfl

/-- Equality of full comparison data follows from raw increasing key
factorization and per-arm equality of mark words on the actual root slice. -/
theorem data_raw {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (base alternative : KeyReader i) (words : WordReader i)
    (g h : Nat → Nat) (hg : StrictMono g) (hh : StrictMono h)
    (native : ∀ rev arm, arm.occurrence.val.root = f.val.root →
      RingFullPathEligibility.key? i r rev arm = (base rev arm).map (key g))
    (other : ∀ rev arm, arm.occurrence.val.root = f.val.root →
      alternative rev arm = (base rev arm).map (key h))
    (marks : ∀ mark arm, arm.occurrence.val.root = f.val.root →
      words mark arm = RingFrameTransport.markWord? i r mark arm) :
    dataWith fr alternative words = RingPairwisePublication.nativeData? fr r := by
  have on (s : Slot) : (RingGroupedCentre.cursor fr s).occurrence.val.root = f.val.root :=
    (fr.direction s).property.1
  have rowNative (rev : Bool) : keysWith fr (RingFullPathEligibility.key? i r) rev =
      keysWith fr (fun rev arm => (base rev arm).map (key g)) rev := by
    unfold keysWith
    congr 1
    funext s
    exact native rev _ (on s)
  have rowOther (rev : Bool) : keysWith fr alternative rev =
      keysWith fr (fun rev arm => (base rev arm).map (key h)) rev := by
    unfold keysWith
    congr 1
    funext s
    exact other rev _ (on s)
  have wordsEq : wordsWith fr words = wordsWith fr (RingFrameTransport.markWord? i r) := by
    funext mark
    cases mark with
    | none => rfl
    | some s =>
      change (four? fun k => words (some (RingGroupedTrials.atom fr s)) (RingGroupedCentre.cursor fr k)) =
        (four? fun k => RingFrameTransport.markWord? i r (some (RingGroupedTrials.atom fr s)) (RingGroupedCentre.cursor fr k))
      congr 1
      funext k
      exact marks _ _ (on k)
  rw [← native_data]
  change (keysWith fr alternative false).bind _ = _
  simp only [dataWith,rowOther,rowNative,wordsEq]
  change dataWith fr (fun rev arm => (base rev arm).map (key h)) (RingFrameTransport.markWord? i r) =
    dataWith fr (fun rev arm => (base rev arm).map (key g)) (RingFrameTransport.markWord? i r)
  rw [dataWith_recode fr base _ h hh,dataWith_recode fr base _ g hg]

/-- Read coordinates only after every full and marked comparison was computed. -/
def centreWith {i : Input} {f : Site i} (fr : Frame i f) (keys : KeyReader i) (words : WordReader i) :=
  (dataWith fr keys words).bind fun d => d.publish
    (fun _ row => LocalizedGenericMarkedRecalculation.readback? (inputGeometry i.certified) (fr.atoms row))

theorem centre_raw {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) (r : Reader i)
    (base alternative : KeyReader i) (words : WordReader i)
    (g h : Nat → Nat) (hg : StrictMono g) (hh : StrictMono h)
    (native : ∀ rev arm, arm.occurrence.val.root = f.val.root →
      RingFullPathEligibility.key? i r rev arm = (base rev arm).map (key g))
    (other : ∀ rev arm, arm.occurrence.val.root = f.val.root →
      alternative rev arm = (base rev arm).map (key h))
    (marks : ∀ mark arm, arm.occurrence.val.root = f.val.root →
      words mark arm = RingFrameTransport.markWord? i r mark arm) :
    centreWith fr alternative words = RingFullPathPublication.centre? fr r := by
  unfold centreWith
  rw [data_raw fr r base alternative words g h hg hh native other marks]
  exact (RingPairwisePublication.centreG_exact fr r _).symm.trans (RingFrameTransport.centreG_input geom fr r)

/-- Structural absence and an unresolved trial remain separate outcomes. -/
def publishWith (i : Input) (q : Site i) (keys : KeyReader i) (words : WordReader i) :
    RingActiveDistanceSchedule.Cell :=
  match RingNestedActivePair.frame? i q with
  | none => some none
  | some fr => centreWith fr keys words

theorem publish_raw {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (r : Reader i) (base alternative : KeyReader i) (words : WordReader i)
    (g h : Nat → Nat) (hg : StrictMono g) (hh : StrictMono h)
    (native : ∀ rev arm, arm.occurrence.val.root = q.val.root →
      RingFullPathEligibility.key? i r rev arm = (base rev arm).map (key g))
    (other : ∀ rev arm, arm.occurrence.val.root = q.val.root →
      alternative rev arm = (base rev arm).map (key h))
    (marks : ∀ mark arm, arm.occurrence.val.root = q.val.root →
      words mark arm = RingFrameTransport.markWord? i r mark arm) :
    publishWith i q alternative words = RingFullPathPublication.publish? i q r := by
  unfold publishWith RingFullPathPublication.publish?
  cases hf : RingNestedActivePair.frame? i q with
  | none => rfl
  | some fr => exact centre_raw geom fr r base alternative words g h hg hh native other marks

end TetraStereo.Engine.RingOriginTetrahedralTrials
assert_kernel_only TetraStereo.Engine.RingOriginTetrahedralTrials.data_raw
assert_kernel_only TetraStereo.Engine.RingOriginTetrahedralTrials.centre_raw

assert_kernel_only TetraStereo.Engine.RingOriginTetrahedralTrials.publish_raw
