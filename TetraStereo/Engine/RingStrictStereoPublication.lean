import TetraStereo.Engine.RingFrameTransport
import Batteries.Tactic.OpenPrivate

/-! A jointly strict ordinary full-key table determines its native publication from
its two independently ordered physical frames. Promotion trials and casing are derived. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStrictStereoPublication
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels label)
open RingActivePairReport (Slot)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
open RingStereoSiblingPass (order)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open private trial_eq from TetraStereo.Engine.RingFullPathTrialParity
open private strict_injective from TetraStereo.Engine.RingFullPathTrialReadings

/-- The ordinary full-key word, with the native empty promotion suffix. -/
def word (keys : Slot → Key) (k : Slot) := trialKey (keys k) []

/-- The evaluator's descending physical slot row. -/
def row (keys : Slot → Key) : List Slot := order (word keys) (List.finRange 4)

theorem word_injective {keys : Slot → Key} (strict : Function.Injective keys) : Function.Injective (word keys) := by
  intro a b eq
  exact strict ((trial_eq (keys a) (keys b) [] []).mp eq).1

/-- A strict ordinary table has exactly its one unmarked native trial. -/
theorem one_trial {keys : Slot → Key} (strict : Function.Injective keys) :
    RingFullPathTrialReadings.trials keys = [none] := by
  have tied : RingFullPathEligibility.tiedSlots keys = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k _ yes
    obtain ⟨j,_,different,same⟩ := by
      simpa only [List.any_eq_true,Bool.and_eq_true,bne_iff_ne,beq_iff_eq] using yes
    exact different (strict same)
  simp [RingFullPathTrialReadings.trials,RingFullPathEligibility.candidates,tied]

private theorem one_reading {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (keys : Slot → Key) (native : RingFullPathPublication.keys? fr r false = some keys)
    (strict : Function.Injective keys) :
    RingFullPathTrialReadings.readings? fr r false =
      some [(none,RingFullPathTrialReadings.readTrial fr false (word keys))] := by
  unfold RingFullPathTrialReadings.readings?
  change (RingFullPathPublication.keys? fr r false).bind _ = _
  rw [native]
  simp only [Option.bind_some]
  unfold RingFullPathTrialReadings.readingsWith
  rw [one_trial strict]
  simp [RingFullPathTrialReadings.markWords?]
  rfl

private theorem letters_two (x y : Slot → Key) (a b : Option RS)
    (relation : b = if RingFullPathTrialParity.reversals x y % 2 = 0 then a.map RS.swap else a) :
    RingFullPathPublication.letters x y [a] =
      a.bind (fun h => b.map (fun k => (label h k,label k h))) := by
  rw [relation]
  unfold RingFullPathPublication.letters
  by_cases even : RingFullPathTrialParity.reversals x y % 2 = 0
  · simp only [if_pos even]
    cases a with
    | none => rfl
    | some h => cases h <;> rfl
  · simp only [if_neg even]
    cases a with
    | none => rfl
    | some h => cases h <;> rfl

/-- The actual and reflected sorted frames are read independently. Strictness of
both native ordinary tables derives the trial population and the case of each label. -/
theorem centre {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) (r : Reader i) (x y : Slot → Key)
    (actual : RingFullPathPublication.keys? fr r false = some x)
    (reflected : RingFullPathPublication.keys? fr r true = some y)
    (strictX : Function.Injective x) (strictY : Function.Injective y) :
    RingFullPathPublication.centre? fr r = some
      ((readback? (inputGeometry i.certified) (fr.atoms (row x))).bind fun h =>
        (readback? (mirror (inputGeometry i.certified)) (fr.atoms (row y))).map fun k =>
          (label h k,label k h)) := by
  have readings := one_reading fr r x actual strictX
  have relation := RingFullPathTrialParity.trial_mirror fr x y (fun _ => [])
    (fun a b => ⟨fun eq => congrArg y (strictX eq),fun eq => congrArg x (strictY eq)⟩)
    ((RingFullPathTrialReadings.read_exact geom fr false (word x) _).mpr rfl)
    ((RingFullPathTrialReadings.read_exact geom fr true (word y) _).mpr rfl)
  unfold RingFullPathPublication.centre?
  rw [actual,reflected,readings]
  simp only [Option.bind_some,Option.map_some,List.map_cons,List.map_nil]
  rw [letters_two x y _ _ relation]
  unfold RingFullPathTrialReadings.readTrial
  rw [if_pos (strict_injective.mpr (word_injective strictX)),if_pos (strict_injective.mpr (word_injective strictY))]
  rfl

/-- Declarative native key readings determine the actual executable table. -/
theorem keys_of_reads {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (rev : Bool) (keys : Slot → Key)
    (reads : ∀ k, RingFullPathEligibility.Reads i r rev (RingGroupedCentre.cursor fr k) (keys k)) :
    RingFullPathPublication.keys? fr r rev = some keys := by
  have hit (k : Slot) : RingFullPathEligibility.key? i r rev (RingGroupedCentre.cursor fr k) = some (keys k) := by
    obtain ⟨v,native,unique⟩ := RingFullPathEligibility.key_exact ready rev (RingGroupedCentre.cursor fr k)
      (RingGroupedCentre.valid fr k) (fr.direction k).property.1
    rw [(unique (keys k)).mp (reads k)]
    exact native
  unfold RingFullPathPublication.keys? RingActivePairReport.four?
  simp only [hit,Option.bind_eq_bind,Option.bind_some]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Source-reading form of the independent two-frame publication law. -/
theorem centre_of_reads {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (x y : Slot → Key)
    (actual : ∀ k, RingFullPathEligibility.Reads i r false (RingGroupedCentre.cursor fr k) (x k))
    (reflected : ∀ k, RingFullPathEligibility.Reads i r true (RingGroupedCentre.cursor fr k) (y k))
    (strictX : Function.Injective x) (strictY : Function.Injective y) :
    RingFullPathPublication.centre? fr r = some
      ((readback? (inputGeometry i.certified) (fr.atoms (row x))).bind fun h =>
        (readback? (mirror (inputGeometry i.certified)) (fr.atoms (row y))).map fun k =>
          (label h k,label k h)) :=
  centre geom fr r x y (keys_of_reads fr ready false x actual)
    (keys_of_reads fr ready true y reflected) strictX strictY

/-- Strictness exposes the one actual physical reading without any aggregate premise. -/
theorem centre_single {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (x y : Slot → Key)
    (actual : RingFullPathPublication.keys? fr r false = some x)
    (reflected : RingFullPathPublication.keys? fr r true = some y)
    (strictX : Function.Injective x) :
    RingFullPathPublication.centre? fr r = some (RingFullPathPublication.letters x y
      [readback? (inputGeometry i.certified) (fr.atoms (row x))]) := by
  have readings := one_reading fr r x actual strictX
  unfold RingFullPathPublication.centre?
  rw [actual,reflected,readings]
  simp only [Option.bind_some,Option.map_some,List.map_cons,List.map_nil]
  unfold RingFullPathTrialReadings.readTrial
  rw [if_pos (strict_injective.mpr (word_injective strictX))]
  rfl

/-- An ordinary comparison changes direction between the two native tables. -/
def changed (x y : Slot → Key) (p : Slot × Slot) : Bool :=
  decide (word x p.2 < word x p.1) != decide (word y p.2 < word y p.1)

abbrev pairs := LocalizedChemicalRing.ConstitutionalPartition.pairs

theorem reversals_zero {x y : Slot → Key} (same : ∀ p ∈ pairs, changed x y p = false) :
    RingFullPathTrialParity.reversals x y = 0 := by
  apply List.countP_eq_zero.mpr
  intro p member
  change ¬changed x y p = true
  rw [same p member]
  decide

theorem reversals_one {x y : Slot → Key} (p : Slot × Slot) (member : p ∈ pairs)
    (only : ∀ q ∈ pairs, changed x y q = decide (q = p)) :
    RingFullPathTrialParity.reversals x y = 1 := by
  have once : ∀ p ∈ pairs, pairs.countP (fun q => decide (q = p)) = 1 := by decide +kernel
  have count := (List.Perm.refl pairs).countP_congr only
  exact count.trans (once p member)

/-- No changed pair yields an ordinary chiral pair. The reversal count is derived. -/
theorem centre_unchanged {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (x y : Slot → Key)
    (actual : RingFullPathPublication.keys? fr r false = some x)
    (reflected : RingFullPathPublication.keys? fr r true = some y)
    (strictX : Function.Injective x)
    (same : ∀ p ∈ pairs, changed x y p = false) :
    RingFullPathPublication.centre? fr r = some
      ((readback? (inputGeometry i.certified) (fr.atoms (row x))).map fun h => (.chiral h,.chiral h.swap)) := by
  rw [centre_single fr r x y actual reflected strictX]
  unfold RingFullPathPublication.letters
  have zero : RingFullPathPublication.reversals x y = 0 := reversals_zero same
  rw [zero]
  cases readback? (inputGeometry i.certified) (fr.atoms (row x)) with
  | none => rfl
  | some h => cases h <;> rfl

/-- One changed ordinary pair yields the native pseudoasymmetric pair, with no
supplied parity or casing premise. -/
theorem centre_one_changed {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (x y : Slot → Key)
    (actual : RingFullPathPublication.keys? fr r false = some x)
    (reflected : RingFullPathPublication.keys? fr r true = some y)
    (strictX : Function.Injective x) (p : Slot × Slot) (member : p ∈ pairs)
    (only : ∀ q ∈ pairs, changed x y q = decide (q = p)) :
    RingFullPathPublication.centre? fr r = some
      ((readback? (inputGeometry i.certified) (fr.atoms (row x))).map fun h =>
        (.pseudoasymmetric (pseudoRSOfRS h),.pseudoasymmetric (pseudoRSOfRS h))) := by
  rw [centre_single fr r x y actual reflected strictX]
  unfold RingFullPathPublication.letters
  have one : RingFullPathPublication.reversals x y = 1 := reversals_one p member only
  rw [one]
  cases readback? (inputGeometry i.certified) (fr.atoms (row x)) with
  | none => rfl
  | some h => cases h <;> rfl

theorem frame_return {i : Input} {f : Site i} (fr : Frame i f) :
    RingNestedActivePair.frame? i f = some fr := by
  rcases fr with ⟨c,h,four,ids,read,physical⟩
  simp [RingNestedActivePair.frame?,Option.attach_eq_some _ ⟨c,h⟩,four,
    Option.attach_eq_some _ ⟨ids,read⟩,physical]

theorem focusP_none {i : Input} {f : Site i} (fr : Frame i f) :
    RingPyramidalPublication.focusP i f = none := by
  cases selected : RingPyramidalPublication.focusP i f with
  | none => rfl
  | some a =>
    obtain ⟨_,_,three⟩ := RingPyramidalPublication.focusP_neighbors selected
    have four := fr.four
    omega

/-- The executable P-or-tetra publisher agrees with the two-frame law at every
recognized tetrahedral frame. Its fast path is discharged by reader readiness. -/
theorem publish {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (x y : Slot → Key)
    (actual : RingFullPathPublication.keys? fr r false = some x)
    (reflected : RingFullPathPublication.keys? fr r true = some y)
    (strictX : Function.Injective x) (strictY : Function.Injective y) :
    RingPyramidalPublication.publish i f r = some
      ((readback? (inputGeometry i.certified) (fr.atoms (row x))).bind fun h =>
        (readback? (mirror (inputGeometry i.certified)) (fr.atoms (row y))).map fun k =>
          (label h k,label k h)) := by
  simp only [RingPyramidalPublication.publish,focusP_none fr]
  rw [RingFullPathConstitution.fast_local geom ready]
  unfold RingFullPathPublication.publish?
  rw [frame_return fr]
  exact centre geom fr r x y actual reflected strictX strictY

assert_kernel_only publish
assert_kernel_only centre_of_reads
assert_kernel_only centre_unchanged
assert_kernel_only centre_one_changed
assert_kernel_only centre
assert_kernel_only one_trial
end TetraStereo.Engine.RingStrictStereoPublication
