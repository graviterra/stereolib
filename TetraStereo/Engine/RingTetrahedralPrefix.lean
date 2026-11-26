import TetraStereo.Engine.RingStrictStereoPublication

/-! The independently executed complete Rule 4a prefix decides every strict
four-ligand frame before any Rule 4b, Rule 4c, Rule 5 or active mark is evaluated. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingTetrahedralPrefix
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels)
open RingActivePairReport (Slot)
open RingRetainedChemicalTrace (Word)
open RingStereoSiblingPass (Branch order)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- Only the ordinary unit-class pass is executed. Its deep key contains
all of Rules 1a, 1b, 2 and 4a, including the complete recursive queues. -/
def keys? {i : Input} {q : Site i} (fr : Frame i q) (r : Reader i) :
    Option (Slot → List Word) :=
  RingActivePairReport.four? fun s =>
    (RingRetainedStereoRefinement.priority i r false [] (RingGroupedCentre.cursor fr s)).map Branch.deep

def row (ks : Slot → List Word) : List Slot := order ks (List.finRange 4)

def result {i : Input} {q : Site i} (fr : Frame i q) (ks : Slot → List Word) : Option Labels :=
  (readback? (inputGeometry i.certified) (fr.atoms (row ks))).map
    fun h => (.chiral h,.chiral h.swap)

/-- Failure means either no frame, an unavailable reader, or a genuine prefix tie.
The successful branch performs no later stereo pass. -/
def early? (i : Input) (q : Site i) (r : Reader i) : Option (Option Labels) := do
  let fr ← RingNestedActivePair.frame? i q
  let ks ← keys? fr r
  if Function.Injective ks then return result fr ks else none

/-- Ready frames have an independently computed full prefix table. -/
theorem keys_total {i : Input} {q : Site i} (fr : Frame i q) {r : Reader i}
    (ready : RingGroupedStereo.Ready q r) : ∃ ks, keys? fr r = some ks := by
  apply Option.isSome_iff_exists.mp
  apply RingActivePairReport.four_full
  intro s
  obtain ⟨b,h⟩ := RingOccurrenceStereo.rank_total ready false []
    (RingGroupedCentre.cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  change RingRetainedStereoRefinement.priority i r false [] (RingGroupedCentre.cursor fr s) = some b at h
  exact Option.isSome_iff_exists.mpr ⟨b.deep,by simp [h]⟩

/-- Every native full key projects to the independently executed Rule 4a key,
on either geometry. This uses no equality assumption about final priorities. -/
theorem projects {i : Input} {q : Site i} (fr : Frame i q) {r : Reader i}
    {ks : Slot → List Word} (hit : keys? fr r = some ks) (rev : Bool)
    {s : Slot} {k : Key}
    (read : RingFullPathEligibility.Reads i r rev (RingGroupedCentre.cursor fr s) k) :
    k.throughFourA = ks s := by
  obtain ⟨u,l,ar,as',fixed,du,dl,ha,hb,hf,rfl⟩ := read
  have slotHit :=  RingActivePairReport.four_at hit s
  obtain ⟨b,hb,value⟩ := Option.map_eq_some_iff.mp slotHit
  have source := RingRetainedUnitPass.source i r rev _ _ hb
  have same := RingRetainedUnitPass.Reading.unique du source
  exact (congrArg Branch.deep same).trans value

private theorem trial_lt {a b : Key} (ne : a.throughFourA ≠ b.throughFourA) :
    trialKey a [] < trialKey b [] ↔ a.throughFourA < b.throughFourA := by
  simp only [trialKey,List.cons_lt_cons_iff]
  simp [ne]

private theorem sorted {ks : Slot → List Word} (strict : Function.Injective ks)
    {x : Slot → Key} (shape : ∀ s, (x s).throughFourA = ks s) :
    RingStrictStereoPublication.row x = row ks := by
  unfold RingStrictStereoPublication.row row RingStereoSiblingPass.order
  apply congrArg (fun cmp => (List.finRange 4).mergeSort cmp)
  funext a b
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [←not_lt,←not_lt]
  by_cases eqn : a = b
  · subst b; simp
  · change (¬trialKey (x a) [] < trialKey (x b) []) ↔ ¬ks a < ks b
    rw [trial_lt (by rw [shape a,shape b]; exact strict.ne eqn),shape a,shape b]

private theorem native {i : Input} {q : Site i} (fr : Frame i q) {r : Reader i}
    (ready : RingGroupedStereo.Ready q r) (rev : Bool) :
    ∃ x, RingFullPathPublication.keys? fr r rev = some x ∧
      ∀ s, RingFullPathEligibility.Reads i r rev (RingGroupedCentre.cursor fr s) (x s) := by
  have each (s : Slot) := RingFullPathEligibility.key_exact ready rev (RingGroupedCentre.cursor fr s)
    (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  choose x computed unique using each
  exact ⟨x,RingStrictStereoPublication.keys_of_reads fr ready rev x
    (fun s => (unique s _).mpr rfl),fun s => (unique s _).mpr rfl⟩

/-- Native publication from the independently sorted physical row, with uppercase
opposite labels and with validity retained as the inner optional result. -/
theorem publish {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} (fr : Frame i q) {r : Reader i} (ready : RingGroupedStereo.Ready q r)
    {ks : Slot → List Word} (hit : keys? fr r = some ks) (strict : Function.Injective ks) :
    RingPyramidalPublication.publish i q r = some (result fr ks) := by
  obtain ⟨x,hx,rx⟩ := native fr ready false
  obtain ⟨y,hy,ry⟩ := native fr ready true
  have sx (s : Slot) := projects fr hit false (rx s)
  have sy (s : Slot) := projects fr hit true (ry s)
  have inj : Function.Injective x := fun a b eqn => strict (by rw [←sx a,←sx b,eqn])
  have unchanged : ∀ p ∈ RingStrictStereoPublication.pairs,
      RingStrictStereoPublication.changed x y p = false := by
    intro p hp
    have ne := ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp hp)
    have nx : (x p.2).throughFourA ≠ (x p.1).throughFourA := by
      rw [sx,sx]; exact strict.ne ne.symm
    have ny : (y p.2).throughFourA ≠ (y p.1).throughFourA := by
      rw [sy,sy]; exact strict.ne ne.symm
    simp only [RingStrictStereoPublication.changed,RingStrictStereoPublication.word]
    simp [trial_lt nx,trial_lt ny,sx,sy]
  simp only [RingPyramidalPublication.publish,RingStrictStereoPublication.focusP_none fr]
  rw [RingFullPathConstitution.fast_local geom ready]
  unfold RingFullPathPublication.publish?
  rw [RingStrictStereoPublication.frame_return fr]
  change RingFullPathPublication.centre? fr r = _
  rw [RingStrictStereoPublication.centre_unchanged fr r x y hx hy inj unchanged,sorted strict sx]
  rfl

theorem early_sound {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r) {out : Option Labels}
    (hit : early? i q r = some out) : RingPyramidalPublication.publish i q r = some out := by
  unfold early? at hit
  obtain ⟨fr,hfr,tail⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨ks,hks,tail⟩ := Option.bind_eq_some_iff.mp tail
  split at tail
  next strict => cases Option.some.inj tail; exact publish geom fr ready hks strict
  next no => contradiction

/-- For a framed ready site, missing the shortcut exhibits two distinct ligands
with genuinely equal complete through-4a molecular keys. -/
theorem missed_tie {i : Input} {q : Site i} (fr : Frame i q) {r : Reader i}
    (ready : RingGroupedStereo.Ready q r) (miss : early? i q r = none) :
    ∃ ks, keys? fr r = some ks ∧ ∃ a b : Slot, a ≠ b ∧ ks a = ks b := by
  obtain ⟨ks,hit⟩ := keys_total fr ready
  have nonstrict : ¬Function.Injective ks := by
    intro strict
    simp [early?,RingStrictStereoPublication.frame_return fr,hit,strict] at miss
  classical
  have pair : ∃ a b, ks a = ks b ∧ a ≠ b := by
    by_contra no
    apply nonstrict
    intro a b eqn
    by_contra ne
    exact no ⟨a,b,eqn,ne⟩
  obtain ⟨a,b,eqn,ne⟩ := pair
  exact ⟨ks,hit,a,b,ne,eqn⟩

/-- Successful physical readback is exactly the condition for an uppercase
opposite pair; an invalid or degenerate row remains an explicit inner failure. -/
theorem result_valid {i : Input} {q : Site i} (fr : Frame i q)
    (ks : Slot → List Word) (h : RS) :
    readback? (inputGeometry i.certified) (fr.atoms (row ks)) = some h →
    result fr ks = some (.chiral h,.chiral h.swap) := by
  intro hit
  simp [result,hit]

assert_kernel_only keys_total
assert_kernel_only projects
assert_kernel_only publish
assert_kernel_only early_sound
assert_kernel_only missed_tie
assert_kernel_only result_valid
end TetraStereo.Engine.RingTetrahedralPrefix
