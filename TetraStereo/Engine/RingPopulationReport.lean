import TetraStereo.Engine.RingChemicalReport
import TetraStereo.Engine.RingFullPathReferencePolicy

/-! Exact public reports using the chiral population to select Rule 4b references. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPopulationReport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Frame Labels)
open RingActivePairReport (Slot)
open RingRetainedReferenceGroup (Listing Hit hands references)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
open RingRetainedChemicalTrace (Word)
open RingFullPathPairs (FullSource)
open RingActiveDistanceSchedule (frozen)
open RingChemicalGraphProof (state)
open RingGroupedReport (Report)

/-- The retained population selects no reference, one hand, or two hands.
Only the selected complete words enter the returned priority. -/
def selectedWord (refs : List RS) (w : RS → List Bool) : List Bool :=
  match refs with
  | [] => []
  | [s] => w s
  | s :: t :: _ => max (w s) (w t)

theorem selectedWord_exact {i : Input} {r : Reader i} {q : Arm i} {hs : List Hit} {rev : Bool}
    (listed : Listing i r q hs) {w : RS → List Bool} (legal : ∀ s, FullSource i r rev s q (w s)) :
    selectedWord (references hs rev) w = max (w .R) (w .S) := by
  obtain ⟨block⟩ := RingFullPathReferencePolicy.arm_prefix listed legal
  by_cases empty : hands hs rev = []
  · have nil : hs = [] := (RingRetainedReferenceGroup.group_empty hs).mp (List.map_eq_nil_iff.mp empty)
    subst hs
    rw [RingFullPathReferencePolicy.word_empty listed (legal .R),
      RingFullPathReferencePolicy.word_empty listed (legal .S)]
    rfl
  · change selectedWord (localizedRule4bReferencesFromPopulation (hands hs rev)) w = _
    by_cases balanced : (hands hs rev).count .R = (hands hs rev).count .S
    · rw [RingReferencePrefix.selected_balanced empty balanced]
      rfl
    · obtain ⟨s,sel,best⟩ := RingReferencePrefix.strict_majority_selects_max block empty balanced
      rw [sel,best]
      rfl

/-- A molecular key using only the references selected from its independent
occurrence listing. The other stages retain their graph definitions. -/
def Reads (i : Input) (r : Reader i) (rev : Bool) (a : Arm i) (key : Key) : Prop :=
  ∃ u l hs, ∃ w : RS → List Bool, ∃ fr,
    RingRetainedStereoRefinement.Derives i r rev [] a u ∧
    RingRetainedStereoRefinement.Derives i r rev [.lowercase] a l ∧
    Listing i r a hs ∧ (∀ s, FullSource i r rev s a (w s)) ∧
    RingFullPathRule5.Word i r rev .R a fr ∧
    key = ⟨u.deep,selectedWord (references hs rev) w,l.word,fr⟩

private theorem reads_iff {i : Input} {f : Site i} {r : Reader i} {rev : Bool} {a : Arm i} {key : Key}
    (ready : RingGroupedStereo.Ready f r) (valid : i.certified.LocalizedRerootCursorValid a)
    (onRoot : a.occurrence.val.root = f.val.root) :
    Reads i r rev a key ↔ RingFullPathEligibility.Reads i r rev a key := by
  constructor
  · rintro ⟨u,l,hs,w,fr,hu,hl,lst,words,fixed,rfl⟩
    exact ⟨u,l,w .R,w .S,fr,hu,hl,words .R,words .S,fixed,by rw [selectedWord_exact lst words]⟩
  · rintro ⟨u,l,ar,as',fr,hu,hl,hr,hs,fixed,rfl⟩
    obtain ⟨profile,ok⟩ := RingGroupedStereo.arm_ready ready a valid onRoot
    have listed := (RingGroupedStereo.arm_source ok).hits
    let w : RS → List Bool := fun | .R => ar | .S => as'
    have words : ∀ s, FullSource i r rev s a (w s) := fun | .R => hr | .S => hs
    exact ⟨u,l,_,w,fr,hu,hl,listed,words,fixed,by rw [selectedWord_exact listed words]⟩

/-- On the actual recursively populated store, both Rule 4b procedures
return the signed comparison of the public key, including a surviving tie. -/
theorem reachable_fourB {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) (a b : Arm i)
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (oa : a.occurrence.val.root = f.val.root) (ob : b.occurrence.val.root = f.val.root) :
    let r := frozen (state i) f
    ∃ ka kb : Key, RingFullPathEligibility.key? i r rev a = some ka ∧
      RingFullPathEligibility.key? i r rev b = some kb ∧
      (ka.throughFourA = kb.throughFourA →
        let value := some (RingReferencePrefix.score (compare ka.bestFourB kb.bestFourB))
        RingFullPathPairs.decision? i r rev a b = value ∧ RingFullPathPairs.hanson? i r rev a b = value) := by
  intro r
  have ready := RingChemicalGraphProof.ready geom f
  obtain ⟨ka,gotA,onlyA⟩ := RingFullPathEligibility.key_exact ready rev a va oa
  obtain ⟨kb,gotB,onlyB⟩ := RingFullPathEligibility.key_exact ready rev b vb ob
  refine ⟨ka,kb,gotA,gotB,?_⟩
  intro tie value
  obtain ⟨u,_,ar,as',_,hu,_,har,has,_,rfl⟩ := (onlyA _).mpr rfl
  obtain ⟨v,_,br,bs,_,hv,_,hbr,hbs,_,rfl⟩ := (onlyB _).mpr rfl
  have word (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
      (onRoot : q.occurrence.val.root = f.val.root) (s : RS) (w : List Bool) (legal : FullSource i r rev s q w) :
      RingFullPathPairs.pairs? i r rev s q = some w := by
    obtain ⟨ws,got,eqn⟩ := RingFullPathPairs.source_exact ready rev s q valid onRoot
    rw [(eqn _).mp legal]
    exact got
  rw [RingFullPathReferencePolicy.ready_eq_hanson ready a b va vb oa ob hu hv tie]
  suffices eqn : RingFullPathPairs.hanson? i r rev a b = value from ⟨eqn,eqn⟩
  simp only [RingFullPathPairs.hanson?,word a va oa .R _ har,word a va oa .S _ has,
    word b vb ob .R _ hbr,word b vb ob .S _ hbs, Option.bind_some,Option.bind_eq_bind,Option.pure_def,
    RingOccurrenceStereo.fourLists_order]
  change some _ = some (RingReferencePrefix.score (compare (max ar as') (max br bs)))
  cases compare (max ar as') (max br bs) <;> rfl

def tetraBallots {i : Input} {q : Site i} (fr : Frame i q) (r : Reader i) (rev : Bool)
    (ks : Slot → Key) (votes : List (Option RS)) : Prop :=
  (∀ j, Reads i r rev (RingGroupedCentre.cursor fr j) (ks j)) ∧
    List.Forall₂ (fun s v => ∃ ws, RingFullPathTrialReadings.MarkWords fr r rev s ws ∧
      RingFullPathTrialReadings.Outcome fr rev (fun j => trialKey (ks j) (ws j)) v)
      (RingFullPathTrialReadings.trials ks) votes

def phosphorusBallots {i : Input} {q : Site i} (fr : RingPyramidalSource.Directions i q)
    (r : Reader i) (a : i.certified.Atom) (rev : Bool) (ks : Fin 3 → Key) (votes : List (Option RS)) : Prop :=
  (∀ j, Reads i r rev (fr.arm j) (ks j)) ∧
    List.Forall₂ (fun s v => ∃ ws, RingPyramidalSource.MarkWords fr r rev s ws ∧
      RingPyramidalSource.Outcome fr a rev (fun j => trialKey (ks j) (ws j)) v)
      (RingPyramidalSource.trials ks) votes

/-- Every local assignment and refusal derives its two geometries using the
population-selected ligand keys. -/
inductive Local (i : Input) (q : Site i) (r : Reader i) : Option Labels → Prop where
  | absent (off : RingPyramidalPublication.focusP i q = none)
      (no : i.certified.localizedOccurrenceDescriptorCenter? q = none) : Local i q r none
  | tetra (off : RingPyramidalPublication.focusP i q = none) {fr : Frame i q} {x y hs ms}
      (actual : tetraBallots fr r false x hs) (mirror : tetraBallots fr r true y ms) :
      Local i q r (RingFullPathPublication.crossed hs ms)
  | phosphorus {a} (selected : RingPyramidalPublication.focusP i q = some a)
      {fr : RingPyramidalSource.Directions i q} {x y hs ms}
      (actual : phosphorusBallots fr r a false x hs) (mirror : phosphorusBallots fr r a true y ms) :
      Local i q r (RingFullPathPublication.crossed hs ms)

theorem local_iff {i : Input} {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r) (v) :
    Local i q r v ↔ RingChemicalGraphProof.Local i q r v := by
  have tetra (fr : Frame i q) (rev ks hs) :
      tetraBallots fr r rev ks hs ↔ RingFullPathPublication.Ballots fr r rev ks hs :=
    and_congr_left' (forall_congr' fun j => reads_iff ready (RingGroupedCentre.valid fr j) (fr.direction j).property.1)
  have phosph (fr : RingPyramidalSource.Directions i q) (a rev ks hs) :
      phosphorusBallots fr r a rev ks hs ↔ RingPyramidalSource.Ballots fr r a rev ks hs :=
    and_congr_left' (forall_congr' fun j => reads_iff ready (fr.valid j) (fr.rooted j))
  constructor
  · intro d
    cases d with
    | absent off no => simpa [RingChemicalGraphProof.Local,off] using RingFullPathPublication.TwoGeometry.absent (r := r) no
    | tetra off actual mirror =>
      simp only [RingChemicalGraphProof.Local,off]
      exact .centre ((tetra ..).mp actual) ((tetra ..).mp mirror)
    | phosphorus sel actual mirror =>
      simp only [RingChemicalGraphProof.Local,sel]
      exact ⟨_,_,_,_,_,(phosph ..).mp actual,(phosph ..).mp mirror,rfl⟩
  · intro h
    cases sel : RingPyramidalPublication.focusP i q with
    | none =>
      simp only [RingChemicalGraphProof.Local,sel] at h
      cases h with
      | absent no => exact .absent sel no
      | centre actual mirror => exact .tetra sel ((tetra ..).mpr actual) ((tetra ..).mpr mirror)
    | some a =>
      simp only [RingChemicalGraphProof.Local,sel] at h
      obtain ⟨fr,x,y,hs,ms,actual,mirror,rfl⟩ := h
      exact .phosphorus sel ((phosph ..).mpr actual) ((phosph ..).mpr mirror)

theorem root_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (v : Option Labels) :
    RingChemicalGraphProof.root i a = some v ↔
    RingEligibleGraph.Derives (RingPyramidalPublication.eligible i) (Local i) a .origin v := by
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i)]
  symm
  apply RingEligibleGraph.derives_iff_store (state i) _ (RingChemicalGraphProof.complete geom) _ .origin v
  · intro q no
    exact (RingChemicalGraphProof.state_eq i q).trans (RingChemicalGraphProof.skips i q _ no)
  · intro q w
    exact (local_iff (RingChemicalGraphProof.ready geom q) w).trans (RingChemicalGraphProof.local_iff geom q w)

def Correct (i : Input) (atoms : List i.certified.Atom) (rows : Report) : Prop :=
  List.Forall₂ (fun a (row : Nat × Option Labels) => row.1 = a.val ∧
    RingEligibleGraph.Derives (RingPyramidalPublication.eligible i) (Local i) a .origin row.2) atoms rows

/-- The raw public report is exactly the graph derivation with population-selected
Rule 4b references at every root and every recursively used auxiliary centre. -/
theorem fromRaw_iff (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    RingChemicalReport.fromRaw? m g ids = some rows ↔ ∃ source : Input,
      LocalizedChemicalRing.admitRawSpatial? m g = some source ∧
      (∃ atoms : List source.certified.Atom, atoms.map Fin.val = ids) ∧
      ∃ i, RingChemicalReport.Prepared source i ∧ ∃ atoms : List i.certified.Atom,
        atoms.map Fin.val = ids ∧ Correct i atoms rows := by
  rw [RingChemicalReport.fromRaw_graph_iff]
  apply exists_congr
  intro source
  apply and_congr_right'
  apply and_congr_right'
  apply exists_congr
  intro i
  apply and_congr_right
  intro prep
  obtain ⟨_,_,_,_,geom⟩ := prep.2
  apply exists_congr
  intro atoms
  apply and_congr_right'
  constructor
  · intro h
    exact h.imp (fun a row d => ⟨d.1,(root_iff geom a row.2).mp ((RingChemicalGraphProof.root_iff geom a row.2).mpr d.2)⟩)
  · intro h
    exact h.imp (fun a row d => ⟨d.1,(RingChemicalGraphProof.root_iff geom a row.2).mp ((root_iff geom a row.2).mpr d.2)⟩)

end TetraStereo.Engine.RingPopulationReport
assert_kernel_only TetraStereo.Engine.RingPopulationReport.reachable_fourB
assert_kernel_only TetraStereo.Engine.RingPopulationReport.fromRaw_iff
