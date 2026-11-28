import TetraStereo.Engine.RingObservedTreeMatch

/-! Refusal from a single unmarked molecular branch exchange. The two
spectators are separated by their constitutional words, which include
atomic number, duplicate origin and isotope mass. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingUnmarkedExchange
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActivePairReport (Slot)
open RingNestedActivePair (Frame Reader)
open RingGroupedCentre (cursor)
open RingFullPathEligibility (Key Reads tiedSlots)
open RingFullPathConstitution (word through_extends)
open RingFullPathTrialReadings (trials trialKey MarkWords Outcome)
open RingGeometryExchange (Carrier Frozen)

private def repeatedWords (words : Vector (List RingRetainedChemicalTrace.Word) 4) : List Slot :=
  (List.finRange 4).filter fun u => (List.finRange 4).any fun v =>
    u != v && words[u] == words[v]

/-- Slots sharing a complete constitutional word with a different slot. -/
def repeated {i : Input} {f : Site i} (fr : Frame i f) : List Slot :=
  repeatedWords (Vector.ofFn (word fr))

/-- Share one child index for the original root across the four key traversals. -/
private def cachedRepeated {i : Input} {f : Site i} (fr : Frame i f) : List Slot :=
  let index := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache
    (i.certified.localizedRerootCarrierCache (i.certified.certified.input.molecule.atomCount + 1)) f.val.root
  repeatedWords (Vector.ofFn fun s =>
    ((RingRetainedChemicalTrace.keyWith i index.reader (cursor fr s)).map
      RingRetainedChemicalPreorder.orderWord).getD [])

@[csimp] private theorem repeated_cached : @repeated = @cachedRepeated := by
  funext i f fr
  simp only [repeated,cachedRepeated,RingRetainedChemicalTrace.keyWith_eq,cursor,
    RingRetainedChemicalPreorder.read_key,Option.map_some,Option.getD_some]
  rfl

/-- Ties after Rule 5 refine constitutional ties on either geometry. -/
theorem ties_sublist {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i} {rev : Bool}
    {keys : Slot → Key} (actual : ∀ s, Reads i r rev (cursor fr s) (keys s)) :
    (tiedSlots keys).Sublist (repeated fr) := by
  apply List.sublist_filter_iff.mpr
  refine ⟨tiedSlots keys,List.filter_sublist,?_⟩
  symm
  apply List.filter_eq_self.mpr
  intro s hs
  obtain ⟨t,ne,tie⟩ := (RingFullPathEligibility.mem_tied keys s).mp hs
  obtain ⟨_,left⟩ := through_extends fr (actual s)
  obtain ⟨_,right⟩ := through_extends fr (actual t)
  have same := left.symm.trans ((congrArg Key.throughFourA tie).trans right)
  have eqn : word fr s = word fr t := List.append_inj_left same rfl
  exact List.any_eq_true.mpr ⟨t,List.mem_finRange _,by simpa using And.intro ne eqn⟩

theorem only_unmarked {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i} {rev : Bool}
    {keys : Slot → Key} (actual : ∀ s, Reads i r rev (cursor fr s) (keys s))
    (few : (repeated fr).length < 3) : trials keys = [none] := by
  have limit := lt_of_le_of_lt (ties_sublist fr actual).length_le few
  simp [trials,RingFullPathEligibility.candidates,Nat.not_le.mpr limit]

/-- One arbitrary-depth exchange preserves every ordinary key component.
Because no marked trial is scheduled, no marked-atom correspondence is required. -/
theorem publish_refusal {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (tetra : RingPyramidalPublication.focusP i f = none)
    (ready : RingGroupedStereo.Ready f r) (few : (repeated fr).length < 3)
    {u v : Slot} (ne : u ≠ v) (c : Carrier i i) (start : c.domain (cursor fr u))
    (target : c.image (cursor fr u) = cursor fr v) (frozen : Frozen c r r) :
    RingPyramidalPublication.publish i f r = some none := by
  have keys (rev : Bool) : ∃ ks : Slot → Key, ∀ s, Reads i r rev (cursor fr s) (ks s) := by
    have each (s : Slot) := RingFullPathEligibility.key_exact ready rev (cursor fr s)
      (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    choose ks _ unique using each
    exact ⟨ks,fun s => (unique s _).mpr rfl⟩
  obtain ⟨ks,actual⟩ := keys false
  obtain ⟨ms,mirrored⟩ := keys true
  have equal := RingFullPathKeyTransport.reads_transport c frozen false start (actual u) (target.symm ▸ actual v)
  have complete : List.Forall₂ (fun m h => ∃ ws, MarkWords fr r false m ws ∧
      Outcome fr false (fun s => trialKey (ks s) (ws s)) h) (trials ks) [none] := by
    rw [only_unmarked fr actual few]
    exact .cons ⟨fun _ => [],fun _ => rfl,.tie ne (by rw [equal])⟩ .nil
  have source := RingFullPathPublication.Source.centre fr ks ms actual mirrored [none] complete
  change RingFullPathPublication.Source i f r none at source
  obtain ⟨v,hv,exactness⟩ := RingFullPathPublication.source_exact geom ready
  rw [RingPyramidalPublication.publish,tetra,RingFullPathConstitution.fast_local geom ready,hv,
    ← (exactness none).mp source]

theorem state_refusal {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (tetra : RingPyramidalPublication.focusP i f = none) (few : (repeated fr).length < 3)
    {u v : Slot} (ne : u ≠ v) (c : Carrier i i) (start : c.domain (cursor fr u))
    (target : c.image (cursor fr u) = cursor fr v)
    (frozen : let read := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
              Frozen c read read) : RingChemicalGraphProof.state i f = some none :=
  (RingChemicalGraphProof.state_eq i f).trans
    (publish_refusal fr geom tetra (RingChemicalGraphProof.ready geom f) few ne c start target frozen)

/-- Test only the two repeated constitutional slots. This tree match checks the
current stereo observations and never evaluates a marked-atom word. -/
def check {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Bool :=
  match repeated fr with
  | [u,v] => u != v && (RingObservedTreeMatch.unmarked? fr r u v).isSome
  | _ => false

theorem checked_publish {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (tetra : RingPyramidalPublication.focusP i f = none) (ready : RingGroupedStereo.Ready f r)
    (ok : check fr r = true) : RingPyramidalPublication.publish i f r = some none := by
  unfold check at ok
  split at ok
  · rename_i u v pattern
    obtain ⟨ne,found⟩ := Bool.and_eq_true_iff.mp ok
    let match' := Option.get _ found
    exact publish_refusal fr geom tetra ready (by simp [pattern]) (bne_iff_ne.mp ne)
      match'.carrier match'.start match'.target match'.frozen
  · contradiction

theorem checked_state {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (tetra : RingPyramidalPublication.focusP i f = none)
    (ok : check fr (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f) = true) :
    RingChemicalGraphProof.state i f = some none :=
  (RingChemicalGraphProof.state_eq i f).trans
    (checked_publish fr geom tetra (RingChemicalGraphProof.ready geom f) ok)

end TetraStereo.Engine.RingUnmarkedExchange

assert_kernel_only TetraStereo.Engine.RingUnmarkedExchange.ties_sublist
assert_kernel_only TetraStereo.Engine.RingUnmarkedExchange.publish_refusal

assert_kernel_only TetraStereo.Engine.RingUnmarkedExchange.state_refusal
assert_kernel_only TetraStereo.Engine.RingUnmarkedExchange.checked_publish
assert_kernel_only TetraStereo.Engine.RingUnmarkedExchange.checked_state
