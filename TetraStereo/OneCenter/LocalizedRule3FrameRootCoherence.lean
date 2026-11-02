import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial
import TetraStereo.OneCenter.LocalizedDescriptorBearingRule3Executable
import TetraStereo.OneCenter.LocalizedConstitutionalOriginalRule3Coherence

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def LocalizedRule3FrameRootsExact (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  List.Forall₂ (fun cursor key => key.constitutional.rule1a.head? =
    some [([], input.localizedRerootCursorRootAtomicNumber cursor)]) cursors frame.keys

private theorem mapM_forall₂ {α β : Type*} (f : α → Option β) (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → R a b) :
    ∀ xs ys, xs.mapM f = some ys → List.Forall₂ R xs ys := by
  intro xs
  induction xs with
  | nil => intro ys h; simp at h; subst ys; exact .nil
  | cons a rest ih =>
      intro ys h
      cases ha : f a with
      | none => simp [List.mapM_cons, ha] at h
      | some b =>
          cases hr : rest.mapM f with
          | none => simp [List.mapM_cons, ha, hr] at h
          | some bs =>
              simp [List.mapM_cons, ha, hr] at h
              subst ys
              exact .cons (sound a b ha) (ih bs hr)

/-- The second pass retains the exact constitutional head for every cursor, irrespective of the
physical units excluded by the first pass. No chemical applicability assumption is required. -/
theorem buildLocalizedDescriptorBearingRule3Frame?_rootsExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedDescriptorBearingRule3Frame?
      target view fuel cursors = some frame) : input.LocalizedRule3FrameRootsExact cursors frame := by
  cases fuel with
  | zero => simp [buildLocalizedDescriptorBearingRule3Frame?] at computed
  | succ fuel =>
      unfold buildLocalizedDescriptorBearingRule3Frame? at computed
      cases raw : cursors.mapM
          (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel []) with
      | none => simp [raw] at computed
      | some rawKeys =>
          cases topology : input.localizedRule3CoupledTopologyResolution? rawKeys with
          | none => simp [raw, topology] at computed
          | some resolution =>
              let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys resolution
              cases rebuilt : cursors.mapM
                  (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel excluded) with
              | none => simp [raw, topology, excluded, rebuilt] at computed
              | some keys =>
                  simp [raw, topology, excluded, rebuilt] at computed
                  subst frame
                  exact mapM_forall₂ _ _
                    (input.buildLocalizedRerootDescriptorBearingRule3Key?_constitutional_rule1a_head_observation
                      target view fuel excluded) cursors keys rebuilt

theorem buildLocalizedDescriptorBearingRule3FrameExec?_rootsExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedDescriptorBearingRule3FrameExec?
      target view fuel cursors = some frame) : input.LocalizedRule3FrameRootsExact cursors frame :=
  input.buildLocalizedDescriptorBearingRule3Frame?_rootsExact target view fuel cursors frame
    (by rwa [buildLocalizedDescriptorBearingRule3FrameExec?_eq_original] at computed)

theorem endpoint_rootsExact_of_frame_rootsExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (heads : input.LocalizedRule3FrameRootsExact
      [frame.firstCursor, frame.secondCursor] frame.rule3Frame)
    (keys : frame.rule3Frame.keys =
      [frame.endpointFrame.firstKey.rule3, frame.endpointFrame.secondKey.rule3]) :
    LocalizedRule3EndpointKeyFrame.FirstSphereRootExact frame.endpointFrame
      frame.firstCursor frame.secondCursor := by
  unfold LocalizedRule3FrameRootsExact at heads
  rw [keys] at heads
  cases heads with
  | cons first rest =>
      cases rest with
      | cons second _ => exact ⟨first, second⟩

/-- Exact complete constitutional observations of every rebuilt key, at every successful pure budget. -/
def LocalizedRule3FrameConstitutionalExact (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  List.Forall₂ (fun cursor full => ∀ fuel plain,
    input.buildLocalizedRerootRuleMajorKeyExec? fuel cursor = some plain →
      constitutionalObservable plain = constitutionalObservable full.constitutional) cursors frame.keys

theorem buildLocalizedDescriptorBearingRule3Frame?_constitutionalExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedDescriptorBearingRule3Frame?
      target view fuel cursors = some frame) :
    input.LocalizedRule3FrameConstitutionalExact cursors frame := by
  have meaning := input.buildLocalizedDescriptorBearingRule3Frame?_sound
    target view fuel cursors frame computed
  cases fuel with
  | zero => exact False.elim meaning
  | succ fuel =>
      obtain ⟨_, _, _, _, rebuilt⟩ := meaning
      unfold LocalizedRule3FrameConstitutionalExact
      apply List.Forall₂.imp ?_ rebuilt
      intro cursor full head plainFuel plain plainComputed
      exact input.declarative_constitutional_observable_unique plainFuel fuel _ _ _
        (input.buildLocalizedRerootRuleMajorKeyExec?_sound _ _ _ plainComputed)
        (input.descriptorRule3Key_constitutional_derived target view fuel _ _ _ head)

theorem endpoint_constitutionalExact_of_frame_constitutionalExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (coherent : input.LocalizedRule3FrameConstitutionalExact
      [frame.firstCursor, frame.secondCursor] frame.rule3Frame)
    (keys : frame.rule3Frame.keys =
      [frame.endpointFrame.firstKey.rule3, frame.endpointFrame.secondKey.rule3]) :
    input.LocalizedRule3EndpointConstitutionalExact frame := by
  unfold LocalizedRule3FrameConstitutionalExact at coherent
  rw [keys] at coherent
  cases coherent with
  | cons first rest =>
      cases rest with
      | cons second _ =>
          intro order computed
          obtain ⟨leftKey, rightKey, left, right, compared⟩ :=
            input.compareLocalizedConstitutionalCursors?_computations _ _ order computed
          exact (ruleMajor_compare_congr leftKey rightKey
            frame.endpointFrame.firstKey.rule3.constitutional
            frame.endpointFrame.secondKey.rule3.constitutional
            (first _ _ left) (second _ _ right)).symm.trans compared

/-- Successful original eager geometry is reproduced by short-circuit geometry with the entire
identity-bearing observation unchanged. Frame-head coherence is derived, not supplied by callers. -/
theorem shortCircuitSpatial_preserves_originalFrame_success
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (oldResult : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
      target occurrence view (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) =
        some oldResult) :
    ∃ result, input.localizedRule3ShortCircuitSpatialUnitWith?
      target occurrence view (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) =
        some result ∧ input.localizedRule3ShortCircuitSpatialObservation result =
          input.localizedRule3DescriptorBearingObservation oldResult := by
  let callback := input.buildLocalizedDescriptorBearingRule3Frame? target view fuel
  have derived := input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_sound
    target occurrence view callback (fun cursors frame => callback cursors = some frame)
    (fun _ _ h => h) oldResult computed
  have left := derived.2.1
  have right := derived.2.2.1
  apply input.localizedRule3ShortCircuitSpatialObservation_eq_of_parameterizedWith
    target occurrence view callback oldResult computed
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.leftCompilation
      (input.buildLocalizedDescriptorBearingRule3Frame?_rootsExact target view fuel _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.rightCompilation
      (input.buildLocalizedDescriptorBearingRule3Frame?_rootsExact target view fuel _ _
        right.2.2.2.1) right.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.leftCompilation
      (input.buildLocalizedDescriptorBearingRule3Frame?_constitutionalExact target view fuel _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.rightCompilation
      (input.buildLocalizedDescriptorBearingRule3Frame?_constitutionalExact target view fuel _ _
        right.2.2.2.1) right.2.2.2.2.1

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
