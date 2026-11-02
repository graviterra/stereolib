import TetraStereo.OneCenter.LocalizedAutomaticComparisonRank
import TetraStereo.OneCenter.LocalizedTetrahedralPermutationExistence
import TetraStereo.OneCenter.LocalizedShortCircuitStrictCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Every independently derived first pass has a coupled-topology resolution. This condition
does not supply a successful recursive callback or a completed key frame. -/
def LocalizedLinearRule3TopologyResolvable (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame fuel) : Prop :=
  ∀ rawKeys, List.Forall₂ (input.DeclarativeLocalizedRerootShortCircuitRule3Key
    target view (2 * (fuel + 1) + 1) []) base.cursors rawKeys →
    ∃ topology, input.DeclarativeLocalizedRule3CoupledTopologyResolution rawKeys topology

private theorem mapM_total {α β : Type} (f : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results, values.mapM f = some results
  | [], _ => ⟨[], rfl⟩
  | value :: values, total => by
      obtain ⟨result, head⟩ := total value (by simp)
      obtain ⟨rest, tail⟩ := mapM_total f values
        (fun value present => total value (by simp [present]))
      exact ⟨result :: rest, by simp [head, tail]⟩

/-- Structural readiness and independent topology resolution construct the complete production
frame at its existing fuel. Both Rule3 passes and every Rule45 key are produced in the proof. -/
theorem fullKeyFrame_exists_of_readiness
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame fuel)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base)
    (unambiguous : input.LocalizedLinearRule3TopologyResolvable target view base) :
    ∃ keys, input.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?
      target view base = some keys := by
  have valid : ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor := by
    intro cursor present
    exact input.localizedRerootChild_valid { occurrence := target, previous? := none }
      cursor base.cursors baseMeaning.1 present
  obtain ⟨rawKeys, rawComputed, frameIff⟩ := input.shortCircuitRule3Frame_at_linear_bound
    callbackFree target view base.cursors valid
  have rawDerived : List.Forall₂ (input.DeclarativeLocalizedRerootShortCircuitRule3Key
      target view (2 * (fuel + 1) + 1) []) base.cursors rawKeys := by
    apply List.Forall₂.imp ?_ (TerminalTie.mapM_forall₂ _ _ _ rawComputed)
    intro cursor key computed
    exact input.buildLocalizedRerootShortCircuitRule3KeyExec?_sound
      target view (2 * (fuel + 1) + 1) [] cursor key computed
  obtain ⟨frame, frameComputed⟩ := frameIff.mpr (unambiguous rawKeys rawDerived)
  have frameDerived := input.buildLocalizedShortCircuitRule3FrameExec?_sound
    target view (2 * (fuel + 1) + 2) base.cursors frame frameComputed
  have frameLength : frame.keys.length = 4 := by
    obtain ⟨_, _, _, _, keysDerived⟩ := frameDerived
    exact keysDerived.length_eq.symm.trans base.length_eq
  have productionFrame : input.buildLocalizedShortCircuitRule3FrameExec?
      target view (localizedDescriptorBearingRule3EvaluationFuel fuel) base.cursors = some frame := by
    rw [input.shortCircuitRule3Frame_stable_above_linear_bound callbackFree
      target target view view base.cursors valid
      (localizedDescriptorBearingRule3EvaluationFuel fuel) (2 * (fuel + 1) + 2)
      (shortCircuit_linear_bound_le_production fuel) (Nat.le_refl _)]
    exact frameComputed
  obtain ⟨rule45Keys, rule45Computed⟩ := mapM_total
    (input.buildLocalizedRerootCompoundRule45KeyExec? target view
      (localizedOccurrenceRerootEvaluationFuel fuel)) base.cursors (by
        intro cursor present
        obtain ⟨key, computed⟩ := input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor present)
        refine ⟨key, ?_⟩
        rw [← buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
        exact computed)
  have rule45Four : rule45Keys.length = 4 :=
    (TerminalTie.mapM_forall₂ _ _ _ rule45Computed).length_eq.symm.trans base.length_eq
  let keys : input.LocalizedOccurrenceRule3Through5KeyFrame fuel :=
    { rule3Frame := frame, rule3Length := frameLength, rule45Keys, rule45Length := rule45Four }
  refine ⟨keys, ?_⟩
  simp [buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?,
    productionFrame, frameLength, rule45Computed, rule45Four, keys]

/-- Independent sufficient conditions at one actual auxiliary view. These permit decisive
Rule45 comparisons, supply no priority order or descriptor, and require only nonzero volume
in the canonical four slots. Separation quantifies independent derivations; checking one computed
frame alone does not establish this universal field. -/
structure LocalizedRankedTetrahedralReadiness
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) where
  callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate fuel
  center : input.TetrahedralCenter
  centerMeaning : input.RealTetrahedralCenterNode target.1.node center
  base : input.LocalizedOccurrenceFourLigandFrame fuel
  baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base
  unambiguous : input.LocalizedLinearRule3TopologyResolvable target view base
  separated : ∀ frame,
    input.DeclarativeLocalizedOccurrenceShortCircuitRule3Through5KeyFrame target view base frame →
      input.FullComparisonSeparated frame
  point : Fin 4 → CartesianPoint3
  pointsMeaning : ∀ i, input.DeclarativeLocalizedRerootCursorSpatialPoint (base.cursorAt i) (point i)
  nonzero : CartesianPoint3.orientedVolume (point 0) (point 1) (point 2) (point 3) ≠ 0

/-- The full existing descriptor evaluator succeeds under independent readiness. Recursion,
complete keys, ordering, coherence, spatial ordering and the final label are all constructed.
The actual executed pseudo count determines uppercase versus lowercase classification. -/
theorem ranked_descriptor_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (ready : input.LocalizedRankedTetrahedralReadiness target view) :
    ∃ descriptor, input.localizedOccurrenceShortCircuitRule3Through5Descriptor?
      target view = some descriptor := by
  obtain ⟨keys, keysComputed⟩ := input.fullKeyFrame_exists_of_readiness
    ready.callbackFree target view ready.base ready.baseMeaning ready.unambiguous
  have keysMeaning := input.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?_sound
    target view ready.base keys keysComputed
  obtain ⟨tracked, trackedComputed, permutation, _⟩ :=
    input.trackedOrder_total_of_separated keys (ready.separated keys keysMeaning)
  obtain ⟨raw, geometry⟩ := rationalTetrahedralDescriptor_exists_of_permutation
    ready.point tracked.highestFirst permutation ready.nonzero
  have pointComputed : ∀ i, input.localizedRerootCursorSpatialPoint? (ready.base.cursorAt i) =
      some (ready.point i) := fun i =>
    (input.localizedRerootCursorSpatialPoint?_eq_some_iff _ _).mpr (ready.pointsMeaning i)
  have pointsComputed : tracked.highestFirst.mapM (fun i =>
      input.localizedRerootCursorSpatialPoint? (ready.base.cursorAt i)) =
        some (tracked.highestFirst.map ready.point) := by
    induction tracked.highestFirst with
    | nil => rfl
    | cons i rest ih =>
        simp only [List.mapM_cons, pointComputed i, ih, List.map_cons]
        rfl
  have centerComputed := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
    target ready.center).mpr ready.centerMeaning
  have baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some ready.base := by
    rw [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target ready.base).mpr ready.baseMeaning
  let evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence fuel :=
    { center := ready.center, base := ready.base, keys, tracked,
      points := tracked.highestFirst.map ready.point }
  have evidenceComputed : input.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?
      target view = some evidence := by
    simp [localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?, centerComputed,
      baseComputed, keysComputed, trackedComputed, pointsComputed, evidence]
  have geometryComputed := (descriptorOfPriorityOrderedPoints?_eq_some_iff _ raw).mpr geometry
  refine ⟨classifyTetrahedralRSPseudo raw tracked.pseudoComparisons, ?_⟩
  simp [localizedOccurrenceShortCircuitRule3Through5Descriptor?, evidenceComputed,
    evidence, geometryComputed]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
