import TetraStereo.OneCenter.LocalizedShortCircuitStrictOrder
import TetraStereo.OneCenter.LocalizedShortCircuitFuelStability

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Independent finite conditions for a tetrahedral center whose complete ligand order is
settled by Rule3. The carrier witness is produced by the existing readiness checker; the remaining
fields state topology uniqueness, rank separation and molecule-backed geometry. No completed
key frame, descriptor computation, auxiliary state or successful recursive callback is supplied. -/
structure LocalizedStrictRule3TetrahedralReadiness
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (raw : RS) where
  callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel
  center : input.TetrahedralCenter
  centerMeaning : input.RealTetrahedralCenterNode target.1.node center
  base : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base
  unambiguous : ∀ rawKeys,
    List.Forall₂ (input.DeclarativeLocalizedRerootShortCircuitRule3Key
      target (fun _ _ => none) (2 * (carrierFuel + 1) + 1) []) base.cursors rawKeys →
    ∃ topology, input.DeclarativeLocalizedRule3CoupledTopologyResolution rawKeys topology
  priority : Fin 4 → Nat
  priorityInjective : Function.Injective priority
  ranked : ∀ (frame : input.LocalizedRule3CanonicalKeyFrame)
      (length : frame.keys.length = 4),
    input.DeclarativeLocalizedShortCircuitRule3Frame target (fun _ _ => none)
      (2 * (carrierFuel + 1) + 2) base.cursors frame →
    ∀ left right : Fin 4, left ≠ right →
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (frame.keys.get (Fin.cast length.symm left))
        (frame.keys.get (Fin.cast length.symm right)) =
          compare (priority left) (priority right)
  order : List (Fin 4)
  permutation : order.Perm (List.finRange 4)
  descending : order.Pairwise (fun left right => priority right < priority left)
  points : List CartesianPoint3
  pointsMeaning : List.Forall₂
    (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
      (base.cursorAt index) point) order points
  geometry : RationalTetrahedralDescriptor points raw

private theorem mapM_meaning {α β : Type} (f : α → Option β) (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → R a b) :
    ∀ values results, (values : List α).mapM f = some results → List.Forall₂ R values results
  | [], results, computed => by simp at computed; subst results; exact .nil
  | value :: values, results, computed => by
      cases head : f value with
      | none => simp [head] at computed
      | some result =>
          cases tail : values.mapM f with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst results
              exact .cons (sound value result head) (mapM_meaning f R sound values rest tail)

private theorem mapM_total_length {α β : Type} (f : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results, values.mapM f = some results ∧ results.length = values.length
  | [], _ => ⟨[], rfl, rfl⟩
  | value :: values, total => by
      obtain ⟨result, head⟩ := total value (by simp)
      obtain ⟨rest, tail, length⟩ := mapM_total_length f values
        (fun value present => total value (by simp [present]))
      exact ⟨result :: rest, by simp [head, tail], by simp [length]⟩

private theorem spatial_map_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points, List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (base.cursorAt index) point) order points →
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
        (base.cursorAt index)) = some points
  | [], [], .nil => rfl
  | index :: order, point :: points, .cons head tail => by
      have computed := (input.localizedRerootCursorSpatialPoint?_eq_some_iff
        (base.cursorAt index) point).mpr head
      simp [computed, input.spatial_map_complete base order points tail]

/-- The linear frame bound lies below the production bound for every carrier size. -/
theorem shortCircuit_linear_bound_le_production (carrierFuel : Nat) :
    2 * (carrierFuel + 1) + 2 ≤ localizedDescriptorBearingRule3EvaluationFuel carrierFuel := by
  unfold localizedDescriptorBearingRule3EvaluationFuel
  nlinarith

/-- The independent readiness conditions force actual descriptor production under EVERY
auxiliary view. Both Rule3 passes, all Rule45 keys, tracked sorting, the coherence guard and
rational geometry are constructed in the proof, rather than assumed successful. -/
theorem strictRule3_descriptor_total_all_views
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (raw : RS)
    (ready : input.LocalizedStrictRule3TetrahedralReadiness target raw) :
    ∀ view : input.LocalizedDependencyView target,
      input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view = some (.chiral raw) := by
  let initialView : input.LocalizedDependencyView target := fun _ _ => none
  have valid : ∀ cursor ∈ ready.base.cursors, input.LocalizedRerootCursorValid cursor := by
    intro cursor present
    exact input.localizedRerootChild_valid { occurrence := target, previous? := none }
      cursor ready.base.cursors ready.baseMeaning.1 present
  obtain ⟨rawKeys, rawComputed, frameIff⟩ := input.shortCircuitRule3Frame_at_linear_bound
    ready.callbackFree target initialView ready.base.cursors valid
  have rawDerived := mapM_meaning
    (input.buildLocalizedRerootShortCircuitRule3KeyExec?
      target initialView (2 * (carrierFuel + 1) + 1) [])
    (input.DeclarativeLocalizedRerootShortCircuitRule3Key
      target initialView (2 * (carrierFuel + 1) + 1) [])
    (input.buildLocalizedRerootShortCircuitRule3KeyExec?_sound
      target initialView (2 * (carrierFuel + 1) + 1) []) _ _ rawComputed
  obtain ⟨frame, frameComputed⟩ := frameIff.mpr (ready.unambiguous rawKeys rawDerived)
  have frameDerived := input.buildLocalizedShortCircuitRule3FrameExec?_sound
    target initialView (2 * (carrierFuel + 1) + 2) ready.base.cursors frame frameComputed
  have frameLength : frame.keys.length = 4 := by
    obtain ⟨_, topology, _, _, keysDerived⟩ := frameDerived
    exact keysDerived.length_eq.symm.trans ready.base.length_eq
  intro view
  have productionFrame : input.buildLocalizedShortCircuitRule3FrameExec?
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      ready.base.cursors = some frame := by
    rw [input.shortCircuitRule3Frame_stable_above_linear_bound ready.callbackFree
      target target view initialView ready.base.cursors valid
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      (2 * (carrierFuel + 1) + 2)
      (shortCircuit_linear_bound_le_production carrierFuel) (Nat.le_refl _)]
    exact frameComputed
  obtain ⟨rule45Keys, rule45Computed, rule45Length⟩ := mapM_total_length
    (input.buildLocalizedRerootCompoundRule45KeyExec? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) ready.base.cursors (by
        intro cursor present
        obtain ⟨key, computed⟩ := input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor present)
        refine ⟨key, ?_⟩
        rw [← buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
        exact computed)
  have rule45Four : rule45Keys.length = 4 := rule45Length.trans ready.base.length_eq
  let keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel :=
    { rule3Frame := frame, rule3Length := frameLength, rule45Keys, rule45Length := rule45Four }
  have keysComputed : input.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?
      target view ready.base = some keys := by
    simp [buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?,
      productionFrame, frameLength, rule45Computed, rule45Four, keys]
  have ranked : ∀ left right, left ≠ right →
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (keys.keyAt left).rule3 (keys.keyAt right).rule3 =
          compare (ready.priority left) (ready.priority right) :=
    ready.ranked frame frameLength frameDerived
  have trackedComputed := input.trackedOrder_total_of_strictRule3 keys ready.priority
    ready.priorityInjective ranked ready.order ready.permutation ready.descending
  have centerComputed := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
    target ready.center).mpr ready.centerMeaning
  have baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some ready.base := by
    rw [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target ready.base).mpr ready.baseMeaning
  have pointsComputed := input.spatial_map_complete ready.base ready.order ready.points ready.pointsMeaning
  let evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel :=
    { center := ready.center, base := ready.base, keys,
      tracked := { highestFirst := ready.order, pseudoComparisons := 0 }, points := ready.points }
  have evidenceComputed : input.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?
      target view = some evidence := by
    simp [localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?, centerComputed,
      baseComputed, keysComputed, trackedComputed, pointsComputed, evidence]
  have geometryComputed := (descriptorOfPriorityOrderedPoints?_eq_some_iff ready.points raw).mpr ready.geometry
  simp [localizedOccurrenceShortCircuitRule3Through5Descriptor?, evidenceComputed,
    evidence, geometryComputed]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
