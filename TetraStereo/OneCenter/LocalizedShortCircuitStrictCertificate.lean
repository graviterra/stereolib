import TetraStereo.OneCenter.LocalizedShortCircuitStrictCompleteness
import TetraStereo.OneCenter.LocalizedShortCircuitStrictPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Finite executable evidence for a view-independent strict descriptor. The bounded frame is
an intermediate computation; descriptor success at the production bound is the proved conclusion.
All fields are produced by `localizedStrictRule3DescriptorCertificate?` below. -/
structure LocalizedStrictRule3DescriptorCertificate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (raw : RS) where
  callbackFree : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel
  center : input.TetrahedralCenter
  centerMeaning : input.RealTetrahedralCenterNode target.1.node center
  base : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base
  frame : input.LocalizedRule3CanonicalKeyFrame
  frameComputed : input.buildLocalizedShortCircuitRule3FrameExec? target (fun _ _ => none)
    (2 * (carrierFuel + 1) + 2) base.cursors = some frame
  frameLength : frame.keys.length = 4
  priority : Fin 4 → Nat
  priorityInjective : Function.Injective priority
  ranked : ∀ left right : Fin 4, left ≠ right →
    input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keys.get (Fin.cast frameLength.symm left))
      (frame.keys.get (Fin.cast frameLength.symm right)) = compare (priority left) (priority right)
  order : List (Fin 4)
  permutation : order.Perm (List.finRange 4)
  descending : order.Pairwise (fun left right => priority right < priority left)
  points : List CartesianPoint3
  pointsMeaning : List.Forall₂
    (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
      (base.cursorAt index) point) order points
  geometry : RationalTetrahedralDescriptor points raw

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

/-- A constructed finite certificate guarantees the production descriptor under every view,
including views containing new auxiliary labels. -/
theorem LocalizedStrictRule3DescriptorCertificate.total
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel} {raw : RS}
    (ready : input.LocalizedStrictRule3DescriptorCertificate target raw) :
    ∀ view : input.LocalizedDependencyView target,
      input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view = some (.chiral raw) := by
  let initialView : input.LocalizedDependencyView target := fun _ _ => none
  let frame := ready.frame
  have frameComputed := ready.frameComputed
  have frameLength : frame.keys.length = 4 := ready.frameLength
  have valid : ∀ cursor ∈ ready.base.cursors, input.LocalizedRerootCursorValid cursor := by
    intro cursor present
    exact input.localizedRerootChild_valid { occurrence := target, previous? := none }
      cursor ready.base.cursors ready.baseMeaning.1 present
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
    ready.ranked
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


private theorem spatial_map_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points, (order : List (Fin 4)).mapM
      (fun index => input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) = some points →
      List.Forall₂ (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (base.cursorAt index) point) order points
  | [], points, computed => by simp at computed; subst points; exact .nil
  | index :: order, points, computed => by
      cases head : input.localizedRerootCursorSpatialPoint? (base.cursorAt index) with
      | none => simp [head] at computed
      | some point =>
          cases tail : order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
              (base.cursorAt index)) with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst points
              exact .cons ((input.localizedRerootCursorSpatialPoint?_eq_some_iff
                (base.cursorAt index) point).mp head)
                (input.spatial_map_sound base order rest tail)



def localizedRule3FrameRank
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3CanonicalKeyFrame) (length : frame.keys.length = 4)
    (slot : Fin 4) : Nat :=
  ((List.finRange 4).filter fun other =>
    input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keys.get (Fin.cast length.symm slot))
      (frame.keys.get (Fin.cast length.symm other)) == Ordering.gt).length

/-- Automatically construct sufficient descriptor-completeness evidence from the molecule.
This finite test uses the linear Rule3 frame bound and direct rank/geometry checks. Refusal means
this sufficient class was not certified; it is not a claim of chemical nonexistence. -/
def localizedStrictRule3DescriptorCertificate?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    Option (Sigma fun raw : RS => input.LocalizedStrictRule3DescriptorCertificate target raw) :=
  match input.localizedRule3CallbackFreeCarrierCertificate? carrierFuel with
  | none => none
  | some callbackFree =>
    match centerComputed : input.localizedOccurrenceDescriptorCenter? target with
    | none => none
    | some center =>
      match baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => none
      | some base =>
        match frameComputed : input.buildLocalizedShortCircuitRule3FrameExec? target
            (fun _ _ => none) (2 * (carrierFuel + 1) + 2) base.cursors with
        | none => none
        | some frame =>
          if frameLength : frame.keys.length = 4 then
            let priority := input.localizedRule3FrameRank frame frameLength
            if injective : Function.Injective priority then
              if ranked : ∀ left right : Fin 4, left ≠ right →
                  input.compareLocalizedRerootRecursiveRule3SpatialKeys
                    (frame.keys.get (Fin.cast frameLength.symm left))
                    (frame.keys.get (Fin.cast frameLength.symm right)) =
                      compare (priority left) (priority right) then
                match sorted : sortFourLocalizedLigandsTracked (strictRankComparison priority) with
                | none => none
                | some tracked =>
                  match pointsComputed : tracked.highestFirst.mapM (fun index =>
                      input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) with
                  | none => none
                  | some points =>
                    match geometryComputed : descriptorOfPriorityOrderedPoints? points with
                    | none => none
                    | some raw =>
                      some ⟨raw, {
                        callbackFree, center,
                        centerMeaning := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
                          target center).mp centerComputed
                        base
                        baseMeaning := (input.localizedOccurrenceFourLigandFrame?_eq_some_iff
                          target base).mp (by
                            rwa [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
                              at baseComputed)
                        frame, frameComputed, frameLength, priority, priorityInjective := injective, ranked
                        order := tracked.highestFirst
                        permutation := by
                          obtain ⟨result, computed, perm, _, _⟩ :=
                            sortFourLocalizedLigandsTracked_strictRank_total priority injective
                          have same := Option.some.inj (sorted.symm.trans computed)
                          simpa [same] using perm
                        descending := by
                          obtain ⟨result, computed, _, descending, _⟩ :=
                            sortFourLocalizedLigandsTracked_strictRank_total priority injective
                          have same := Option.some.inj (sorted.symm.trans computed)
                          simpa [same] using descending
                        points
                        pointsMeaning := input.spatial_map_sound base tracked.highestFirst points pointsComputed
                        geometry := (descriptorOfPriorityOrderedPoints?_eq_some_iff points raw).mp geometryComputed
                      }⟩
              else none
            else none
          else none

end CertifiedLocalizedCIPInput
namespace LocalizedShortCircuit
open Certificate.Dependency

/-- The executable constructor's certificate forces the generated global dependency assignment. -/
theorem reference_assigns_strictCertificate
    (input : Input) (target : Occurrence input) (raw : RS)
    (certificate : input.certified.LocalizedStrictRule3DescriptorCertificate target raw) :
    referenceState input target = some (.chiral raw) := by
  rw [← reference_equation input target]
  exact certificate.total _

/-- The same assignment is present in every accepted fast or fallback evaluation. -/
theorem evaluation_assigns_strictCertificate
    (input : Input) (result : Evaluation input) (target : Occurrence input) (raw : RS)
    (certificate : input.certified.LocalizedStrictRule3DescriptorCertificate target raw) :
    lookup result.facts target = some (.chiral raw) := by
  rw [evaluation_eq_reference input result]
  exact reference_assigns_strictCertificate input target raw certificate

end LocalizedShortCircuit
end TetraStereo.OneCenter
