import TetraStereo.OneCenter.AuthoritativeSingleWedgeAuxiliaryIndependence
import TetraStereo.OneCenter.AuthoritativeSingleWedgeExactPriorityDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

open CertifiedLocalizedCIPInput














noncomputable def occurrenceOrdinaryPriorityEvidence? (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option (OrdinaryPriorityEvidence source carrierFuel) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let drawing ← extract? source center.1
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  let slots ← findSlotAlignment? drawing.endpoints (roots.map (cursorAtomID source))
  let keys ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    target view ruleFuel roots
  let tracked ← source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys
  let points ← tracked.highestFirst.mapM (drawingPointForOccurrenceSlot? drawing slots)
  some { drawing, slots, keys, tracked, points }

/-- No successful adapter or sorter equation occurs in this independent sound meaning. -/
def OccurrenceOrdinaryPriorityEvidenceMeaning (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : OrdinaryPriorityEvidence source carrierFuel) : Prop :=
  ∃ center roots,
    source.RealAromaticCanonicalTetrahedralOccurrenceNode target.1.node center ∧
    SourceFrame source center.1.val evidence.drawing ∧
    source.DeclarativeAromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } roots ∧
    ExactSlotAlignment evidence.drawing.endpoints
      (roots.map (cursorAtomID source)) evidence.slots ∧
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyFrame
      target view ruleFuel roots evidence.keys ∧
    source.DeclarativeSafeAromaticCanonicalOccurrenceRule3Through5TrackedOrder
      evidence.keys evidence.tracked ∧
    List.Forall₂ (DrawingPointForOccurrenceSlot evidence.drawing evidence.slots)
      evidence.tracked.highestFirst evidence.points

private theorem occurrenceDrawingPoint_mapM_sound (drawing : Frame) (slots : List Nat) :
    ∀ order points,
      order.mapM (drawingPointForOccurrenceSlot? drawing slots) = some points →
      List.Forall₂ (DrawingPointForOccurrenceSlot drawing slots) order points
  | [], points, computed => by
      simp at computed
      subst points
      exact .nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : drawingPointForOccurrenceSlot? drawing slots index with
      | none => simp [headComputed] at computed
      | some point =>
          cases tailComputed : order.mapM (drawingPointForOccurrenceSlot? drawing slots) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst points
              exact .cons
                ((drawingPointForOccurrenceSlot?_eq_some_iff drawing slots index point).mp
                  headComputed)
                (occurrenceDrawingPoint_mapM_sound drawing slots order tail tailComputed)

theorem occurrenceOrdinaryPriorityEvidence?_sound (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : OrdinaryPriorityEvidence source carrierFuel)
    (computed : occurrenceOrdinaryPriorityEvidence? source target view ruleFuel = some evidence) :
    OccurrenceOrdinaryPriorityEvidenceMeaning source target view ruleFuel evidence := by
  unfold occurrenceOrdinaryPriorityEvidence? at computed
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases drawingComputed : extract? source center.1 with
      | none => simp [centerComputed, drawingComputed] at computed
      | some drawing =>
          cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
          | none => simp [centerComputed, rootsComputed] at computed
          | some roots =>
              cases slotsComputed : findSlotAlignment? drawing.endpoints
                  (roots.map (cursorAtomID source)) with
              | none => simp [centerComputed, drawingComputed, rootsComputed, slotsComputed]
                  at computed
              | some slots =>
                  cases keysComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
                      target view ruleFuel roots with
                  | none => simp [centerComputed, rootsComputed, keysComputed] at computed
                  | some keys =>
                      cases trackedComputed :
                          source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys with
                      | none => simp [centerComputed, rootsComputed, keysComputed, trackedComputed] at computed
                      | some tracked =>
                          cases pointsComputed : tracked.highestFirst.mapM
                              (drawingPointForOccurrenceSlot? drawing slots) with
                          | none => simp [centerComputed, drawingComputed, rootsComputed,
                              slotsComputed, keysComputed, trackedComputed, pointsComputed] at computed
                          | some points =>
                              simp [centerComputed, drawingComputed, rootsComputed, slotsComputed,
                                keysComputed, trackedComputed, pointsComputed] at computed
                              subst evidence
                              exact ⟨center, roots,
                                source.aromaticCanonicalOccurrenceTetrahedralCenter?_sound
                                  target center centerComputed,
                                (extract?_eq_some_iff source center.1 drawing).mp drawingComputed,
                                source.aromaticCanonicalOccurrenceLigandFrame?_sound
                                  target roots rootsComputed,
                                findSlotAlignment?_sound _ _ slots slotsComputed,
                                source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
                                  target view ruleFuel roots keys keysComputed,
                                source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
                                  keys tracked trackedComputed,
                                occurrenceDrawingPoint_mapM_sound _ _ _ _ pointsComputed⟩

noncomputable def occurrenceOrdinaryDescriptor? (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option AromaticCanonicalAuxiliaryLabel := do
  let evidence ← occurrenceOrdinaryPriorityEvidence? source target view ruleFuel
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

def OccurrenceOrdinaryDescriptorMeaning (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    OccurrenceOrdinaryPriorityEvidenceMeaning source target view ruleFuel evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

/-- Exact compiled evidence and independent geometry, distinct from the weaker sound meaning. -/
def CanonicalOccurrenceOrdinaryDescriptor (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    occurrenceOrdinaryPriorityEvidence? source target view ruleFuel = some evidence ∧
    OccurrenceOrdinaryPriorityEvidenceMeaning source target view ruleFuel evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

theorem occurrenceOrdinaryDescriptor?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    occurrenceOrdinaryDescriptor? source target view ruleFuel = some descriptor ↔
      CanonicalOccurrenceOrdinaryDescriptor source target view ruleFuel descriptor := by
  constructor
  · intro computed
    unfold occurrenceOrdinaryDescriptor? at computed
    cases evidenceComputed : occurrenceOrdinaryPriorityEvidence? source target view ruleFuel with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
        | none => simp [evidenceComputed, rawComputed] at computed
        | some raw =>
            simp [evidenceComputed, rawComputed] at computed
            subst descriptor
            exact ⟨evidence, raw, evidenceComputed,
              occurrenceOrdinaryPriorityEvidence?_sound source target view ruleFuel
                evidence evidenceComputed,
              (descriptorOfPriorityOrderedPoints?_eq_some_iff evidence.points raw).mp rawComputed,
              rfl⟩
  · rintro ⟨evidence, raw, evidenceComputed, _meaning, geometry, rfl⟩
    simp [occurrenceOrdinaryDescriptor?, evidenceComputed,
      (descriptorOfPriorityOrderedPoints?_eq_some_iff evidence.points raw).mpr geometry]

theorem occurrenceOrdinaryDescriptor?_sound (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (computed : occurrenceOrdinaryDescriptor? source target view ruleFuel = some descriptor) :
    OccurrenceOrdinaryDescriptorMeaning source target view ruleFuel descriptor := by
  obtain ⟨evidence, raw, _, meaning, geometry, classified⟩ :=
    (occurrenceOrdinaryDescriptor?_eq_some_iff_canonical source target view ruleFuel descriptor).mp
      computed
  exact ⟨evidence, raw, meaning, geometry, classified⟩

theorem occurrenceOrdinaryDescriptor?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    occurrenceOrdinaryDescriptor? source target view ruleFuel = none ↔
      ¬∃ descriptor, CanonicalOccurrenceOrdinaryDescriptor source target view ruleFuel descriptor := by
  constructor
  · intro refused ⟨descriptor, canonical⟩
    have success := (occurrenceOrdinaryDescriptor?_eq_some_iff_canonical
      source target view ruleFuel descriptor).mpr canonical
    rw [refused] at success
    cases success
  · intro absent
    cases computed : occurrenceOrdinaryDescriptor? source target view ruleFuel with
    | none => rfl
    | some descriptor =>
        exact False.elim (absent ⟨descriptor,
          (occurrenceOrdinaryDescriptor?_eq_some_iff_canonical
            source target view ruleFuel descriptor).mp computed⟩)

def OccurrenceOrdinaryOutcome (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  match outcome with
  | none => ¬∃ descriptor, CanonicalOccurrenceOrdinaryDescriptor source target
      (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor
  | some descriptor => CanonicalOccurrenceOrdinaryDescriptor source target
      (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor

theorem occurrenceOrdinaryOutcome_iff (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) :
    OccurrenceOrdinaryOutcome source ruleFuel state target outcome ↔
      occurrenceOrdinaryDescriptor? source target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = outcome := by
  cases outcome with
  | none => exact (occurrenceOrdinaryDescriptor?_eq_none_iff_no_canonical source target _ ruleFuel).symm
  | some descriptor => exact (occurrenceOrdinaryDescriptor?_eq_some_iff_canonical
      source target _ ruleFuel descriptor).symm

noncomputable def occurrenceOrdinaryAuxiliarySemantics (source : AuthoritativeChemicalInput)
    (carrierFuel ruleFuel : Nat) : source.AromaticCanonicalRuleSemantics carrierFuel where
  DeclarativeDerivation := OccurrenceOrdinaryOutcome source ruleFuel
  executableRule := fun target view => occurrenceOrdinaryDescriptor? source target view ruleFuel
  derivation_executable_iff := occurrenceOrdinaryOutcome_iff source ruleFuel

theorem existsUnique_occurrenceOrdinaryCIPModel (source : AuthoritativeChemicalInput)
    (carrierFuel ruleFuel : Nat) :
    ∃! state, (source.aromaticCanonicalOccurrenceSystem
      (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel)).CIPModel state :=
  source.existsUnique_aromaticCanonicalCIPModel
    (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel)

noncomputable def occurrenceOrdinaryScheduledState (source : AuthoritativeChemicalInput)
    (carrierFuel ruleFuel : Nat) : source.AromaticCanonicalAuxiliaryState carrierFuel :=
  DeclarativeCIP.OccurrenceScheduler.decode
    (source.aromaticCanonicalOccurrenceSystem
      (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel))
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (DeclarativeCIP.OccurrenceScheduler.closure
      (source.aromaticCanonicalOccurrenceSystem
        (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel))
      (@source.AromaticCanonicalDepthDependency carrierFuel))

theorem occurrenceOrdinaryScheduledState_cipModel (source : AuthoritativeChemicalInput)
    (carrierFuel ruleFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel)).CIPModel
        (occurrenceOrdinaryScheduledState source carrierFuel ruleFuel) :=
  source.aromaticCanonicalSchedulerClosure_cipModel
    (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel)

theorem occurrenceOrdinaryModel_evaluates (source : AuthoritativeChemicalInput)
    {carrierFuel ruleFuel : Nat} (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    occurrenceOrdinaryDescriptor? source target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = state target := by
  have fixed := (source.aromaticCanonicalOccurrenceSystem
    (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel)).cipModel_iff_executableStateStep_fixed
      (source.aromaticCanonicalDerivationStepCorrespondence
        (occurrenceOrdinaryAuxiliarySemantics source carrierFuel ruleFuel)) state |>.mp model
  exact congrFun fixed target

theorem occurrenceTetrahedralCenter?_final (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalOccurrenceTetrahedralCenter?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some center := by
  classical
  simp [aromaticCanonicalOccurrenceTetrahedralCenter?, aromaticCanonicalFinalOccurrence,
    OfficialCIPNode.root, center.2]

theorem occurrenceOrdinaryDescriptor?_final_eq (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) (ruleFuel : Nat) :
    occurrenceOrdinaryDescriptor? source
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view ruleFuel =
      ordinaryDescriptor? source carrierFuel center view ruleFuel := by
  cases drawingComputed : extract? source center.1 with
  | none =>
      simp [occurrenceOrdinaryDescriptor?, occurrenceOrdinaryPriorityEvidence?,
        occurrenceTetrahedralCenter?_final, ordinaryDescriptor?, ordinaryPriorityEvidence?,
        occurrenceAlignment?, drawingComputed]
  | some drawing =>
      cases slotsComputed : findSlotAlignment? drawing.endpoints
          ((finalOccurrenceRoots source carrierFuel center).map (cursorAtomID source)) with
      | none =>
          simp [occurrenceOrdinaryDescriptor?, occurrenceOrdinaryPriorityEvidence?,
            occurrenceTetrahedralCenter?_final, finalOccurrenceRoots_are_returned,
            ordinaryDescriptor?, ordinaryPriorityEvidence?, occurrenceAlignment?,
            drawingComputed, finalOccurrenceRootIDs, slotsComputed]
      | some slots =>
          simp [occurrenceOrdinaryDescriptor?, occurrenceOrdinaryPriorityEvidence?,
            occurrenceTetrahedralCenter?_final, finalOccurrenceRoots_are_returned,
            ordinaryDescriptor?, ordinaryPriorityEvidence?, occurrenceAlignment?,
            drawingComputed, finalOccurrenceRootIDs, slotsComputed]

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeOccurrenceDescriptorRegression

open AuthoritativeChemicalInput AuthoritativeChemicalInput.SingleWedgeSource
open SingleWedgeOccurrenceAlignmentRegression

/-! ### Historical-key policy

The declarations `cfclbri_occurrence_descriptor_S` and
`cfclbri_occurrence_scheduled_state_S` are historical API keys pinned by
`AuthoritativeSingleWedgeOccurrenceDescriptorKernelCertificate`. Their suffixes predate the
corrected negative-`R`/positive-`S` calibration; the solid-wedge CFClBrI production descriptor is
`R`. The historical names are retained with corrected statements, and accurately named `_R`
siblings state the same results for new code. -/

/-- A closed source-native nonvacuity check through the new original-occurrence adapter.
Historical API key: the suffix `_S` predates the sign correction; the proved descriptor is `R`. -/
theorem cfclbri_occurrence_descriptor_S
    (view : SingleWedgeSourceRegression.source.AromaticCanonicalDependencyView
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter)) :
    occurrenceOrdinaryDescriptor? SingleWedgeSourceRegression.source
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter)
      view 2 = some (.chiral RS.R) := by
  rw [occurrenceOrdinaryDescriptor?_final_eq,
    SingleWedgeAuxiliaryIndependenceRegression.cfclbri_any_auxiliary_view_agrees_empty]
  exact SingleWedgeExactPriorityDescriptorRegression.cfclbri_full_production_solid_descriptor

/-- Accurate-name sibling of `cfclbri_occurrence_descriptor_S`. -/
theorem cfclbri_occurrence_descriptor_R
    (view : SingleWedgeSourceRegression.source.AromaticCanonicalDependencyView
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter)) :
    occurrenceOrdinaryDescriptor? SingleWedgeSourceRegression.source
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter)
      view 2 = some (.chiral RS.R) :=
  cfclbri_occurrence_descriptor_S view

/-- The internally scheduled drawing-only model assigns this actual final occurrence `R`.
Historical API key: the suffix `_S` predates the sign correction. This is not coverage of
interior tied-priority units or mixed evidence conflicts. -/
theorem cfclbri_occurrence_scheduled_state_S :
    occurrenceOrdinaryScheduledState SingleWedgeSourceRegression.source 0 2
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter) =
        some (.chiral RS.R) := by
  have fixed := occurrenceOrdinaryModel_evaluates SingleWedgeSourceRegression.source
    (occurrenceOrdinaryScheduledState SingleWedgeSourceRegression.source 0 2)
    (occurrenceOrdinaryScheduledState_cipModel SingleWedgeSourceRegression.source 0 2)
    (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter)
  rw [← fixed]
  exact cfclbri_occurrence_descriptor_S _

/-- Accurate-name sibling of `cfclbri_occurrence_scheduled_state_S`. -/
theorem cfclbri_occurrence_scheduled_state_R :
    occurrenceOrdinaryScheduledState SingleWedgeSourceRegression.source 0 2
      (SingleWedgeSourceRegression.source.aromaticCanonicalFinalOccurrence 0 cfclbriProductionCenter) =
        some (.chiral RS.R) :=
  cfclbri_occurrence_scheduled_state_S

end SingleWedgeOccurrenceDescriptorRegression
end TetraStereo.OneCenter
