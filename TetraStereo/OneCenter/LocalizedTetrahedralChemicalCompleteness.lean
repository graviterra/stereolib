import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3ChemicalApplicability
import TetraStereo.OneCenter.LocalizedRule3CoupledTopologyApplicability
import TetraStereo.OneCenter.LocalizedScheduledStereochemistryExactOnceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Public tetrahedral completeness from finite chemical classification

The tetrahedral branch uses a common four-ligand descriptor-bearing Rule-3 frame, so its chemical
readiness must additionally state the independent exhaustive coupled-unit uniqueness condition.
This module proves total construction of that frame and then compiles an independently strict
tracked order and exact rational tetrahedral geometry into the canonical scheduler state.
-/

private theorem exists_mapM_compoundRule45_of_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)) = some keys
  | [], _valid => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ :=
        input.exists_mapM_compoundRule45_of_valid target view cursors
          (fun child present => valid child (by simp [present]))
      have keyComputed' :
          input.buildLocalizedRerootCompoundRule45Key? target view
              (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor = some key := by
        simpa only [localizedOccurrenceRerootEvaluationFuel] using keyComputed
      exact ⟨key :: keys, by
        simp [List.mapM_cons, keyComputed', keysComputed]⟩

private theorem length_eq_of_mapM_eq_some
    {Input Output : Type} (f : Input → Option Output) :
    ∀ inputs outputs, (inputs : List Input).mapM f = some outputs →
      outputs.length = inputs.length
  | [], outputs, computed => by
      simp at computed
      subst outputs
      rfl
  | input :: inputs, outputs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none => simp [headComputed] at computed
      | some output =>
          cases tailComputed : inputs.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              simp [length_eq_of_mapM_eq_some f inputs tail tailComputed]

/-- Finite chemical node classification, exact four-ligand topology, and declarative coupled-unit
uniqueness force the actual descriptor-bearing Rules-1a--5 key-frame compiler to succeed. -/
theorem exists_buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame_of_chemical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base)
    (chemical : input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
    (unambiguous : input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      base.cursors) :
    ∃ keys,
      input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
        target view base = some keys := by
  have valid : ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor := by
    intro cursor present
    exact input.localizedRerootChild_valid
      { occurrence := target, previous? := none }
      cursor base.cursors baseMeaning.1 present
  have resolved :=
    LocalizedDescriptorBearingRule3ReachableSupportThrough.resolved input target view
      (chemical.reachableSupport input target view)
  obtain ⟨rule3Frame, rule3Computed⟩ :=
    input.exists_buildLocalizedDescriptorBearingRule3Frame?_at_conservativeFuel_declarative
      target view resolved base.cursors unambiguous valid
  have rule3Length : rule3Frame.keys.length = 4 := by
    rw [input.buildLocalizedDescriptorBearingRule3Frame?_keys_length_eq
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      base.cursors rule3Frame rule3Computed]
    exact base.length_eq
  obtain ⟨rule45Keys, rule45Computed⟩ :=
    input.exists_mapM_compoundRule45_of_valid target view base.cursors valid
  have rule45Length : rule45Keys.length = 4 := by
    rw [length_eq_of_mapM_eq_some
      (input.buildLocalizedRerootCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      base.cursors rule45Keys rule45Computed]
    exact base.length_eq
  let keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel :=
    { rule3Frame, rule3Length, rule45Keys, rule45Length }
  refine ⟨keys, ?_⟩
  simp [buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?,
    rule3Computed, rule3Length, rule45Computed, rule45Length, keys]

/-- The safe tracked-sort evaluator is complete for its independent sort history and all-pairs
strictness relation. -/
theorem safeLocalizedOccurrenceRule3Through5TrackedOrder?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (meaning : input.DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder
      keys tracked) :
    input.safeLocalizedOccurrenceRule3Through5TrackedOrder? keys = some tracked := by
  have sorted : input.localizedOccurrenceRule3Through5TrackedOrder? keys = some tracked :=
    (sortFourLocalizedLigandsTracked_eq_some_iff
      (input.compareLocalizedOccurrenceRule3Through5At? keys) tracked).mpr meaning.1
  have coherent : input.localizedOccurrenceRule3Through5OrderCoherent
      keys tracked.highestFirst = true :=
    (input.localizedOccurrenceRule3Through5OrderCoherent_eq_true_iff
      keys tracked.highestFirst).mpr meaning.2.2
  simp [safeLocalizedOccurrenceRule3Through5TrackedOrder?, sorted, coherent]

private theorem mapM_spatialPoint_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points,
      List.Forall₂
        (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
          (base.cursorAt index) point) order points →
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
        (base.cursorAt index)) = some points
  | [], [], List.Forall₂.nil => rfl
  | index :: order, point :: points, List.Forall₂.cons head tail => by
      rw [List.mapM_cons]
      have headComputed :=
        (input.localizedRerootCursorSpatialPoint?_eq_some_iff
          (base.cursorAt index) point).mpr head
      rw [headComputed, input.mapM_spatialPoint_complete base order points tail]
      rfl

/-- Independent chemical readiness of one final tetrahedral occurrence.  No complete descriptor,
key-frame, tracked-sort, coordinate-map, or scheduler-state success is assumed. -/
def LocalizedTetrahedralChemicalReadiness
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) : Prop :=
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let target := input.localizedFinalOccurrence fuel center
  let view := input.localizedDependencyView state target
  ∃ descriptorCenter base,
    input.RealTetrahedralCenterNode target.1.node descriptorCenter ∧
      input.DeclarativeLocalizedOccurrenceFourLigandFrame target base ∧
      input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough target view
        (localizedDescriptorBearingRule3EvaluationFuel fuel) ∧
      input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
        target view (localizedDescriptorBearingRule3EvaluationFuel fuel) base.cursors ∧
      ∀ keys,
        input.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame
            target view base keys →
        ∃ tracked points raw,
          input.DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder keys tracked ∧
          List.Forall₂
            (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
              (base.cursorAt index) point)
            tracked.highestFirst points ∧
          RationalTetrahedralDescriptor points raw

/-- Independent tetrahedral chemical readiness forces the canonical causal scheduler to assign a
descriptor at the requested center. -/
theorem exists_localizedScheduledTetrahedralSpatialAssignmentAt?_of_chemicalReadiness
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter)
    (ready : input.LocalizedTetrahedralChemicalReadiness fuel center) :
    ∃ assignment,
      input.localizedScheduledTetrahedralSpatialAssignmentAt? fuel center = some assignment ∧
        input.DeclarativeLocalizedScheduledTetrahedralSpatialAssignment fuel assignment := by
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let target := input.localizedFinalOccurrence fuel center
  let view := input.localizedDependencyView state target
  change ∃ descriptorCenter base,
      input.RealTetrahedralCenterNode target.1.node descriptorCenter ∧
      input.DeclarativeLocalizedOccurrenceFourLigandFrame target base ∧
      input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough target view
        (localizedDescriptorBearingRule3EvaluationFuel fuel) ∧
      input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous target view
        (localizedDescriptorBearingRule3EvaluationFuel fuel) base.cursors ∧
      _ at ready
  rcases ready with ⟨descriptorCenter, base, centerMeaning, baseMeaning,
    chemical, unambiguous, spatial⟩
  have centerComputed : input.localizedOccurrenceDescriptorCenter? target =
      some descriptorCenter :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target descriptorCenter).mpr
      centerMeaning
  have baseComputed : input.localizedOccurrenceFourLigandFrame? target = some base :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target base).mpr baseMeaning
  obtain ⟨keys, keysComputed⟩ :=
    input.exists_buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame_of_chemical
      target view base baseMeaning chemical unambiguous
  have keysMeaning :=
    input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?_sound
      target view base keys keysComputed
  obtain ⟨tracked, points, raw, trackedMeaning, pointsMeaning, handedness⟩ :=
    spatial keys keysMeaning
  have trackedComputed :=
    input.safeLocalizedOccurrenceRule3Through5TrackedOrder?_complete
      keys tracked trackedMeaning
  have pointsComputed :=
    input.mapM_spatialPoint_complete base tracked.highestFirst points pointsMeaning
  let evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence fuel :=
    { center := descriptorCenter, base, keys, tracked, points }
  have evidenceComputed :
      input.localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?
        target view = some evidence := by
    simp [localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?,
      centerComputed, baseComputed, keysComputed, trackedComputed, pointsComputed, evidence]
  have rawComputed : descriptorOfPriorityOrderedPoints? points = some raw :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff points raw).mpr handedness
  let descriptor := classifyTetrahedralRSPseudo raw tracked.pseudoComparisons
  have descriptorComputed :
      input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? target view =
        some descriptor := by
    simp [localizedOccurrenceDescriptorBearingRule3Through5Descriptor?, evidenceComputed,
      evidence, rawComputed, descriptor]
  have canonical : input.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
      target view descriptor :=
    (input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_some_iff_canonical
      target view descriptor).mp descriptorComputed
  have stateComputed : state target = some descriptor :=
    (input.localizedOccurrenceDescriptorBearingRule3Through5Model_eq_some_iff_canonical
      state (input.localizedDescriptorBearingRule3Through5SchedulerState_cipModel fuel)
      target descriptor).mpr canonical
  let assignment : input.LocalizedScheduledTetrahedralSpatialAssignment fuel :=
    { center, descriptor }
  have assignmentComputed : input.localizedScheduledTetrahedralSpatialAssignmentAt?
      fuel center = some assignment := by
    simp [localizedScheduledTetrahedralSpatialAssignmentAt?, state, target,
      stateComputed, assignment]
  exact ⟨assignment, assignmentComputed,
    input.localizedScheduledTetrahedralSpatialAssignmentAt?_sound
      fuel center assignment assignmentComputed⟩

/-- A chemically ready tetrahedral center has one independently conforming public assignment and
literal global physical-unit count one. -/
theorem every_chemicallyApplicable_localizedTetrahedral_public_exactly_once
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter)
    (ready : input.LocalizedTetrahedralChemicalReadiness fuel center) :
    ∃ assignment,
      LocalizedScheduledStereochemicalAssignment.tetrahedral assignment ∈
          input.analyzeLocalizedScheduledStereochemistry fuel ∧
        input.DeclarativeLocalizedScheduledTetrahedralSpatialAssignment fuel assignment ∧
        List.count (.tetrahedral center)
          ((input.analyzeLocalizedScheduledStereochemistry fuel).map
            LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 := by
  obtain ⟨assignment, computed, derived⟩ :=
    input.exists_localizedScheduledTetrahedralSpatialAssignmentAt?_of_chemicalReadiness
      fuel center ready
  have retained := input.localizedScheduledTetrahedralSpatialAssignmentAt?_center
    fuel center assignment computed
  have familyPresent : assignment ∈ input.analyzeLocalizedScheduledTetrahedralSpatial fuel :=
    (input.mem_analyzeLocalizedScheduledTetrahedralSpatial_iff fuel assignment).mpr (by
      simpa [retained] using computed)
  refine ⟨assignment,
    (input.tetrahedral_mem_analyzeLocalizedScheduledStereochemistry_iff
      fuel assignment).mpr familyPresent,
    derived, ?_⟩
  simpa [retained] using
    input.tetrahedral_physicalUnit_count_eq_one_of_mem fuel assignment familyPresent

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
