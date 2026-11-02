import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance
import TetraStereo.OneCenter.CIPAuthoritativeStereoAssignmentConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Complete observed-geometry assignment conformance

The graph-only authority theorem cannot establish handedness that exists only in coordinates or a
configuration drawing.  This file gives the raw geometry ingress its own independent judgments and
then joins those judgments to the certified graph analyzer.  Geometry records are observations,
not priority assertions: atom incidence and strict axial endpoint priorities are checked against
the molecule, while polyhedral priorities are derived and certified by the IR-9 layer.
-/

namespace BlueBookP93.GeometryIngress

/-- A successful endpoint comparison must be strict; a tie or unavailable comparison cannot
license an axial descriptor. -/
def StrictPriorityDecision : Option Ordering → Prop
  | some .gt | some .lt => True
  | _ => False

/-- Independent P-92 `Rₐ/Sₐ` interpretation of the two-valued orientation observation. -/
def AxialSenseOutcomeJudgment : StereoSense → StereoOutcome → Prop
  | .positive, .axial .Ra
  | .negative, .axial .Sa => True
  | _, _ => False

/-- Independent P-92 `Rₚ/Sₚ` interpretation of the planar orientation observation. -/
def PlanarSenseOutcomeJudgment : StereoSense → StereoOutcome → Prop
  | .positive, .planar .Rp
  | .negative, .planar .Sp => True
  | _, _ => False

/-- Independent helicity interpretation: positive/right-handed is `P`, negative/left-handed is
`M`. -/
def HelicalSenseOutcomeJudgment : StereoSense → StereoOutcome → Prop
  | .positive, .helical .P
  | .negative, .helical .M => True
  | _, _ => False

/-- Complete molecule-checked meaning of one raw axial orientation record. -/
structure AxialObservationAssignmentJudgment
    (result : ChemistryNormalizationResult) (record : IndexedAxialGeometryObservation)
    (assignment : StereoAssignment) : Prop where
  axisStartInRange : record.axisStart < result.parsed.atomCount
  axisEndInRange : record.axisEnd < result.parsed.atomCount
  startFirstInRange : record.startFirst < result.parsed.atomCount
  startSecondInRange : record.startSecond < result.parsed.atomCount
  endFirstInRange : record.endFirst < result.parsed.atomCount
  endSecondInRange : record.endSecond < result.parsed.atomCount
  axisDistinct : record.axisStart ≠ record.axisEnd
  startPairDistinct : record.startFirst ≠ record.startSecond
  endPairDistinct : record.endFirst ≠ record.endSecond
  startFirstIncident :
    record.startFirst ∈ result.geometryPriorityState.1.writtenNeighbors record.axisStart
  startSecondIncident :
    record.startSecond ∈ result.geometryPriorityState.1.writtenNeighbors record.axisStart
  endFirstIncident :
    record.endFirst ∈ result.geometryPriorityState.1.writtenNeighbors record.axisEnd
  endSecondIncident :
    record.endSecond ∈ result.geometryPriorityState.1.writtenNeighbors record.axisEnd
  startPriorityStrict : StrictPriorityDecision
    (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
      result.geometryPriorityState.2.2 result.geometryPriorityState.2.1 record.axisStart
      record.startFirst record.startSecond)
  endPriorityStrict : StrictPriorityDecision
    (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
      result.geometryPriorityState.2.2 result.geometryPriorityState.2.1 record.axisEnd
      record.endFirst record.endSecond)
  unit : assignment.unit = StereoUnit.axis record.axisStart record.axisEnd
  outcome : AxialSenseOutcomeJudgment record.sense assignment.outcome

/-- Complete well-formed-record meaning of one planar orientation observation.  The orientation
itself is external geometry evidence; all represented atom references are checked here. -/
structure PlanarObservationAssignmentJudgment
    (result : ChemistryNormalizationResult) (record : IndexedPlanarGeometryObservation)
    (assignment : StereoAssignment) : Prop where
  planeAtomsInRange : ∀ atom ∈ record.planeAtoms, atom < result.parsed.atomCount
  pilotInRange : record.pilotAtom < result.parsed.atomCount
  firstReferenceInRange : record.firstReference < result.parsed.atomCount
  secondReferenceInRange : record.secondReference < result.parsed.atomCount
  planeHasAtLeastThreeAtoms : 3 ≤ record.planeAtoms.length
  planeAtomsNoDuplicates : record.planeAtoms.eraseDups.length = record.planeAtoms.length
  referencesDistinct : record.firstReference ≠ record.secondReference
  unit : assignment.unit = StereoUnit.plane record.planeAtoms
  outcome : PlanarSenseOutcomeJudgment record.sense assignment.outcome

/-- Complete well-formed-record meaning of one helical orientation observation. -/
structure HelicalObservationAssignmentJudgment
    (result : ChemistryNormalizationResult) (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop where
  pathAtomsInRange : ∀ atom ∈ record.helixPath, atom < result.parsed.atomCount
  frontReferenceInRange : record.frontReference < result.parsed.atomCount
  backReferenceInRange : record.backReference < result.parsed.atomCount
  pathHasAtLeastThreeAtoms : 3 ≤ record.helixPath.length
  pathNoDuplicates : record.helixPath.eraseDups.length = record.helixPath.length
  referencesDistinct : record.frontReference ≠ record.backReference
  unit : assignment.unit = StereoUnit.helix record.helixPath
  outcome : HelicalSenseOutcomeJudgment record.sense assignment.outcome

/-- The already independent, proof-relevant IR-9 certificate exposed by every successful
polyhedral observation assignment. -/
def PolyhedralObservationAssignmentJudgment
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  ∃ priorities memberships independentRotation? rotation? positions index absolute,
    record.geometryRecognitionOK? = true ∧
    RedBookIR9.GeometryRecognized record.recognition
      (BlueBookP93.geometryOfProduction record.geometry) ∧
    result.observedPolyhedralPriorityNumbers? record.center record.geometry
        record.ligands record.priming = some priorities ∧
    ValidatedMolecularPrimingFrame result result.geometryPriorityState.1
      result.geometryPriorityState.2.2 record.center record.ligands record.priming
      memberships ∧
    (∃ compareAt baseNumbers primeCounts,
      result.polyhedralPriorityComparisonFrame? record.center record.geometry record.ligands =
          some compareAt ∧
      deriveDensePolyhedralBasePriorityNumbers? record.ligands.length compareAt =
          some baseNumbers ∧
      RedBookIR9.FinitePriorityNumbering record.ligands.length compareAt baseNumbers ∧
      canonicalPolyhedralPrimeCounts? record.ligands.length memberships = some primeCounts ∧
      RedBookIR9.FinitePrimingAssignment record.ligands.length
        (effectivePolyhedralPrimingMemberships record.ligands.length memberships) primeCounts ∧
      baseNumbers.zipWithM (fun number primes =>
        some { number := number, primes := primes }) primeCounts = some priorities) ∧
    RedBookIR9.ConfigurationPositionsRecognized record.configurationPositions
      (BlueBookP93.geometryOfProduction record.geometry) positions ∧
    RedBookIR9.AbsoluteOrientationRecognized record.absoluteOrientation
      (BlueBookP93.geometryOfProduction record.geometry) independentRotation? ∧
    rotation? = independentRotation?.map PolyhedralRotationSense.ofIndependent ∧
    (independentRotation?.isSome &&
      priorities.eraseDups.length != priorities.length) = false ∧
    polyhedralConfigurationIndex? record.geometry priorities positions = some index ∧
    polyhedralAbsoluteConfiguration? record.geometry rotation? = some absolute ∧
    assignment =
      { unit := StereoUnit.polyhedron record.center
        outcome := StereoOutcome.polyhedral
          { geometry := record.geometry, configurationIndex := index,
            absolute? := absolute } }

end BlueBookP93.GeometryIngress

/-! ## Explicit planar observation boundary

The current planar record intentionally contains an external orientation sense.  The following
theorems make the resulting information boundary formal: changing only that bit never changes
whether the router accepts the frame, yet the two accepted results are distinct.  Therefore no
coordinate-free theorem about this API can select `Rₚ` rather than `Sₚ`; a source-faithful
`a,b,y,z` derived-tetrahedron premise must be added upstream.
-/

def IndexedPlanarGeometryObservation.withSense
    (record : IndexedPlanarGeometryObservation) (sense : StereoSense) :
    IndexedPlanarGeometryObservation :=
  { record with sense := sense }

def IndexedPlanarGeometryObservation.assignmentOfSense
    (record : IndexedPlanarGeometryObservation) (sense : StereoSense) : StereoAssignment :=
  { unit := StereoUnit.plane record.planeAtoms
    outcome := StereoOutcome.planar (PlanarDescriptor.ofSense sense) }

theorem IndexedPlanarGeometryObservation.assignmentOfSense_positive_ne_negative
    (record : IndexedPlanarGeometryObservation) :
    record.assignmentOfSense .positive ≠ record.assignmentOfSense .negative := by
  simp [IndexedPlanarGeometryObservation.assignmentOfSense,
    PlanarDescriptor.ofSense]

/-- Acceptance of a planar frame contains no information about which raw sense was supplied. -/
theorem ChemistryNormalizationResult.planarGeometryObservationAssignment?_withSense_isSome
    (result : ChemistryNormalizationResult) (record : IndexedPlanarGeometryObservation)
    (first second : StereoSense) :
    (result.planarGeometryObservationAssignment? (record.withSense first)).isSome =
      (result.planarGeometryObservationAssignment? (record.withSense second)).isSome := by
  unfold ChemistryNormalizationResult.planarGeometryObservationAssignment?
  simp only [IndexedPlanarGeometryObservation.withSense]
  cases result.atomFinList? record.planeAtoms <;> simp
  cases result.atomFin? record.pilotAtom <;> simp
  cases result.atomFin? record.firstReference <;> simp
  cases result.atomFin? record.secondReference <;> simp
  split <;> simp

/-- Whenever one raw sense is accepted, changing only that external bit accepts the opposite,
distinct descriptor as well.  This is a proved insufficiency of the old record, not a chemical
claim that both configurations describe the same coordinate set. -/
theorem ChemistryNormalizationResult.planarGeometryObservationAssignment?_opposite_raw_senses
    (result : ChemistryNormalizationResult) (record : IndexedPlanarGeometryObservation) :
    result.planarGeometryObservationAssignment? (record.withSense .positive) =
        some (record.assignmentOfSense .positive) ↔
      result.planarGeometryObservationAssignment? (record.withSense .negative) =
        some (record.assignmentOfSense .negative) := by
  unfold ChemistryNormalizationResult.planarGeometryObservationAssignment?
  simp only [IndexedPlanarGeometryObservation.withSense,
    IndexedPlanarGeometryObservation.assignmentOfSense]
  cases result.atomFinList? record.planeAtoms <;> simp
  cases result.atomFin? record.pilotAtom <;> simp
  cases result.atomFin? record.firstReference <;> simp
  cases result.atomFin? record.secondReference <;> simp

/-! ## Structural index reflection -/

@[simp] theorem ChemistryNormalizationResult.atomFin?_isSome_iff
    (result : ChemistryNormalizationResult) (atom : Nat) :
    (result.atomFin? atom).isSome = true ↔ atom < result.parsed.atomCount := by
  simp [ChemistryNormalizationResult.atomFin?]

theorem ChemistryNormalizationResult.atomFin?_eq_some_bound
    (result : ChemistryNormalizationResult) (atom : Nat)
    (bounded : Fin result.parsed.atomCount)
    (conversion : result.atomFin? atom = some bounded) :
    atom < result.parsed.atomCount := by
  by_cases inRange : atom < result.parsed.atomCount
  · exact inRange
  · simp [ChemistryNormalizationResult.atomFin?, inRange] at conversion

theorem ChemistryNormalizationResult.atomFinList?_eq_some_all_in_range
    (result : ChemistryNormalizationResult) (atoms : List Nat)
    (converted : List (Fin result.parsed.atomCount))
    (conversion : result.atomFinList? atoms = some converted) :
    ∀ atom ∈ atoms, atom < result.parsed.atomCount := by
  induction atoms generalizing converted with
  | nil => simp
  | cons atom atoms inductionHypothesis =>
      unfold ChemistryNormalizationResult.atomFinList? at conversion
      cases atomEq : result.atomFin? atom with
      | none => simp [atomEq] at conversion
      | some bounded =>
          cases restEq : result.atomFinList? atoms with
          | none => simp [atomEq, restEq] at conversion
          | some boundedAtoms =>
              have atomBound : atom < result.parsed.atomCount := by
                exact result.atomFin?_eq_some_bound atom bounded atomEq
              have restBound := inductionHypothesis boundedAtoms restEq
              intro candidate present
              simp only [List.mem_cons] at present
              rcases present with rfl | inRest
              · exact atomBound
              · exact restBound candidate inRest

/-! ## Per-record soundness -/

theorem ChemistryNormalizationResult.axialGeometryObservationAssignment?_sound_P92
    (result : ChemistryNormalizationResult) (record : IndexedAxialGeometryObservation)
    (assignment : StereoAssignment)
    (produced : result.axialGeometryObservationAssignment? record = some assignment) :
    BlueBookP93.GeometryIngress.AxialObservationAssignmentJudgment
      result record assignment := by
  unfold ChemistryNormalizationResult.axialGeometryObservationAssignment? at produced
  simp only [ChemistryNormalizationResult.atomFin?] at produced
  split at produced <;> rename_i axisStartBound
  · split at produced <;> rename_i axisEndBound
    · split at produced <;> rename_i startFirstBound
      · split at produced <;> rename_i startSecondBound
        · split at produced <;> rename_i endFirstBound
          · split at produced <;> rename_i endSecondBound
            · split at produced <;> rename_i distinct
              · contradiction
              · simp only [Bool.or_eq_true, beq_iff_eq] at distinct
                split at produced <;> rename_i incident
                · contradiction
                · simp only [Bool.or_eq_true] at incident
                  generalize startDecisionEq :
                    compareBranchesThroughOfficialContext? result
                      result.geometryPriorityState.1 result.geometryPriorityState.2.2
                      result.geometryPriorityState.2.1 record.axisStart record.startFirst
                      record.startSecond = startDecision at produced
                  generalize endDecisionEq :
                    compareBranchesThroughOfficialContext? result
                      result.geometryPriorityState.1 result.geometryPriorityState.2.2
                      result.geometryPriorityState.2.1 record.axisEnd record.endFirst
                      record.endSecond = endDecision at produced
                  cases startDecision with
                  | none => simp at produced
                  | some startOrder =>
                      cases endDecision with
                      | none => simp at produced
                      | some endOrder =>
                          have startStrict :
                              BlueBookP93.GeometryIngress.StrictPriorityDecision
                                (some startOrder) := by
                            cases startOrder <;>
                              simp_all [BlueBookP93.GeometryIngress.StrictPriorityDecision]
                          have endStrict :
                              BlueBookP93.GeometryIngress.StrictPriorityDecision
                                (some endOrder) := by
                            cases endOrder <;>
                              simp_all [BlueBookP93.GeometryIngress.StrictPriorityDecision]
                          have axisDistinct : record.axisStart ≠ record.axisEnd := fun equal =>
                            distinct (.inl (.inl equal))
                          have startPairDistinct :
                              record.startFirst ≠ record.startSecond := fun equal =>
                            distinct (.inl (.inr equal))
                          have endPairDistinct :
                              record.endFirst ≠ record.endSecond := fun equal =>
                            distinct (.inr equal)
                          have startFirstIncident :
                              record.startFirst ∈
                                result.geometryPriorityState.1.writtenNeighbors
                                  record.axisStart := by
                            by_contra absent
                            apply incident
                            exact .inl (.inl (.inl (by simpa using absent)))
                          have startSecondIncident :
                              record.startSecond ∈
                                result.geometryPriorityState.1.writtenNeighbors
                                  record.axisStart := by
                            by_contra absent
                            apply incident
                            exact .inl (.inl (.inr (by simpa using absent)))
                          have endFirstIncident :
                              record.endFirst ∈
                                result.geometryPriorityState.1.writtenNeighbors
                                  record.axisEnd := by
                            by_contra absent
                            apply incident
                            exact .inl (.inr (by simpa using absent))
                          have endSecondIncident :
                              record.endSecond ∈
                                result.geometryPriorityState.1.writtenNeighbors
                                  record.axisEnd := by
                            by_contra absent
                            apply incident
                            exact .inr (by simpa using absent)
                          simp at produced
                          have assignmentEq : assignment =
                              { unit := StereoUnit.axis record.axisStart record.axisEnd,
                                outcome := StereoOutcome.axial
                                  (AxialDescriptor.ofSense record.sense) } :=
                            produced.2.symm
                          subst assignment
                          refine {
                            axisStartInRange := axisStartBound
                            axisEndInRange := axisEndBound
                            startFirstInRange := startFirstBound
                            startSecondInRange := startSecondBound
                            endFirstInRange := endFirstBound
                            endSecondInRange := endSecondBound
                            axisDistinct := axisDistinct
                            startPairDistinct := startPairDistinct
                            endPairDistinct := endPairDistinct
                            startFirstIncident := startFirstIncident
                            startSecondIncident := startSecondIncident
                            endFirstIncident := endFirstIncident
                            endSecondIncident := endSecondIncident
                            startPriorityStrict := ?_
                            endPriorityStrict := ?_
                            unit := rfl
                            outcome := ?_ }
                          · rw [startDecisionEq]
                            exact startStrict
                          · rw [endDecisionEq]
                            exact endStrict
                          · cases record.sense <;>
                              trivial
            · simp at produced
          · simp at produced
        · simp at produced
      · simp at produced
    · simp at produced
  · simp at produced

theorem ChemistryNormalizationResult.planarGeometryObservationAssignment?_sound_P92
    (result : ChemistryNormalizationResult) (record : IndexedPlanarGeometryObservation)
    (assignment : StereoAssignment)
    (produced : result.planarGeometryObservationAssignment? record = some assignment) :
    BlueBookP93.GeometryIngress.PlanarObservationAssignmentJudgment
      result record assignment := by
  unfold ChemistryNormalizationResult.planarGeometryObservationAssignment? at produced
  cases planeEq : result.atomFinList? record.planeAtoms with
  | none => simp [planeEq] at produced
  | some planeAtoms =>
      cases pilotEq : result.atomFin? record.pilotAtom with
      | none => simp [planeEq, pilotEq] at produced
      | some pilot =>
          cases firstEq : result.atomFin? record.firstReference with
          | none => simp [planeEq, pilotEq, firstEq] at produced
          | some first =>
              cases secondEq : result.atomFin? record.secondReference with
              | none => simp [planeEq, pilotEq, firstEq, secondEq] at produced
              | some second =>
                  simp only [planeEq, pilotEq, firstEq, secondEq] at produced
                  split at produced <;> rename_i accepted
                  · simp at produced
                  · have planeBounds := result.atomFinList?_eq_some_all_in_range
                        record.planeAtoms planeAtoms planeEq
                    have pilotBound : record.pilotAtom < result.parsed.atomCount := by
                      exact result.atomFin?_eq_some_bound record.pilotAtom pilot pilotEq
                    have firstBound : record.firstReference < result.parsed.atomCount := by
                      exact result.atomFin?_eq_some_bound record.firstReference first firstEq
                    have secondBound : record.secondReference < result.parsed.atomCount := by
                      exact result.atomFin?_eq_some_bound record.secondReference second secondEq
                    have shortFalse : decide (record.planeAtoms.length < 3) = false := by
                      apply Bool.eq_false_of_not_eq_true
                      intro shortTrue
                      apply accepted
                      simp [shortTrue]
                    have duplicatesFalse :
                        (record.planeAtoms.eraseDups.length !=
                          record.planeAtoms.length) = false := by
                      apply Bool.eq_false_of_not_eq_true
                      intro duplicatesTrue
                      apply accepted
                      simp [duplicatesTrue]
                    have referencesFalse :
                        (record.firstReference == record.secondReference) = false := by
                      apply Bool.eq_false_of_not_eq_true
                      intro referencesTrue
                      apply accepted
                      simp [referencesTrue]
                    have lengthAtLeast : 3 ≤ record.planeAtoms.length := by
                      have notShort : ¬ record.planeAtoms.length < 3 := by
                        simpa using shortFalse
                      omega
                    have noDuplicates :
                        record.planeAtoms.eraseDups.length = record.planeAtoms.length := by
                      simpa using duplicatesFalse
                    have referencesDistinct :
                        record.firstReference ≠ record.secondReference := by
                      simpa using referencesFalse
                    have assignmentEq : assignment =
                        { unit := StereoUnit.plane record.planeAtoms,
                          outcome := StereoOutcome.planar
                            (PlanarDescriptor.ofSense record.sense) } := by
                      simpa using produced.symm
                    subst assignment
                    refine {
                      planeAtomsInRange := planeBounds
                      pilotInRange := pilotBound
                      firstReferenceInRange := firstBound
                      secondReferenceInRange := secondBound
                      planeHasAtLeastThreeAtoms := lengthAtLeast
                      planeAtomsNoDuplicates := noDuplicates
                      referencesDistinct := referencesDistinct
                      unit := rfl
                      outcome := ?_ }
                    cases record.sense <;>
                      trivial

theorem ChemistryNormalizationResult.helicalGeometryObservationAssignment?_sound_P92
    (result : ChemistryNormalizationResult) (record : IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment)
    (produced : result.helicalGeometryObservationAssignment? record = some assignment) :
    BlueBookP93.GeometryIngress.HelicalObservationAssignmentJudgment
      result record assignment := by
  unfold ChemistryNormalizationResult.helicalGeometryObservationAssignment? at produced
  cases pathEq : result.atomFinList? record.helixPath with
  | none => simp [pathEq] at produced
  | some path =>
      cases frontEq : result.atomFin? record.frontReference with
      | none => simp [pathEq, frontEq] at produced
      | some front =>
          cases backEq : result.atomFin? record.backReference with
          | none => simp [pathEq, frontEq, backEq] at produced
          | some back =>
              simp only [pathEq, frontEq, backEq] at produced
              split at produced <;> rename_i accepted
              · simp at produced
              · have pathBounds := result.atomFinList?_eq_some_all_in_range
                    record.helixPath path pathEq
                have frontBound : record.frontReference < result.parsed.atomCount := by
                  exact result.atomFin?_eq_some_bound record.frontReference front frontEq
                have backBound : record.backReference < result.parsed.atomCount := by
                  exact result.atomFin?_eq_some_bound record.backReference back backEq
                have shortFalse : decide (record.helixPath.length < 3) = false := by
                  apply Bool.eq_false_of_not_eq_true
                  intro shortTrue
                  apply accepted
                  simp [shortTrue]
                have duplicatesFalse :
                    (record.helixPath.eraseDups.length != record.helixPath.length) = false := by
                  apply Bool.eq_false_of_not_eq_true
                  intro duplicatesTrue
                  apply accepted
                  simp [duplicatesTrue]
                have referencesFalse :
                    (record.frontReference == record.backReference) = false := by
                  apply Bool.eq_false_of_not_eq_true
                  intro referencesTrue
                  apply accepted
                  simp [referencesTrue]
                have lengthAtLeast : 3 ≤ record.helixPath.length := by
                  have notShort : ¬ record.helixPath.length < 3 := by
                    simpa using shortFalse
                  omega
                have noDuplicates :
                    record.helixPath.eraseDups.length = record.helixPath.length := by
                  simpa using duplicatesFalse
                have referencesDistinct :
                    record.frontReference ≠ record.backReference := by
                  simpa using referencesFalse
                have assignmentEq : assignment =
                    { unit := StereoUnit.helix record.helixPath,
                      outcome := StereoOutcome.helical
                        (HelicalDescriptor.ofSense record.sense) } := by
                  simpa using produced.symm
                subst assignment
                refine {
                  pathAtomsInRange := pathBounds
                  frontReferenceInRange := frontBound
                  backReferenceInRange := backBound
                  pathHasAtLeastThreeAtoms := lengthAtLeast
                  pathNoDuplicates := noDuplicates
                  referencesDistinct := referencesDistinct
                  unit := rfl
                  outcome := ?_ }
                cases record.sense <;>
                  trivial

theorem ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?_sound_judgment
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (produced : result.polyhedralGeometryObservationAssignment? record = some assignment) :
    BlueBookP93.GeometryIngress.PolyhedralObservationAssignmentJudgment
      result record assignment :=
  result.polyhedralGeometryObservationAssignment?_sound_IR9 record assignment produced

/-! ## Whole-list and certified-pipeline soundness -/

/-- `eraseDups` never invents a list member. -/
private theorem mem_source_of_mem_eraseDups {α : Type} [BEq α] [LawfulBEq α]
    (input : List α) (candidate : α) (present : candidate ∈ input.eraseDups) :
    candidate ∈ input := by
  match input with
  | [] => simp at present
  | head :: tail =>
      rw [List.eraseDups_cons] at present
      rcases List.mem_cons.mp present with atHead | inFiltered
      · exact List.mem_cons.mpr (.inl atHead)
      · have inFilter := mem_source_of_mem_eraseDups _ candidate inFiltered
        exact List.mem_cons.mpr (.inr (List.mem_filter.mp inFilter).1)
termination_by input.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- `eraseDups` preserves membership under a lawful Boolean equality. -/
private theorem mem_eraseDups_of_mem {α : Type} [BEq α] [LawfulBEq α]
    (input : List α) (candidate : α) (present : candidate ∈ input) :
    candidate ∈ input.eraseDups := by
  match input with
  | [] => simp at present
  | head :: tail =>
      rw [List.eraseDups_cons]
      rcases List.mem_cons.mp present with atHead | inTail
      · exact List.mem_cons.mpr (.inl atHead)
      · by_cases same : candidate = head
        · exact List.mem_cons.mpr (.inl same)
        · apply List.mem_cons.mpr
          apply Or.inr
          apply mem_eraseDups_of_mem
          exact List.mem_filter.mpr ⟨inTail, by simp [same]⟩
termination_by input.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Exact membership semantics of `eraseDups`, used below to expose the conflict policy without
depending on list implementation details. -/
private theorem mem_eraseDups_iff_mem {α : Type} [BEq α] [LawfulBEq α]
    (input : List α) (candidate : α) :
    candidate ∈ input.eraseDups ↔ candidate ∈ input :=
  ⟨mem_source_of_mem_eraseDups input candidate,
    mem_eraseDups_of_mem input candidate⟩

/-- The implementation of duplicate erasure really is duplicate-free. -/
private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α]
    (input : List α) : input.eraseDups.Nodup := by
  match input with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, eraseDups_nodup _⟩
      rw [mem_eraseDups_iff_mem]
      simp
termination_by input.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Public generic membership certificate for lawful `eraseDups`. -/
theorem mem_eraseDups_iff_mem_lawful {α : Type} [BEq α] [LawfulBEq α]
    (input : List α) (candidate : α) :
    candidate ∈ input.eraseDups ↔ candidate ∈ input :=
  mem_eraseDups_iff_mem input candidate

/-- Public generic duplicate-freedom certificate for lawful `eraseDups`. -/
theorem eraseDups_nodup_lawful {α : Type} [BEq α] [LawfulBEq α]
    (input : List α) : input.eraseDups.Nodup :=
  eraseDups_nodup input

private theorem eraseDups_length_eq_one_iff_of_mem
    {α : Type} [BEq α] [LawfulBEq α]
    (input : List α) (representative : α) (present : representative ∈ input) :
    input.eraseDups.length = 1 ↔
      ∀ candidate ∈ input, candidate = representative := by
  constructor
  · intro lengthOne candidate candidatePresent
    obtain ⟨only, erasedEq⟩ := List.length_eq_one_iff.mp lengthOne
    have candidateErased := mem_eraseDups_of_mem input candidate candidatePresent
    have representativeErased := mem_eraseDups_of_mem input representative present
    have candidateEq : candidate = only := by
      simpa [erasedEq] using candidateErased
    have representativeEq : representative = only := by
      simpa [erasedEq] using representativeErased
    exact candidateEq.trans representativeEq.symm
  · intro allEqual
    cases input with
    | nil => simp at present
    | cons head tail =>
        have headEq : head = representative := allEqual head (by simp)
        subst head
        rw [List.eraseDups_cons]
        have filteredEmpty :
            tail.filter (fun candidate => !candidate == representative) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate candidatePresent
          have candidateEq : candidate = representative :=
            allEqual candidate (by simp [candidatePresent])
          simp [candidateEq]
        rw [filteredEmpty]
        rfl

/-- Independent agreement policy for a unit key.  The assignment must be a source member, and
every source observation for the same stereogenic unit must give the same outcome. -/
def ConflictFreeGeometryAssignmentJudgment
    (assignments : List StereoAssignment) (assignment : StereoAssignment) : Prop :=
  assignment ∈ assignments ∧
    ∀ other ∈ assignments, other.unit = assignment.unit →
      other.outcome = assignment.outcome

private theorem conflictFreeGeometryAssignmentAccepted_iff
    (assignments : List StereoAssignment) (assignment : StereoAssignment)
    (present : assignment ∈ assignments) :
    (((assignments.filter fun other => other.unit == assignment.unit).map
      StereoAssignment.outcome).eraseDups.length == 1) = true ↔
      ∀ other ∈ assignments, other.unit = assignment.unit →
        other.outcome = assignment.outcome := by
  let outcomes := (assignments.filter fun other => other.unit == assignment.unit).map
    StereoAssignment.outcome
  have ownOutcome : assignment.outcome ∈ outcomes := by
    apply List.mem_map.mpr
    exact ⟨assignment, List.mem_filter.mpr ⟨present, by simp⟩, rfl⟩
  constructor
  · intro accepted other otherPresent sameUnit
    have lengthOne : outcomes.eraseDups.length = 1 := by
      simpa [outcomes] using accepted
    have allOutcomes :=
      (eraseDups_length_eq_one_iff_of_mem outcomes assignment.outcome ownOutcome).mp lengthOne
    apply allOutcomes other.outcome
    apply List.mem_map.mpr
    exact ⟨other, List.mem_filter.mpr ⟨otherPresent, by simp [sameUnit]⟩, rfl⟩
  · intro agrees
    have allOutcomes : ∀ outcome ∈ outcomes, outcome = assignment.outcome := by
      intro outcome outcomePresent
      rcases List.mem_map.mp outcomePresent with ⟨other, otherPresent, rfl⟩
      rcases List.mem_filter.mp otherPresent with ⟨otherSource, sameUnit⟩
      exact agrees other otherSource (by simpa using sameUnit)
    have lengthOne :=
      (eraseDups_length_eq_one_iff_of_mem outcomes assignment.outcome ownOutcome).mpr
        allOutcomes
    simpa [outcomes] using lengthOne

/-- Exact independent membership theorem for the geometry conflict filter. -/
theorem mem_conflictFreeGeometryAssignments_iff
    (assignments : List StereoAssignment) (assignment : StereoAssignment) :
    assignment ∈ conflictFreeGeometryAssignments assignments ↔
      ConflictFreeGeometryAssignmentJudgment assignments assignment := by
  rw [conflictFreeGeometryAssignments, mem_eraseDups_iff_mem, List.mem_filter]
  constructor
  · rintro ⟨present, accepted⟩
    exact ⟨present,
      (conflictFreeGeometryAssignmentAccepted_iff assignments assignment present).mp accepted⟩
  · rintro ⟨present, agrees⟩
    exact ⟨present,
      (conflictFreeGeometryAssignmentAccepted_iff assignments assignment present).mpr agrees⟩

/-- The conflict-filtered assignment list has no duplicate public assignments. -/
theorem conflictFreeGeometryAssignments_nodup
    (assignments : List StereoAssignment) :
    (conflictFreeGeometryAssignments assignments).Nodup := by
  unfold conflictFreeGeometryAssignments
  exact eraseDups_nodup _

/-- Independent meaning of an observed assignment before the native/observed lists are merged. -/
inductive IndependentlyJudgedObservedGeometryAssignment
    (result : ChemistryNormalizationResult) (observations : IndexedCIPGeometryObservations)
    (native : List StereoAssignment) : StereoAssignment → Prop
  | axial {assignment record}
      (present : record ∈ observations.axes)
      (judged : BlueBookP93.GeometryIngress.AxialObservationAssignmentJudgment
        result record assignment)
      (notNative : ¬ native.any fun existing => existing.unit == assignment.unit) :
      IndependentlyJudgedObservedGeometryAssignment result observations native assignment
  | planar {assignment record}
      (present : record ∈ observations.planes)
      (judged : BlueBookP93.GeometryIngress.PlanarObservationAssignmentJudgment
        result record assignment) :
      IndependentlyJudgedObservedGeometryAssignment result observations native assignment
  | helical {assignment record}
      (present : record ∈ observations.helices)
      (judged : BlueBookP93.GeometryIngress.HelicalObservationAssignmentJudgment
        result record assignment) :
      IndependentlyJudgedObservedGeometryAssignment result observations native assignment
  | polyhedral {assignment record}
      (present : record ∈ observations.polyhedra)
      (judged : BlueBookP93.GeometryIngress.PolyhedralObservationAssignmentJudgment
        result record assignment)
      (notNative : ¬ native.any fun existing => existing.unit == assignment.unit) :
      IndependentlyJudgedObservedGeometryAssignment result observations native assignment

theorem conflictFreeGeometryAssignments_member_source
    (assignments : List StereoAssignment) (assignment : StereoAssignment)
    (present : assignment ∈ conflictFreeGeometryAssignments assignments) :
    assignment ∈ assignments := by
  have filteredDups : assignment ∈ (assignments.filter fun assignment =>
      ((assignments.filter fun other => other.unit == assignment.unit).map
        StereoAssignment.outcome).eraseDups.length == 1).eraseDups := by
    simpa only [conflictFreeGeometryAssignments] using present
  have filtered := mem_source_of_mem_eraseDups _ _ filteredDups
  exact (List.mem_filter.mp filtered).1

theorem observedGeometryAssignments_member_judged
    (result : ChemistryNormalizationResult) (observations : IndexedCIPGeometryObservations)
    (native : List StereoAssignment) (assignment : StereoAssignment)
    (present : assignment ∈ observedGeometryAssignments result observations native) :
    IndependentlyJudgedObservedGeometryAssignment result observations native assignment := by
  unfold observedGeometryAssignments at present
  split at present <;> rename_i admissible
  · simp at present
  · dsimp only at present
    simp only [List.mem_append] at present
    rcases present with ((axis | planar) | helical) | polyhedral
    · rcases List.mem_filter.mp axis with ⟨axisConflictFree, notNative⟩
      have axisRaw := conflictFreeGeometryAssignments_member_source _ _ axisConflictFree
      rcases List.mem_filterMap.mp axisRaw with ⟨record, recordPresent, produced⟩
      exact .axial recordPresent
        (result.axialGeometryObservationAssignment?_sound_P92 record assignment produced)
        (by simpa using notNative)
    · have planarRaw := conflictFreeGeometryAssignments_member_source _ _ planar
      rcases List.mem_filterMap.mp planarRaw with ⟨record, recordPresent, produced⟩
      exact .planar recordPresent
        (result.planarGeometryObservationAssignment?_sound_P92 record assignment produced)
    · have helicalRaw := conflictFreeGeometryAssignments_member_source _ _ helical
      rcases List.mem_filterMap.mp helicalRaw with ⟨record, recordPresent, produced⟩
      exact .helical recordPresent
        (result.helicalGeometryObservationAssignment?_sound_P92 record assignment produced)
    · rcases List.mem_filter.mp polyhedral with ⟨polyhedralConflictFree, notNative⟩
      have polyhedralRaw := conflictFreeGeometryAssignments_member_source _ _
        polyhedralConflictFree
      rcases List.mem_filterMap.mp polyhedralRaw with ⟨record, recordPresent, produced⟩
      exact .polyhedral recordPresent
        (result.polyhedralGeometryObservationAssignment?_sound_judgment
          record assignment produced)
        (by simpa using notNative)

/-- Independent final meaning of every result exposed by the certified geometry-aware analyzer. -/
def IndependentlyJudgedCertifiedGeometryStereoAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations) (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment ∨
    IndependentlyJudgedObservedGeometryAssignment certified.result observations
      (analyzeCertifiedNormalized certified) assignment

/-- End-to-end soundness of the complete currently exposed certified graph-plus-geometry
pipeline.  Retaining or removing a native tetrahedral result in favor of a validated polyhedral
frame cannot introduce an unjudged assignment. -/
theorem analyzeCertifiedNormalizedWithObservedGeometry_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations) (assignment : StereoAssignment)
    (present : assignment ∈
      analyzeCertifiedNormalizedWithObservedGeometry certified observations) :
    IndependentlyJudgedCertifiedGeometryStereoAssignment certified observations assignment := by
  unfold analyzeCertifiedNormalizedWithObservedGeometry at present
  simp only [List.mem_append] at present
  rcases present with native | observed
  · left
    have nativePresent : assignment ∈ analyzeCertifiedNormalized certified :=
      (List.mem_filter.mp native).1
    exact analyzeCertifiedNormalized_member_judged certified assignment nativePresent
  · right
    exact observedGeometryAssignments_member_judged certified.result observations
      (analyzeCertifiedNormalized certified) assignment observed

end TetraStereo.OneCenter
