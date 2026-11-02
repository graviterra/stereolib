import TetraStereo.OneCenter.CIPObservedHelicalSpatialConformance
import TetraStereo.OneCenter.CIPPlanarDerivedTetrahedronConformance
import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-backed exact planar-chirality ingress

The legacy planar observation carries only an orientation bit.  This replacement record exposes
the source roles in P-92.1.2.1.3: the planar unit `a-x-b`, the adjacent out-of-plane bond `y-z`,
and the two finite physical applicability observations which a static molecular graph cannot
establish by itself.  Production derives `a>b` through the official-context branch comparator and
computes `Rₚ/Sₚ` from the exact `a,b,y,z` determinant.  No raw planar sense is consumed.
-/

/-- Source-shaped finite input for one planar derived tetrahedron.  `firstReference` and
`secondReference` are unordered candidates for `a,b`; `pilotAtom` is `x`.  The restriction and
symmetry-plane fields are explicit physical observations, not facts inferred from constitution. -/
structure IndexedPlanarDerivedTetrahedronObservation where
  planeAtoms : List Nat
  pilotAtom : Nat
  firstReference : Nat
  secondReference : Nat
  inPlaneBondAtom : Nat
  outOfPlaneAtom : Nat
  torsionRestricted : Bool
  planeCannotBeSymmetryPlane : Bool
  deriving DecidableEq, Repr

/-- Additional naming applicability needed to request the P-93.5.5.1 preferred cyclophane-plane
symbol.  The composite locant itself belongs to the name renderer; this finite observation records
that it was selected from the ring or ring system viewed from the pilot atom. -/
structure IndexedCyclophanePlanarNamingObservation where
  planar : IndexedPlanarDerivedTetrahedronObservation
  locantIsCompositeRingLocantViewedFromPilotAtom : Bool
  deriving DecidableEq, Repr

namespace BlueBookP93.GeometryIngress

/-- Molecule-backed finite meaning of the source topology and physical applicability boundary.
The three vertices which define the reference plane are required to belong to `planeAtoms`; exact
coordinate coplanarity is checked separately. -/
def PlanarDerivedMolecularFrameJudgment
    (result : ChemistryNormalizationResult)
    (record : IndexedPlanarDerivedTetrahedronObservation) : Prop :=
  3 ≤ record.planeAtoms.length ∧
    record.planeAtoms.Nodup ∧
    (∀ atom ∈ record.planeAtoms, atom < result.parsed.atomCount) ∧
    record.pilotAtom < result.parsed.atomCount ∧
    record.firstReference < result.parsed.atomCount ∧
    record.secondReference < result.parsed.atomCount ∧
    record.inPlaneBondAtom < result.parsed.atomCount ∧
    record.outOfPlaneAtom < result.parsed.atomCount ∧
    record.pilotAtom ∈ record.planeAtoms ∧
    record.firstReference ∈ record.planeAtoms ∧
    record.secondReference ∈ record.planeAtoms ∧
    record.inPlaneBondAtom ∈ record.planeAtoms ∧
    record.outOfPlaneAtom ∉ record.planeAtoms ∧
    [record.pilotAtom, record.firstReference, record.secondReference,
      record.inPlaneBondAtom].Nodup ∧
    record.firstReference ≠ record.secondReference ∧
    record.inPlaneBondAtom ≠ record.outOfPlaneAtom ∧
    record.firstReference ∈
      result.geometryPriorityState.1.writtenNeighbors record.pilotAtom ∧
    record.secondReference ∈
      result.geometryPriorityState.1.writtenNeighbors record.pilotAtom ∧
    record.inPlaneBondAtom ∈
      result.geometryPriorityState.1.writtenNeighbors record.pilotAtom ∧
    record.outOfPlaneAtom ∈
      result.geometryPriorityState.1.writtenNeighbors record.inPlaneBondAtom ∧
    record.torsionRestricted = true ∧
    record.planeCannotBeSymmetryPlane = true

/-- Independent meaning of orienting an unordered candidate pair as strict `high,low`. -/
def StrictReferencePairJudgment (decision : Option Ordering)
    (first second high low : Nat) : Prop :=
  (decision = some .gt ∧ high = first ∧ low = second) ∨
    (decision = some .lt ∧ high = second ∧ low = first)

/-- Complete independent judgment for an emitted source-shaped planar assignment. -/
def PlanarDerivedObservationAssignmentJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  let context := result.geometryPriorityState
  ∃ high low highPoint lowPoint yPoint zPoint planePoints descriptor,
    PlanarDerivedMolecularFrameJudgment result record ∧
    StrictReferencePairJudgment
      (compareBranchesThroughOfficialContext? result context.1 context.2.2 context.2.1
        record.pilotAtom record.firstReference record.secondReference)
      record.firstReference record.secondReference high low ∧
    SpatialPointAt spatial high highPoint ∧
    SpatialPointAt spatial low lowPoint ∧
    SpatialPointAt spatial record.inPlaneBondAtom yPoint ∧
    SpatialPointAt spatial record.outOfPlaneAtom zPoint ∧
    record.planeAtoms.mapM (fun atom => spatial.positions[atom]?) = some planePoints ∧
    (∀ point ∈ planePoints,
      CartesianPoint3.orientedVolume highPoint lowPoint yPoint point = 0) ∧
    BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor
      highPoint lowPoint yPoint zPoint descriptor ∧
    assignment =
      { unit := StereoUnit.plane record.planeAtoms
        outcome := StereoOutcome.planar descriptor }

/-- Independent P-92-to-P-93.5.5.1 naming judgment.  The general `Rₚ/Sₚ` configuration is
coordinate-derived above; for a cyclophane reference with the required composite pilot-view
locant, the same plane is named by the unique preferred `P/M` representative. -/
def PreferredCyclophanePlanarDescriptorJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedCyclophanePlanarNamingObservation)
    (preferred : BlueBookP93.Cyclic.CyclophanePlaneDescriptor) : Prop :=
  record.locantIsCompositeRingLocantViewedFromPilotAtom = true ∧
    ∃ assignment general,
      PlanarDerivedObservationAssignmentJudgment result spatial record.planar assignment ∧
      assignment.outcome = StereoOutcome.planar general ∧
      preferred =
        BlueBookP93.Cyclic.CyclophanePlaneDescriptor.preferredOfGeneralPlanar general

end BlueBookP93.GeometryIngress

/-- Constructively decidable source-topology/applicability check. -/
def ChemistryNormalizationResult.planarDerivedMolecularFrameOK?
    (result : ChemistryNormalizationResult)
    (record : IndexedPlanarDerivedTetrahedronObservation) : Bool :=
  decide (3 ≤ record.planeAtoms.length) &&
    decide record.planeAtoms.Nodup &&
    record.planeAtoms.all (fun atom => decide (atom < result.parsed.atomCount)) &&
    decide (record.pilotAtom < result.parsed.atomCount) &&
    decide (record.firstReference < result.parsed.atomCount) &&
    decide (record.secondReference < result.parsed.atomCount) &&
    decide (record.inPlaneBondAtom < result.parsed.atomCount) &&
    decide (record.outOfPlaneAtom < result.parsed.atomCount) &&
    record.planeAtoms.contains record.pilotAtom &&
    record.planeAtoms.contains record.firstReference &&
    record.planeAtoms.contains record.secondReference &&
    record.planeAtoms.contains record.inPlaneBondAtom &&
    !record.planeAtoms.contains record.outOfPlaneAtom &&
    decide [record.pilotAtom, record.firstReference, record.secondReference,
      record.inPlaneBondAtom].Nodup &&
    decide (record.firstReference ≠ record.secondReference) &&
    decide (record.inPlaneBondAtom ≠ record.outOfPlaneAtom) &&
    (result.geometryPriorityState.1.writtenNeighbors record.pilotAtom).contains
      record.firstReference &&
    (result.geometryPriorityState.1.writtenNeighbors record.pilotAtom).contains
      record.secondReference &&
    (result.geometryPriorityState.1.writtenNeighbors record.pilotAtom).contains
      record.inPlaneBondAtom &&
    (result.geometryPriorityState.1.writtenNeighbors record.inPlaneBondAtom).contains
      record.outOfPlaneAtom &&
    record.torsionRestricted && record.planeCannotBeSymmetryPlane

theorem ChemistryNormalizationResult.planarDerivedMolecularFrameOK?_eq_true_iff
    (result : ChemistryNormalizationResult)
    (record : IndexedPlanarDerivedTetrahedronObservation) :
    result.planarDerivedMolecularFrameOK? record = true ↔
      BlueBookP93.GeometryIngress.PlanarDerivedMolecularFrameJudgment result record := by
  simp [ChemistryNormalizationResult.planarDerivedMolecularFrameOK?,
    BlueBookP93.GeometryIngress.PlanarDerivedMolecularFrameJudgment,
    List.all_eq_true]
  tauto

/-- Select both the senior and junior references; ties and unavailable comparisons are refused. -/
def strictReferencePairOfDecision? (decision : Option Ordering)
    (first second : Nat) : Option (Nat × Nat) :=
  match decision with
  | some .gt => some (first, second)
  | some .lt => some (second, first)
  | _ => none

theorem strictReferencePairOfDecision?_eq_some_iff
    (decision : Option Ordering) (first second high low : Nat) :
    strictReferencePairOfDecision? decision first second = some (high, low) ↔
      BlueBookP93.GeometryIngress.StrictReferencePairJudgment
        decision first second high low := by
  cases decision with
  | none => simp [strictReferencePairOfDecision?,
      BlueBookP93.GeometryIngress.StrictReferencePairJudgment]
  | some ordering =>
      cases ordering <;>
        simp [strictReferencePairOfDecision?,
          BlueBookP93.GeometryIngress.StrictReferencePairJudgment, eq_comm]

/-- Exact source-shaped planar assignment.  The output descriptor is derived, never supplied. -/
def ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation) : Option StereoAssignment := do
  if result.planarDerivedMolecularFrameOK? record then
  let context := result.geometryPriorityState
  let references ← strictReferencePairOfDecision?
    (compareBranchesThroughOfficialContext? result context.1 context.2.2 context.2.1
      record.pilotAtom record.firstReference record.secondReference)
    record.firstReference record.secondReference
  let highPoint ← spatial.positions[references.1]?
  let lowPoint ← spatial.positions[references.2]?
  let yPoint ← spatial.positions[record.inPlaneBondAtom]?
  let zPoint ← spatial.positions[record.outOfPlaneAtom]?
  let planePoints ← record.planeAtoms.mapM (fun atom => spatial.positions[atom]?)
  if planePoints.all (fun point =>
      CartesianPoint3.orientedVolume highPoint lowPoint yPoint point == 0) then
  let descriptor ← planarDescriptorOfDerivedTetrahedron? highPoint lowPoint yPoint zPoint
  some { unit := StereoUnit.plane record.planeAtoms
         outcome := StereoOutcome.planar descriptor }
  else none
  else none

/-- Every successful source-shaped planar assignment has the complete independent molecular,
priority, coordinate-coplanarity, determinant-sign, and output-family judgment. -/
theorem ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?_sound
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation) (assignment : StereoAssignment)
    (produced : result.planarDerivedTetrahedronAssignment? spatial record = some assignment) :
    BlueBookP93.GeometryIngress.PlanarDerivedObservationAssignmentJudgment
      result spatial record assignment := by
  unfold ChemistryNormalizationResult.planarDerivedTetrahedronAssignment? at produced
  split at produced <;> rename_i frameAccepted
  · have frame : BlueBookP93.GeometryIngress.PlanarDerivedMolecularFrameJudgment
        result record := by
      exact (result.planarDerivedMolecularFrameOK?_eq_true_iff record).mp
        frameAccepted
    generalize referencesEq : strictReferencePairOfDecision?
      (compareBranchesThroughOfficialContext? result result.geometryPriorityState.1
        result.geometryPriorityState.2.2 result.geometryPriorityState.2.1
        record.pilotAtom record.firstReference record.secondReference)
      record.firstReference record.secondReference = references at produced
    cases references with
    | none => simp [referencesEq] at produced
    | some references =>
        cases highEq : spatial.positions[references.1]? with
        | none => simp [referencesEq, highEq] at produced
        | some highPoint =>
            cases lowEq : spatial.positions[references.2]? with
            | none => simp [referencesEq, highEq, lowEq] at produced
            | some lowPoint =>
                cases yEq : spatial.positions[record.inPlaneBondAtom]? with
                | none => simp [referencesEq, yEq] at produced
                | some yPoint =>
                    cases zEq : spatial.positions[record.outOfPlaneAtom]? with
                    | none => simp [referencesEq, yEq, zEq] at produced
                    | some zPoint =>
                        cases planeEq : record.planeAtoms.mapM
                            (fun atom => spatial.positions[atom]?) with
                        | none =>
                            simp [referencesEq, yEq, zEq, planeEq] at produced
                        | some planePoints =>
                            simp only [referencesEq, instMonadOption, Option.bind_some, highEq,
                              lowEq, yEq, zEq, planeEq] at produced
                            by_cases planeAccepted : planePoints.all (fun point =>
                                CartesianPoint3.orientedVolume
                                  highPoint lowPoint yPoint point == 0) = true
                            · rw [if_pos planeAccepted] at produced
                              have coplanar : ∀ point ∈ planePoints,
                                  CartesianPoint3.orientedVolume
                                    highPoint lowPoint yPoint point = 0 := by
                                simpa only [List.all_eq_true, beq_iff_eq] using planeAccepted
                              cases descriptorEq : planarDescriptorOfDerivedTetrahedron?
                                  highPoint lowPoint yPoint zPoint with
                              | none =>
                                  simp only [descriptorEq, Option.bind_none] at produced
                                  simp at produced
                              | some descriptor =>
                                  have descriptorJudgment :=
                                    (planarDescriptorOfDerivedTetrahedron?_eq_some_iff
                                      highPoint lowPoint yPoint zPoint descriptor).mp
                                      descriptorEq
                                  rcases references with ⟨high, low⟩
                                  have referenceJudgment :=
                                    (strictReferencePairOfDecision?_eq_some_iff
                                      _ _ _ high low).mp referencesEq
                                  have assignmentEq : assignment =
                                      { unit := StereoUnit.plane record.planeAtoms
                                        outcome := StereoOutcome.planar descriptor } := by
                                    simpa only [descriptorEq, Option.bind_some,
                                      Option.some.injEq] using produced.symm
                                  exact ⟨high, low, highPoint, lowPoint, yPoint, zPoint,
                                    planePoints, descriptor, frame, referenceJudgment,
                                    highEq, lowEq, yEq, zEq, planeEq, coplanar,
                                    descriptorJudgment, assignmentEq⟩
                            · rw [if_neg planeAccepted] at produced
                              simp at produced
  · simp_all

/-- The source-shaped planar evaluator succeeds exactly for the independent molecular,
priority, coplanarity, and determinant judgment.  Thus its refusals are characterized as well as
its outputs. -/
theorem ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation) (assignment : StereoAssignment) :
    result.planarDerivedTetrahedronAssignment? spatial record = some assignment ↔
      BlueBookP93.GeometryIngress.PlanarDerivedObservationAssignmentJudgment
        result spatial record assignment := by
  constructor
  · exact result.planarDerivedTetrahedronAssignment?_sound spatial record assignment
  · rintro ⟨high, low, highPoint, lowPoint, yPoint, zPoint, planePoints, descriptor,
      frame, references, highEq, lowEq, yEq, zEq, planeEq, coplanar,
      descriptorJudgment, assignmentEq⟩
    have frameAccepted :=
      (result.planarDerivedMolecularFrameOK?_eq_true_iff record).mpr frame
    have referencesEq :=
      (strictReferencePairOfDecision?_eq_some_iff _ _ _ high low).mpr references
    have descriptorEq :=
      (planarDescriptorOfDerivedTetrahedron?_eq_some_iff
        highPoint lowPoint yPoint zPoint descriptor).mpr descriptorJudgment
    change spatial.positions[high]? = some highPoint at highEq
    change spatial.positions[low]? = some lowPoint at lowEq
    change spatial.positions[record.inPlaneBondAtom]? = some yPoint at yEq
    change spatial.positions[record.outOfPlaneAtom]? = some zPoint at zEq
    subst assignment
    simp [ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?, frameAccepted,
      referencesEq, highEq, lowEq, yEq, zEq, planeEq, descriptorEq]
    exact coplanar

/-- Independent readiness of one supplied molecule-backed planar observation. -/
def BlueBookP93.GeometryIngress.PlanarDerivedObservationReady
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation) : Prop :=
  ∃ assignment,
    BlueBookP93.GeometryIngress.PlanarDerivedObservationAssignmentJudgment
      result spatial record assignment

/-- The local evaluator is present exactly when the complete independent planar judgment has a
witness. -/
theorem ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?_isSome_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation) :
    (result.planarDerivedTetrahedronAssignment? spatial record).isSome = true ↔
      BlueBookP93.GeometryIngress.PlanarDerivedObservationReady
        result spatial record := by
  rw [Option.isSome_iff_exists]
  exact ⟨fun ⟨assignment, computed⟩ =>
      ⟨assignment,
        (result.planarDerivedTetrahedronAssignment?_eq_some_iff
          spatial record assignment).mp computed⟩,
    fun ⟨assignment, judged⟩ =>
      ⟨assignment,
        (result.planarDerivedTetrahedronAssignment?_eq_some_iff
          spatial record assignment).mpr judged⟩⟩

/-- Exact refusal boundary for one supplied planar observation. -/
theorem ChemistryNormalizationResult.planarDerivedTetrahedronAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation) :
    result.planarDerivedTetrahedronAssignment? spatial record = none ↔
      ¬ BlueBookP93.GeometryIngress.PlanarDerivedObservationReady
        result spatial record := by
  rw [← not_iff_not]
  simp only [not_not]
  rw [← result.planarDerivedTetrahedronAssignment?_isSome_iff spatial record]
  exact Option.ne_none_iff_isSome

/-- A fixed observation has at most one independently valid public assignment. -/
theorem BlueBookP93.GeometryIngress.planarDerivedObservationAssignmentJudgment_subsingleton
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    {left right : StereoAssignment}
    (leftJudged : PlanarDerivedObservationAssignmentJudgment
      result spatial record left)
    (rightJudged : PlanarDerivedObservationAssignmentJudgment
      result spatial record right) :
    left = right := by
  have leftComputed :=
    (result.planarDerivedTetrahedronAssignment?_eq_some_iff
      spatial record left).mpr leftJudged
  have rightComputed :=
    (result.planarDerivedTetrahedronAssignment?_eq_some_iff
      spatial record right).mpr rightJudged
  rw [leftComputed] at rightComputed
  exact Option.some.inj rightComputed

/-- Coordinate-derived preferred cyclophane-plane nomenclature.  The result type is the
cyclophane-plane vocabulary, so its `P/M` cannot be confused with a helical `StereoOutcome`. -/
def ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedCyclophanePlanarNamingObservation) :
    Option BlueBookP93.Cyclic.CyclophanePlaneDescriptor := do
  if record.locantIsCompositeRingLocantViewedFromPilotAtom then
  let assignment ← result.planarDerivedTetrahedronAssignment? spatial record.planar
  match assignment.outcome with
  | .planar general =>
      some (BlueBookP93.Cyclic.CyclophanePlaneDescriptor.preferredOfGeneralPlanar general)
  | _ => none
  else none

/-- The naming evaluator succeeds exactly for the independent molecular/coordinate planar
judgment plus the P-93.5.5.1 composite-locant applicability condition and preferred-symbol map. -/
theorem ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedCyclophanePlanarNamingObservation)
    (preferred : BlueBookP93.Cyclic.CyclophanePlaneDescriptor) :
    result.preferredCyclophanePlanarDescriptor? spatial record = some preferred ↔
      BlueBookP93.GeometryIngress.PreferredCyclophanePlanarDescriptorJudgment
        result spatial record preferred := by
  constructor
  · intro computed
    unfold ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor? at computed
    split at computed <;> rename_i locantAccepted
    · cases assignmentEq : result.planarDerivedTetrahedronAssignment?
          spatial record.planar with
      | none => simp [assignmentEq] at computed
      | some assignment =>
          have assignmentJudgment :=
            (result.planarDerivedTetrahedronAssignment?_eq_some_iff
              spatial record.planar assignment).mp assignmentEq
          rcases assignmentJudgment with
            ⟨high, low, highPoint, lowPoint, yPoint, zPoint, planePoints, general,
              frame, references, highEq, lowEq, yEq, zEq, planeEq, coplanar,
              descriptorJudgment, assignmentStructure⟩
          have assignmentOutcome : assignment.outcome = StereoOutcome.planar general := by
            rw [assignmentStructure]
          have preferredEq :
              BlueBookP93.Cyclic.CyclophanePlaneDescriptor.preferredOfGeneralPlanar general =
                preferred := by
            simpa [assignmentEq, assignmentOutcome] using computed
          exact ⟨locantAccepted, assignment, general,
            ⟨high, low, highPoint, lowPoint, yPoint, zPoint, planePoints, general,
              frame, references, highEq, lowEq, yEq, zEq, planeEq, coplanar,
              descriptorJudgment, assignmentStructure⟩,
            assignmentOutcome, preferredEq.symm⟩
    · simp_all
  · rintro ⟨locantAccepted, assignment, general, assignmentJudgment,
      assignmentOutcome, rfl⟩
    have assignmentEq :=
      (result.planarDerivedTetrahedronAssignment?_eq_some_iff
        spatial record.planar assignment).mpr assignmentJudgment
    simp [ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor?,
      locantAccepted, assignmentEq, assignmentOutcome]

/-- A successful cyclophane naming result is always one of the preferred P-93.5.5.1 symbols;
the acceptable but nonpreferred `Rₚ/Sₚ` spellings cannot escape this function. -/
theorem ChemistryNormalizationResult.preferredCyclophanePlanarDescriptor?_is_preferred
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedCyclophanePlanarNamingObservation)
    (preferred : BlueBookP93.Cyclic.CyclophanePlaneDescriptor)
    (computed : result.preferredCyclophanePlanarDescriptor? spatial record = some preferred) :
    BlueBookP93.Cyclic.PreferredCyclophanePlaneDescriptor preferred := by
  have judged :=
    (result.preferredCyclophanePlanarDescriptor?_eq_some_iff
      spatial record preferred).mp computed
  rcases judged with ⟨_, assignment, general, assignmentJudgment, assignmentOutcome, rfl⟩
  exact BlueBookP93.Cyclic.preferredOfGeneralPlanar_is_preferred general

/-! ## Exact list semantics for supplied planar observations -/

/-- Evaluate supplied molecule-backed planar observations and retain a unit only when every
successful observation of that unit agrees. -/
def ChemistryNormalizationResult.derivedPlanarSpatialAssignments
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation) :
    List StereoAssignment :=
  conflictFreeGeometryAssignments
    (records.filterMap (result.planarDerivedTetrahedronAssignment? spatial))

/-- Independent meaning of a conflict-free assignment from a list of supplied planar
observations.  Both source existence and agreement of every independently successful observation
of the same plane are explicit. -/
def BlueBookP93.GeometryIngress.PlanarDerivedConflictFreeAssignmentJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  (∃ record ∈ records,
    PlanarDerivedObservationAssignmentJudgment result spatial record assignment) ∧
  ∀ otherRecord ∈ records, ∀ otherAssignment,
    PlanarDerivedObservationAssignmentJudgment
      result spatial otherRecord otherAssignment →
    otherAssignment.unit = assignment.unit →
    otherAssignment.outcome = assignment.outcome

/-- Exact membership of the conflict-free planar branch. -/
theorem ChemistryNormalizationResult.mem_derivedPlanarSpatialAssignments_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) :
    assignment ∈ result.derivedPlanarSpatialAssignments spatial records ↔
      BlueBookP93.GeometryIngress.PlanarDerivedConflictFreeAssignmentJudgment
        result spatial records assignment := by
  rw [ChemistryNormalizationResult.derivedPlanarSpatialAssignments,
    mem_conflictFreeGeometryAssignments_iff]
  constructor
  · rintro ⟨candidatePresent, agrees⟩
    rcases List.mem_filterMap.mp candidatePresent with
      ⟨record, recordPresent, computed⟩
    refine ⟨⟨record, recordPresent,
      (result.planarDerivedTetrahedronAssignment?_eq_some_iff
        spatial record assignment).mp computed⟩, ?_⟩
    intro otherRecord otherRecordPresent otherAssignment otherJudged sameUnit
    have otherComputed :=
      (result.planarDerivedTetrahedronAssignment?_eq_some_iff
        spatial otherRecord otherAssignment).mpr otherJudged
    have otherCandidate : otherAssignment ∈
        records.filterMap (result.planarDerivedTetrahedronAssignment? spatial) :=
      List.mem_filterMap.mpr ⟨otherRecord, otherRecordPresent, otherComputed⟩
    exact agrees otherAssignment otherCandidate sameUnit
  · rintro ⟨⟨record, recordPresent, judged⟩, allAgree⟩
    have computed :=
      (result.planarDerivedTetrahedronAssignment?_eq_some_iff
        spatial record assignment).mpr judged
    refine ⟨List.mem_filterMap.mpr ⟨record, recordPresent, computed⟩, ?_⟩
    intro otherAssignment otherCandidate sameUnit
    rcases List.mem_filterMap.mp otherCandidate with
      ⟨otherRecord, otherRecordPresent, otherComputed⟩
    exact allAgree otherRecord otherRecordPresent otherAssignment
      ((result.planarDerivedTetrahedronAssignment?_eq_some_iff
        spatial otherRecord otherAssignment).mp otherComputed) sameUnit

/-- The conflict-free planar branch has no duplicate public assignments. -/
theorem ChemistryNormalizationResult.derivedPlanarSpatialAssignments_nodup
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (records : List IndexedPlanarDerivedTetrahedronObservation) :
    (result.derivedPlanarSpatialAssignments spatial records).Nodup := by
  exact conflictFreeGeometryAssignments_nodup _

/-! ## Joined analyzer which excludes the underdetermined raw planar branch -/

/-- Keep coordinate-validated axes and helices and all independently certified polyhedral input,
but remove legacy raw planar senses. -/
def IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation
    (observations : IndexedCIPGeometryObservations)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    IndexedCIPGeometryObservations :=
  { observations.withSpatiallyValidatedAxesAndHelices result spatial with planes := [] }

/-- The already-certified native, axial, helical, and polyhedral prefix against which derived
planar units are checked for ownership conflicts. -/
def derivedPlanarSpatialBaseAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations) :
    List StereoAssignment :=
  analyzeCertifiedNormalizedWithObservedGeometry certified
    (observations.withoutRawPlanesAfterSpatialValidation certified.result spatial)

/-- Independent public-contribution policy for the derived planar branch: the planar observation
list agrees on the result, and no earlier certified branch owns the same stereogenic unit. -/
def BlueBookP93.GeometryIngress.PlanarDerivedPublicContributionJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  PlanarDerivedConflictFreeAssignmentJudgment
    certified.result spatial records assignment ∧
  ∀ existing ∈ derivedPlanarSpatialBaseAssignments certified spatial observations,
    existing.unit ≠ assignment.unit

/-- Public joined route for exact axial, terminal-reference helical, and source-shaped derived
planar coordinates.  Derived planar results cannot replace or duplicate an existing unit. -/
def analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation) :
    List StereoAssignment :=
  let base := derivedPlanarSpatialBaseAssignments certified spatial observations
  let derived := (certified.result.derivedPlanarSpatialAssignments
    spatial derivedPlanes).filter fun assignment =>
    !(base.any fun existing => existing.unit == assignment.unit)
  (base ++ derived).eraseDups

/-- Exact public membership: a result is either retained from the earlier certified branches or
is an independently conflict-free planar contribution whose unit has no earlier owner. -/
theorem mem_analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) :
    assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
        certified spatial observations derivedPlanes ↔
      assignment ∈ derivedPlanarSpatialBaseAssignments certified spatial observations ∨
      BlueBookP93.GeometryIngress.PlanarDerivedPublicContributionJudgment
        certified spatial observations derivedPlanes assignment := by
  simp [analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry,
    BlueBookP93.GeometryIngress.PlanarDerivedPublicContributionJudgment,
    mem_eraseDups_iff_mem_lawful,
    certified.result.mem_derivedPlanarSpatialAssignments_iff]

/-- The complete joined public result has no duplicate assignments. -/
theorem analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation) :
    (analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
      certified spatial observations derivedPlanes).Nodup := by
  unfold analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
  exact eraseDups_nodup_lawful _

/-- Independent readiness of one supplied planar observation for public emission.  It includes
membership in the supplied observation list, a complete local assignment judgment, global
agreement for that plane, and absence of an earlier public owner. -/
def BlueBookP93.GeometryIngress.PlanarDerivedObservationPublicReady
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation) : Prop :=
  record ∈ records ∧
    ∃ assignment,
      PlanarDerivedObservationAssignmentJudgment
        certified.result spatial record assignment ∧
      PlanarDerivedPublicContributionJudgment
        certified spatial observations records assignment

/-- Every public-ready supplied planar observation contributes exactly one public assignment.
Uniqueness follows from the exact local evaluator; literal list multiplicity is additionally
controlled by the public analyzer's `Nodup` theorem. -/
theorem every_publicReady_planarDerivedObservation_occurs_exactly_once
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (ready : BlueBookP93.GeometryIngress.PlanarDerivedObservationPublicReady
      certified spatial observations records record) :
    ∃! assignment,
      assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
        certified spatial observations records ∧
      BlueBookP93.GeometryIngress.PlanarDerivedObservationAssignmentJudgment
        certified.result spatial record assignment := by
  rcases ready with ⟨recordPresent, assignment, assignmentJudged, publicJudged⟩
  have assignmentPresent : assignment ∈
      analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
        certified spatial observations records :=
    (mem_analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_iff
      certified spatial observations records assignment).mpr (.inr publicJudged)
  refine ⟨assignment, ⟨assignmentPresent, assignmentJudged⟩, ?_⟩
  intro other ⟨otherPresent, otherJudged⟩
  exact BlueBookP93.GeometryIngress.planarDerivedObservationAssignmentJudgment_subsingleton
    certified.result spatial record otherJudged assignmentJudged

/-- Literal list-multiplicity form of exact-once public planar completeness. -/
theorem every_publicReady_planarDerivedObservation_count_eq_one
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (records : List IndexedPlanarDerivedTetrahedronObservation)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (ready : BlueBookP93.GeometryIngress.PlanarDerivedObservationPublicReady
      certified spatial observations records record) :
    ∃ assignment,
      BlueBookP93.GeometryIngress.PlanarDerivedObservationAssignmentJudgment
        certified.result spatial record assignment ∧
      List.count assignment
        (analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
          certified spatial observations records) = 1 := by
  rcases every_publicReady_planarDerivedObservation_occurs_exactly_once
      certified spatial observations records record ready with
    ⟨assignment, ⟨present, judged⟩, unique⟩
  exact ⟨assignment, judged,
    List.count_eq_one_of_mem
      (analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_nodup
        certified spatial observations records) present⟩

/-- Independent classification of every member of the source-shaped planar spatial route. -/
def IndependentlyJudgedCertifiedDerivedPlanarSpatialAssignment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment) : Prop :=
  IndependentlyJudgedCertifiedSpatialAxialHelicalStereoAssignment certified spatial
      { observations with planes := [] } assignment ∨
    ∃ record ∈ derivedPlanes,
      BlueBookP93.GeometryIngress.PlanarDerivedObservationAssignmentJudgment
        certified.result spatial record assignment

/-- `eraseDups` never introduces a planar-route assignment. -/
private theorem mem_source_of_mem_eraseDups_planar {α : Type} [BEq α] [LawfulBEq α]
    (input : List α) (candidate : α) (present : candidate ∈ input.eraseDups) :
    candidate ∈ input := by
  match input with
  | [] => simp at present
  | head :: tail =>
      rw [List.eraseDups_cons] at present
      rcases List.mem_cons.mp present with atHead | inFiltered
      · exact List.mem_cons.mpr (.inl atHead)
      · have inFilter := mem_source_of_mem_eraseDups_planar _ candidate inFiltered
        exact List.mem_cons.mpr (.inr (List.mem_filter.mp inFilter).1)
termination_by input.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Every emitted member has either the existing certified native/axial/helical/polyhedral
judgment or the complete molecule-backed exact planar-derived-tetrahedron judgment. -/
theorem analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry_member_judged
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (assignment : StereoAssignment)
    (present : assignment ∈ analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry
      certified spatial observations derivedPlanes) :
    IndependentlyJudgedCertifiedDerivedPlanarSpatialAssignment
      certified spatial observations derivedPlanes assignment := by
  let rawFree : IndexedCIPGeometryObservations := { observations with planes := [] }
  let filtered := observations.withoutRawPlanesAfterSpatialValidation certified.result spatial
  let base := analyzeCertifiedNormalizedWithObservedGeometry certified filtered
  let candidates := derivedPlanes.filterMap
    (certified.result.planarDerivedTetrahedronAssignment? spatial)
  let derived := (conflictFreeGeometryAssignments candidates).filter fun assignment =>
    !(base.any fun existing => existing.unit == assignment.unit)
  have inErased : assignment ∈ (base ++ derived).eraseDups := by
    simpa [analyzeCertifiedNormalizedWithDerivedPlanarSpatialGeometry,
      filtered, base, candidates, derived] using present
  have inSource : assignment ∈ base ++ derived :=
    mem_source_of_mem_eraseDups_planar (base ++ derived) assignment inErased
  rcases List.mem_append.mp inSource with inBase | inDerived
  · left
    have baseJudged :=
      analyzeCertifiedNormalizedWithSpatiallyValidatedAxialHelicalGeometry_member_judged
        certified spatial rawFree assignment (by
          simpa [analyzeCertifiedNormalizedWithSpatiallyValidatedAxialHelicalGeometry,
            IndexedCIPGeometryObservations.withoutRawPlanesAfterSpatialValidation,
            filtered, base, rawFree,
            IndexedCIPGeometryObservations.withSpatiallyValidatedAxesAndHelices,
            IndexedCIPGeometryObservations.withSpatiallyValidatedAxes] using inBase)
    simpa [rawFree] using baseJudged
  · right
    have inConflictFree : assignment ∈ conflictFreeGeometryAssignments candidates :=
      (List.mem_filter.mp inDerived).1
    have inCandidates : assignment ∈ candidates :=
      conflictFreeGeometryAssignments_member_source candidates assignment inConflictFree
    rcases List.mem_filterMap.mp inCandidates with ⟨record, recordPresent, produced⟩
    exact ⟨record, recordPresent,
      certified.result.planarDerivedTetrahedronAssignment?_sound
        spatial record assignment produced⟩

end TetraStereo.OneCenter
