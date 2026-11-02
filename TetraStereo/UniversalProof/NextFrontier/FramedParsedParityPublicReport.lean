import TetraStereo.UniversalProof.NextFrontier.FramedParsedParitySchedulerLeaves
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000







namespace TetraStereo.UniversalProof.FramedParsedParityPublicReport

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParityFamily
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
open TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves

/-- The public analyzer's exact residual computation after its descriptor state is known. -/
def reportFromState (result : ChemistryNormalizationResult) (state : RawDescriptorState) :
    List StereoAssignment :=
  if !result.parsed.rule2MassesKnown? then [] else
  if !result.expandedStereochemicalAdmissible? then [] else
  let mol := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel mol
  let geometryState := normalizedGeometryDescriptorState result mol fuel state
  let networks := normalizedCoupledGeometryNetworks result mol geometryState fuel
  let bonds := ordinaryDoubleBondAssignments result mol state fuel
  tetrahedralAssignments result mol state fuel ++ bonds ++
    result.stereobonds.doubleBondAssignments.filterMap
      (coupledOrDescriptorDependentDoubleBondAssignment? result mol geometryState fuel bonds networks) ++
    oddCumuleneDoubleBondAssignments result mol geometryState fuel ++
    mol.extendedTetrahedralParityCarriers.map
      (extendedTetrahedralAxialAssignment result mol geometryState fuel)

/-- Reusable semantic equality, requiring the actual discovery equation. -/
theorem analyzeNormalized_of_discovery (result : ChemistryNormalizationResult)
    (state : RawDescriptorState)
    (discovered : discoverRawDescriptors result result.parsed.withExplicitHydrogens
      (analysisFuel result.parsed.withExplicitHydrogens) = state) :
    analyzeNormalized result = reportFromState result state := by
  calc
    analyzeNormalized result = reportFromState result
        (discoverRawDescriptors result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)) := rfl
    _ = reportFromState result state := congrArg (reportFromState result) discovered

/-- Independent expected central outcome, including the exact equal-arm refusal. -/
def expectedCenterOutcome (center left right : TetrahedralInputParity) : StereoOutcome :=
  if left == right then .refused .notStereogenic else
    .pseudoTetrahedral
      (match descriptorOfParity center (permutationIsEven (expectedPositions left)) with
       | .R => .r
       | .S => .s)

/-- Full report in actual increasing atom-index order; both assigned arm rows are retained. -/
def expectedReport (center left right : TetrahedralInputParity) : List StereoAssignment :=
  [{ unit := .tetrahedral 1, outcome := expectedCenterOutcome center left right },
   { unit := .tetrahedral 2, outcome := .tetrahedral (descriptorOfParity left false) },
   { unit := .tetrahedral 7, outcome := .tetrahedral (descriptorOfParity right false) }]

/-- Structural route reduction for arbitrary states. Only the three annotated carbon
atoms survive, and every non-tetrahedral report segment is empty. -/
theorem report_shape (center left right : TetrahedralInputParity) (state : RawDescriptorState) :
    reportFromState (actualResult center left right) state =
      [1, 2, 7].filterMap
        (annotatedTetrahedralAssignment? (actualResult center left right)
          (actualMol center left right) state (actualFuel center left right)) := by
  have shape : reportFromState (actualResult center left right) state =
      [1, 2, 7].filterMap
        (annotatedTetrahedralAssignment? (actualResult center left right)
          (actualMol center left right) state (actualFuel center left right)) ++ [] ++ [] ++ [] ++ [] := by
    cases center <;> cases left <;> cases right <;> rfl
  simpa only [List.append_nil] using shape

/-- Both arm outcomes read the actual full state at the actual parsed atoms. -/
theorem arm_outcomes (center left right : TetrahedralInputParity) :
    annotatedTetrahedralOutcome? (actualResult center left right) (actualMol center left right)
      (stateD center left right) (actualFuel center left right) 2 =
        some (.tetrahedral (descriptorOfParity left false)) ∧
    annotatedTetrahedralOutcome? (actualResult center left right) (actualMol center left right)
      (stateD center left right) (actualFuel center left right) 7 =
        some (.tetrahedral (descriptorOfParity right false)) := by
  cases center <;> cases left <;> cases right <;> decide +kernel

/-- Public-route admission and bypass guards, with no descriptor computation. -/
theorem intake_guards (center left right : TetrahedralInputParity) :
    (parsedRaw center left right).rule2MassesKnown? = true ∧
    (actualResult center left right).parsed.admissible? = true ∧
    (actualResult center left right).parsed.writtenNeighborExact? = true ∧
    (actualResult center left right).parsed.valenceOK? = true ∧
    (actualResult center left right).parsed.rule2MassesKnown? = true ∧
    (actualResult center left right).expandedStereochemicalAdmissible? = true ∧
    singleInvariantEarlyAssignment? (actualResult center left right) = none := by
  cases center <;> cases left <;> cases right <;> decide +kernel

/-- Every finite source spelling retains valid introduction metadata after normalization. -/
theorem introduction_guard (center left right : TetrahedralInputParity) :
    (actualResult center left right).parsed.introductionPredecessorsValid? = true := by
  cases center <;> cases left <;> cases right <;> decide +kernel

/-- Concrete certified record carrying the actual normalization result. -/
def actualCertified (center left right : TetrahedralInputParity) : CertifiedChemistryNormalizationResult :=
  { result := actualResult center left right
    admissible := ((actualResult center left right).parsed.admissible?_eq_true_iff).mp
      (intake_guards center left right).2.1
    writtenNeighborExact := ((actualResult center left right).parsed.writtenNeighborExact?_eq_true_iff).mp
      (intake_guards center left right).2.2.1
    valenceOK := ((actualResult center left right).parsed.valenceOK?_eq_true_iff).mp
      (intake_guards center left right).2.2.2.1
    rule2MassesKnown := ((actualResult center left right).parsed.rule2MassesKnown?_eq_true_iff).mp
      (intake_guards center left right).2.2.2.2.1 }

theorem actual_certify (center left right : TetrahedralInputParity) :
    (actualResult center left right).certify? = some (actualCertified center left right) := by
  simp only [ChemistryNormalizationResult.certify?, actualCertified,
    introduction_guard center left right, if_true,
    (intake_guards center left right).2.1,
    (intake_guards center left right).2.2.1,
    (intake_guards center left right).2.2.2.1,
    (intake_guards center left right).2.2.2.2.1, dite_true]

/-- Actual parser result; the empty fallback is unreachable. -/
theorem actual_parse (center left right : TetrahedralInputParity) :
    parseOpenSMILES (familyString center left right) = .ok (parsedRaw center left right) := by
  have h := parsedRaw_actual center left right
  unfold familyMol? at h
  cases hp : parseOpenSMILES (familyString center left right) with
  | error message => simp only [hp, reduceCtorEq] at h
  | ok mol =>
      have hm : mol = parsedRaw center left right := by
        simpa only [hp, Option.some.injEq] using h
      exact congrArg Except.ok hm

theorem actual_certified_intake (center left right : TetrahedralInputParity) :
    parseAndNormalizeOpenSMILESCertified (familyString center left right) =
      .ok (actualCertified center left right) := by
  unfold parseAndNormalizeOpenSMILESCertified parseAndNormalizeOpenSMILES
  rw [actual_parse]
  change (match (actualResult center left right).certify? with
    | some certified => Except.ok certified
    | none => Except.error "normalized molecule failed structural, valence, or Rule-2 mass admission") = _
  rw [actual_certify]

/-- The actual string route reaches the normalized analyzer, with every admission guard
proved and the single-center shortcut excluded. No report value is assumed. -/
theorem analyzeSmiles_route (center left right : TetrahedralInputParity) :
    analyzeSmiles (familyString center left right) =
      .ok (analyzeNormalized (actualResult center left right)) := by
  have certified := actual_certify center left right
  change (normalizeRawMolecule (parsedRaw center left right)).certify? =
    some (actualCertified center left right) at certified
  have guarded : (actualCertified center left right).result.expandedStereochemicalAdmissible? = true :=
    (intake_guards center left right).2.2.2.2.2.1
  have early : singleInvariantEarlyAssignment? (actualCertified center left right).result = none :=
    (intake_guards center left right).2.2.2.2.2.2
  simp only [analyzeSmiles, actual_parse, (intake_guards center left right).1,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, certified, guarded, early]
  rfl

/-- Actual public central outcome for member aaa; discovery is already factored out. -/
theorem center_outcome_aaa :
    annotatedTetrahedralOutcome? (actualResult .anticlockwise .anticlockwise .anticlockwise) (actualMol .anticlockwise .anticlockwise .anticlockwise)
      (stateD .anticlockwise .anticlockwise .anticlockwise) (actualFuel .anticlockwise .anticlockwise .anticlockwise) 1 =
        some (expectedCenterOutcome .anticlockwise .anticlockwise .anticlockwise) := by
  decide +kernel

/-- Actual public central outcome for member aac; discovery is already factored out. -/
theorem center_outcome_aac :
    annotatedTetrahedralOutcome? (actualResult .anticlockwise .anticlockwise .clockwise) (actualMol .anticlockwise .anticlockwise .clockwise)
      (stateD .anticlockwise .anticlockwise .clockwise) (actualFuel .anticlockwise .anticlockwise .clockwise) 1 =
        some (expectedCenterOutcome .anticlockwise .anticlockwise .clockwise) := by
  decide +kernel

/-- Actual public central outcome for member aca; discovery is already factored out. -/
theorem center_outcome_aca :
    annotatedTetrahedralOutcome? (actualResult .anticlockwise .clockwise .anticlockwise) (actualMol .anticlockwise .clockwise .anticlockwise)
      (stateD .anticlockwise .clockwise .anticlockwise) (actualFuel .anticlockwise .clockwise .anticlockwise) 1 =
        some (expectedCenterOutcome .anticlockwise .clockwise .anticlockwise) := by
  decide +kernel

/-- Actual public central outcome for member acc; discovery is already factored out. -/
theorem center_outcome_acc :
    annotatedTetrahedralOutcome? (actualResult .anticlockwise .clockwise .clockwise) (actualMol .anticlockwise .clockwise .clockwise)
      (stateD .anticlockwise .clockwise .clockwise) (actualFuel .anticlockwise .clockwise .clockwise) 1 =
        some (expectedCenterOutcome .anticlockwise .clockwise .clockwise) := by
  decide +kernel

/-- Actual public central outcome for member caa; discovery is already factored out. -/
theorem center_outcome_caa :
    annotatedTetrahedralOutcome? (actualResult .clockwise .anticlockwise .anticlockwise) (actualMol .clockwise .anticlockwise .anticlockwise)
      (stateD .clockwise .anticlockwise .anticlockwise) (actualFuel .clockwise .anticlockwise .anticlockwise) 1 =
        some (expectedCenterOutcome .clockwise .anticlockwise .anticlockwise) := by
  decide +kernel

/-- Actual public central outcome for member cac; discovery is already factored out. -/
theorem center_outcome_cac :
    annotatedTetrahedralOutcome? (actualResult .clockwise .anticlockwise .clockwise) (actualMol .clockwise .anticlockwise .clockwise)
      (stateD .clockwise .anticlockwise .clockwise) (actualFuel .clockwise .anticlockwise .clockwise) 1 =
        some (expectedCenterOutcome .clockwise .anticlockwise .clockwise) := by
  decide +kernel

/-- Actual public central outcome for member cca; discovery is already factored out. -/
theorem center_outcome_cca :
    annotatedTetrahedralOutcome? (actualResult .clockwise .clockwise .anticlockwise) (actualMol .clockwise .clockwise .anticlockwise)
      (stateD .clockwise .clockwise .anticlockwise) (actualFuel .clockwise .clockwise .anticlockwise) 1 =
        some (expectedCenterOutcome .clockwise .clockwise .anticlockwise) := by
  decide +kernel

/-- Actual public central outcome for member ccc; discovery is already factored out. -/
theorem center_outcome_ccc :
    annotatedTetrahedralOutcome? (actualResult .clockwise .clockwise .clockwise) (actualMol .clockwise .clockwise .clockwise)
      (stateD .clockwise .clockwise .clockwise) (actualFuel .clockwise .clockwise .clockwise) 1 =
        some (expectedCenterOutcome .clockwise .clockwise .clockwise) := by
  decide +kernel

theorem center_outcome (center left right : TetrahedralInputParity) :
    annotatedTetrahedralOutcome? (actualResult center left right) (actualMol center left right)
      (stateD center left right) (actualFuel center left right) 1 =
        some (expectedCenterOutcome center left right) := by
  cases center with
  | anticlockwise =>
      cases left with
      | anticlockwise =>
          cases right with
          | anticlockwise => exact center_outcome_aaa
          | clockwise => exact center_outcome_aac
      | clockwise =>
          cases right with
          | anticlockwise => exact center_outcome_aca
          | clockwise => exact center_outcome_acc
  | clockwise =>
      cases left with
      | anticlockwise =>
          cases right with
          | anticlockwise => exact center_outcome_caa
          | clockwise => exact center_outcome_cac
      | clockwise =>
          cases right with
          | anticlockwise => exact center_outcome_cca
          | clockwise => exact center_outcome_ccc

/-- Equal arms return the exact public refusal through the actual annotated fallback.
An absent central descriptor alone would not prove this result. -/
theorem equal_arms_refused (center arm : TetrahedralInputParity) :
    annotatedTetrahedralOutcome? (actualResult center arm arm) (actualMol center arm arm)
      (stateD center arm arm) (actualFuel center arm arm) 1 = some (.refused .notStereogenic) := by
  have h := center_outcome center arm arm
  cases arm <;> exact h

/-- Full exact report assembled from shape and outcome leaves; no discovery reduction. -/
theorem reportFromState_eq_expected (center left right : TetrahedralInputParity) :
    reportFromState (actualResult center left right) (stateD center left right) =
      expectedReport center left right := by
  rw [report_shape]
  simp only [List.filterMap_cons, List.filterMap_nil, annotatedTetrahedralAssignment?,
    center_outcome, (arm_outcomes center left right).1, (arm_outcomes center left right).2,
    Option.map_some, expectedReport]

end TetraStereo.UniversalProof.FramedParsedParityPublicReport

assert_kernel_only TetraStereo.UniversalProof.FramedParsedParityPublicReport.introduction_guard
assert_kernel_only TetraStereo.UniversalProof.FramedParsedParityPublicReport.actual_certify
