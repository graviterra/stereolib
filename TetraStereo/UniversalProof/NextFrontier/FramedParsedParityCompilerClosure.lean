import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFamily
import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityPublicReport
import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFinishCompletion
import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.Engine.Claims
import TetraStereo.Engine.CertificateExporter

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000










namespace TetraStereo.UniversalProof.FramedParsedParityCompilerClosure

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.Engine
open TetraStereo.UniversalProof.FramedParsedParityFamily

/-! ## Actual pipeline definitions (real definitions, not candidate values) -/

/-- Actual raw authoritative occurrence fact through the maintained single wrapper. -/
def repairedFact? (center leftArm rightArm : TetrahedralInputParity) : Option RawDescriptorFact :=
  match familyMol? center leftArm rightArm with
  | some mol => tetrahedralOccurrenceFactAuthoritative? mol (analysisFuel mol) 1
  | none => none

/-- Actual certified intake of the family string. -/
def certifiedFamily? (center leftArm rightArm : TetrahedralInputParity) :
    Option CertifiedChemistryNormalizationResult :=
  match parseAndNormalizeOpenSMILESCertified (familyString center leftArm rightArm) with
  | .ok certified => some certified
  | .error _ => none

/-- Actual public report rows from the certified certificate. -/
def reportRows? (center leftArm rightArm : TetrahedralInputParity) : Option (List StereoAssignment) :=
  (certifiedFamily? center leftArm rightArm).map fun certified => analyzeNormalized certified.result

/-- Actual `analyzeSmiles` public route, fail-closed to `none`. -/
def analyzeSmiles? (center leftArm rightArm : TetrahedralInputParity) :
    Option (List StereoAssignment) :=
  match analyzeSmiles (familyString center leftArm rightArm) with
  | .ok rows => some rows
  | .error _ => none

/-- Core comparison tuple of a raw descriptor fact. -/
def factCore (fact : RawDescriptorFact) : Nat × RS × Bool × List Nat :=
  (fact.atom, fact.descriptor, fact.uppercase, fact.priorityPositions)

/-- Core comparison tuple of an occurrence auxiliary fact. -/
def occurrenceCore (fact : OccurrenceAuxFact) : Nat × RS × Bool × List Nat :=
  (fact.atom, fact.descriptor, fact.uppercase, fact.priorityPositions)

/-- No *assigned* tetrahedral row at the central atom 1 (absent or explicitly refused). -/
def centralAssigned (rows : List StereoAssignment) : Prop :=
  ∃ row ∈ rows, row.unit = StereoUnit.tetrahedral 1 ∧ row.outcome.assigned = true

instance centralAssignedDecidable (rows : List StereoAssignment) : Decidable (centralAssigned rows) :=
  inferInstanceAs (Decidable (∃ row ∈ rows,
    row.unit = StereoUnit.tetrahedral 1 ∧ row.outcome.assigned = true))

/-- The expected assigned central report row for an opposite-arm member. -/
def expectedCentralRow (center leftArm : TetrahedralInputParity) : StereoAssignment :=
  { unit := StereoUnit.tetrahedral 1
    outcome :=
      StereoOutcome.pseudoTetrahedral
        (match descriptorOfParity center (permutationIsEven (expectedPositions leftArm)) with
         | .R => .r
         | .S => .s) }

/-- Complete report, including the exact equal-arm refusal and both ordinary arm rows. -/
def expectedReport (center left right : TetrahedralInputParity) : List StereoAssignment :=
  FramedParsedParityPublicReport.expectedReport center left right

/-- Actual discovery is supplied by the all-eight finish theorem, not an input premise. -/
theorem normalized_report_eq_expected (center left right : TetrahedralInputParity) :
    analyzeNormalized (FramedParsedParitySchedulerCenter.actualResult center left right) =
      expectedReport center left right := by
  have discovered := FramedParsedParityFinishCompletion.actual_descriptors center left right
  have report := FramedParsedParityPublicReport.analyzeNormalized_of_discovery
    (FramedParsedParitySchedulerCenter.actualResult center left right)
    (FramedParsedParitySchedulerLeaves.stateD center left right)
    (by simpa only [FramedParsedParitySchedulerCenter.actualMol,
      FramedParsedParitySchedulerCenter.actualFuel] using discovered)
  exact report.trans (FramedParsedParityPublicReport.reportFromState_eq_expected center left right)

/-- Full certified report equality, derived without evaluating discovery. -/
theorem reportRows_eq_expected (center left right : TetrahedralInputParity) :
    reportRows? center left right = some (expectedReport center left right) := by
  unfold reportRows? certifiedFamily?
  rw [FramedParsedParityPublicReport.actual_certified_intake]
  change some (analyzeNormalized (FramedParsedParitySchedulerCenter.actualResult center left right)) = _
  rw [normalized_report_eq_expected]

/-- Full string-route equality, including success and exact refusal outcomes. -/
theorem analyzeRows_eq_expected (center left right : TetrahedralInputParity) :
    analyzeSmiles? center left right = some (expectedReport center left right) := by
  unfold analyzeSmiles?
  rw [FramedParsedParityPublicReport.analyzeSmiles_route, normalized_report_eq_expected]

/-! ## New actual normalized input / report bridge (candidate kernel computations) -/

/-- Actual raw-wrapper core equals the independently derived candidate core: equal arms are `none`,
opposite arms carry the candidate descriptor/uppercase/priority positions, atom 1. -/
theorem repairedFact_core (center leftArm rightArm : TetrahedralInputParity) :
    (repairedFact? center leftArm rightArm).map factCore =
      (expectedFact? center leftArm rightArm).map occurrenceCore := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-- Equal written arm parity: the actual raw wrapper refuses the central fact. -/
theorem repairedFact_same_none (center arm : TetrahedralInputParity) :
    (repairedFact? center arm arm).isSome = false := by
  cases center <;> cases arm <;> decide +kernel

/-- Opposite written arm parity: the actual raw wrapper yields a fact (no vacuous `none`). -/
theorem repairedFact_opposite_some (center leftArm rightArm : TetrahedralInputParity)
    (opposite : leftArm ≠ rightArm) :
    (repairedFact? center leftArm rightArm).isSome = true := by
  cases center <;> cases leftArm <;> cases rightArm <;>
    first | exact absurd rfl opposite | decide +kernel

/-- Actual certified intake succeeds for every member. -/
theorem certified_success (center leftArm rightArm : TetrahedralInputParity) :
    (certifiedFamily? center leftArm rightArm).isSome = true := by
  unfold certifiedFamily?
  rw [FramedParsedParityPublicReport.actual_certified_intake]
  rfl

/-- The public route succeeds for every member, including central nonassignment cases. -/
theorem analyze_success (center leftArm rightArm : TetrahedralInputParity) :
    (analyzeSmiles? center leftArm rightArm).isSome = true := by
  rw [analyzeRows_eq_expected]
  rfl

/-- The certified and string routes return the same full public report. -/
theorem public_reports_agree (center leftArm rightArm : TetrahedralInputParity) :
    reportRows? center leftArm rightArm = analyzeSmiles? center leftArm rightArm := by
  rw [reportRows_eq_expected, analyzeRows_eq_expected]

/-- The certified intake preserves the 11-atom topology and the three written parities. -/
theorem certified_structural (center leftArm rightArm : TetrahedralInputParity) :
    (certifiedFamily? center leftArm rightArm).map (fun certified =>
      (certified.result.parsed.atomCount,
        (certified.result.parsed.atomAt? 1).bind (fun spec => spec.tetrahedral?),
        (certified.result.parsed.atomAt? 2).bind (fun spec => spec.tetrahedral?),
        (certified.result.parsed.atomAt? 7).bind (fun spec => spec.tetrahedral?))) =
      some (11, some center, some leftArm, some rightArm) := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-- Opposite arms: the actual public report carries the expected assigned central row. -/
theorem report_central_assigned_opposite (center leftArm rightArm : TetrahedralInputParity)
    (opposite : leftArm ≠ rightArm) :
    expectedCentralRow center leftArm ∈ (reportRows? center leftArm rightArm).getD [] := by
  rw [reportRows_eq_expected]
  cases center <;> cases leftArm <;> cases rightArm <;>
    first | exact absurd rfl opposite | decide +kernel

/-- Opposite arms: the actual `analyzeSmiles` route carries the expected assigned central row. -/
theorem analyze_central_assigned_opposite (center leftArm rightArm : TetrahedralInputParity)
    (opposite : leftArm ≠ rightArm) :
    expectedCentralRow center leftArm ∈ (analyzeSmiles? center leftArm rightArm).getD [] := by
  rw [← public_reports_agree]
  exact report_central_assigned_opposite center leftArm rightArm opposite

/-- Equal arms: the actual public report has no assigned central row (nonassignment). -/
theorem report_central_nonassigned_same (center arm : TetrahedralInputParity) :
    ¬ centralAssigned ((reportRows? center arm arm).getD []) := by
  rw [reportRows_eq_expected]
  cases center <;> cases arm <;> decide +kernel

/-- Equal arms: the actual `analyzeSmiles` route has no assigned central row (nonassignment). -/
theorem analyze_central_nonassigned_same (center arm : TetrahedralInputParity) :
    ¬ centralAssigned ((analyzeSmiles? center arm arm).getD []) := by
  rw [← public_reports_agree]
  exact report_central_nonassigned_same center arm

/-! ## Whole-family executable claim -/

/-- Whole-family claim over all eight members: accepted actual runtime truths plus the new actual
certified-intake and public-report bridge. No desired output, comparator or model field is assumed.
Equal-arm nonassignment is stated for the report route with the two arm parameters identified. -/
def FamilyClaim : Prop := ∀ center leftArm rightArm : TetrahedralInputParity,
  (parseOpenSMILES (familyString center leftArm rightArm)).isOk = true ∧
  (familyMol? center leftArm rightArm).map (fun mol =>
      (mol.atomCount,
        (mol.atomAt? 1).bind (fun spec => spec.tetrahedral?),
        (mol.atomAt? 2).bind (fun spec => spec.tetrahedral?),
        (mol.atomAt? 7).bind (fun spec => spec.tetrahedral?))) =
    some (11, some center, some leftArm, some rightArm) ∧
  (auxiliaryState? center leftArm rightArm false).isSome = true ∧
  (auxiliaryState? center leftArm rightArm true).isSome = true ∧
  centralFact? center leftArm rightArm true = expectedFact? center leftArm rightArm ∧
  armPairDecision? center leftArm rightArm true = expectedArmDecision? leftArm rightArm ∧
  (repairedFact? center leftArm rightArm).map factCore =
    (expectedFact? center leftArm rightArm).map occurrenceCore ∧
  (certifiedFamily? center leftArm rightArm).isSome = true ∧
  (certifiedFamily? center leftArm rightArm).map (fun certified =>
      (certified.result.parsed.atomCount,
        (certified.result.parsed.atomAt? 1).bind (fun spec => spec.tetrahedral?),
        (certified.result.parsed.atomAt? 2).bind (fun spec => spec.tetrahedral?),
        (certified.result.parsed.atomAt? 7).bind (fun spec => spec.tetrahedral?))) =
    some (11, some center, some leftArm, some rightArm) ∧
  (leftArm ≠ rightArm →
    expectedCentralRow center leftArm ∈ (reportRows? center leftArm rightArm).getD [] ∧
    expectedCentralRow center leftArm ∈ (analyzeSmiles? center leftArm rightArm).getD []) ∧
  (leftArm = rightArm →
    ¬ centralAssigned ((reportRows? center leftArm leftArm).getD []) ∧
    ¬ centralAssigned ((analyzeSmiles? center leftArm leftArm).getD [])) ∧
  (analyzeSmiles? center leftArm rightArm).isSome = true ∧
  reportRows? center leftArm rightArm = analyzeSmiles? center leftArm rightArm

theorem familyClaim_holds : FamilyClaim := by
  intro center leftArm rightArm
  refine ⟨family_parse_success center leftArm rightArm,
    family_structural center leftArm rightArm,
    auxiliary_fast_success center leftArm rightArm,
    auxiliary_authoritative_success center leftArm rightArm,
    centralAuthoritative_eq_expected center leftArm rightArm,
    armAuthoritative_eq_expected center leftArm rightArm,
    repairedFact_core center leftArm rightArm,
    certified_success center leftArm rightArm,
    certified_structural center leftArm rightArm, ?_, ?_,
    analyze_success center leftArm rightArm, public_reports_agree center leftArm rightArm⟩
  · intro h
    exact ⟨report_central_assigned_opposite center leftArm rightArm h,
      analyze_central_assigned_opposite center leftArm rightArm h⟩
  · intro h
    cases h
    exact ⟨report_central_nonassigned_same center leftArm,
      analyze_central_nonassigned_same center leftArm⟩

/-! ## Actual compiler / export route (as in the frozen second-sphere closure) -/



def fixedPlan : PublicClaimTheoremPlan where
  imports := ["TetraStereo.UniversalProof.NextFrontier.FramedParsedParityCompilerClosure",
    "TetraStereo.KernelOnly"]
  namespacePath := ["TetraStereo", "Generated", "FramedParsedParityCompilerExport"]
  theoremName := "framedParsedParityFamilyCorrect"
  statement := "TetraStereo.UniversalProof.FramedParsedParityCompilerClosure.FamilyClaim"
  proofTerm := "  exact TetraStereo.UniversalProof.FramedParsedParityCompilerClosure.compiledArtifact_checked\n\nexample : TetraStereo.UniversalProof.FramedParsedParityCompilerClosure.compiledArtifact.claim :=\n  framedParsedParityFamilyCorrect\n\nassert_kernel_only TetraStereo.Generated.FramedParsedParityCompilerExport.framedParsedParityFamilyCorrect"

/-- The actual production compiler, carrying the meaningful whole-family claim. -/
def compiledArtifact : LeanCertificateArtifact :=
  compilePublicClaim fixedPlan .multiCenterRelation
    "Framed parsed 8-member parity family: actual intake, public report and maintained raw occurrence wrapper"
    FamilyClaim familyClaim_holds

theorem compiledArtifact_claim : compiledArtifact.claim = FamilyClaim := rfl

theorem compiledArtifact_checked : compiledArtifact.claim := compiledArtifact.checked

def sourceEntry : CertificateSourceEntry where
  key := "framed-parsed-parity-family-compiler-export"
  description := "Eight-member parsed parity family: actual certified intake, report and raw occurrence wrapper"
  fileName := "FramedParsedParityCompilerExport.lean"
  source := compiledArtifact.source

theorem sourceEntry_actual_compiler_source : sourceEntry.source = compiledArtifact.source := rfl

def writeFamilyExport (outputDirectory : String) : IO System.FilePath :=
  sourceEntry.writeSource outputDirectory

theorem writeFamilyExport_emits_renderer (outputDirectory : String) :
    writeFamilyExport outputDirectory = (do
      IO.FS.createDirAll (System.FilePath.mk outputDirectory)
      let path := sourceEntry.outputPath outputDirectory
      IO.FS.writeFile path sourceEntry.fileSource
      pure path) := rfl

theorem inhabited_compiler_family_claim :
    ∃ artifact : LeanCertificateArtifact, artifact = compiledArtifact ∧
      artifact.claim = FamilyClaim ∧ artifact.claim ∧ artifact.source = sourceEntry.source :=
  ⟨compiledArtifact, rfl, compiledArtifact_claim, compiledArtifact_checked, rfl⟩

/-! ## Minimal source premises and open gates -/

/-- Minimal independent source premises this closure still needs from Root. -/
def requiredSourcePremises : List String :=
  [ "Root installs the current frozen FramedParsedParityFamily source at the logical accepted import",
    "independent SAME-source scheduled CIP model for this topology (SOURCE_MODEL_BRIDGE) — OPEN",
    "human scientific review (HUMAN) — OPEN",
    "external source-authority approval (EXTERNAL) — OPEN" ]

#check FamilyClaim
#check familyClaim_holds
#check compiledArtifact_checked
#check repairedFact_core
#check certified_structural

end TetraStereo.UniversalProof.FramedParsedParityCompilerClosure
