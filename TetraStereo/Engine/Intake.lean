import TetraStereo.OneCenter.CertificateExport

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section

/-!
  Certified chemistry intake decisions.

  This module is the production-facing intake spine.  It does not pretend Lean already owns every
  chemical parser.  Instead it gives the host engine a total decision boundary: an input either
  imports through a declared normalization policy and executable sanity checks, or it receives a
  checked refusal explaining why the molecule is not entering the proof kernel.
-/

/-! ### Host intake request algebra -/

/-- A host string import request.  Only formats with internal parsers can succeed directly. -/
structure StringImportRequest where
  format : ChemistryImportFormat
  input : String
  policy : ChemistryNormalizationPolicy := ChemistryNormalizationPolicy.openSMILESDefault
  aromaticCycles : List AromaticCycle := []
  deriving Repr

/-- Host import input: either a string surface or a predecoded bridge packet. -/
inductive ImportRequest where
  | string (request : StringImportRequest)
  | bridgePacket (packet : ExternalRawMoleculePacket)
  deriving Repr

/-- Certified refusal reasons at the engine intake boundary. -/
inductive IntakeRefusalReason where
  | importError (error : ChemistryImportError)
  | rawMoleculeNotAdmissible
  deriving DecidableEq, Repr

namespace IntakeRefusalReason

/-- Host-facing diagnostic label for intake refusal. -/
def label : IntakeRefusalReason → String
  | importError error => error.message
  | rawMoleculeNotAdmissible =>
      "raw molecule contains an invalid endpoint, self-loop, or duplicate unordered edge"

end IntakeRefusalReason

namespace ImportRequest

/-- Run the parser/bridge portion of an import request before executable sanity checks. -/
def import? : ImportRequest → Except ChemistryImportError ChemistryImportResult
  | string request =>
      importStringWithPolicy request.format request.input request.policy request.aromaticCycles
  | bridgePacket packet => Except.ok (importExternalRawMoleculePacket packet)

/-- Every successful import result records the same normalized parsed molecule obtained by the
core bond-kind normalizer from its raw molecule. -/
theorem import?_eq_ok_normalizedParsed
    (request : ImportRequest) (result : ChemistryImportResult)
    (h : request.import? = Except.ok result) :
    result.normalized.normalized.parsed = result.raw.normalizeUnspecifiedBonds := by
  cases request with
  | bridgePacket packet =>
      change Except.ok (importExternalRawMoleculePacket packet) = Except.ok result at h
      cases h
      rfl
  | string stringRequest =>
      change importStringWithPolicy stringRequest.format stringRequest.input
        stringRequest.policy stringRequest.aromaticCycles = Except.ok result at h
      unfold importStringWithPolicy at h
      cases hparse : parseImportStringAsRaw stringRequest.format stringRequest.input with
      | error error =>
          rw [hparse] at h
          contradiction
      | ok mol =>
          rw [hparse] at h
          cases h
          rfl

/-- Run the safe intake boundary: parse/bridge, then require the complete executable raw-molecule
admission contract.  This covers external packets as well as the internal parser. -/
def safeImport? (request : ImportRequest) :
    Except IntakeRefusalReason ChemistryImportResult :=
  match request.import? with
  | Except.error error => Except.error (IntakeRefusalReason.importError error)
  | Except.ok result =>
      if result.raw.admissible? then
        Except.ok result
      else
        Except.error IntakeRefusalReason.rawMoleculeNotAdmissible

end ImportRequest

/-! ### Intake certificate artifacts -/

/-- Claim that a host intake request safely imported a concrete normalized result. -/
def IntakeSuccessCertificateClaim (request : ImportRequest)
    (result : ChemistryImportResult) : Prop :=
  request.safeImport? = Except.ok result

/-- Claim that a host intake request was safely refused. -/
def IntakeRefusalCertificateClaim (request : ImportRequest)
    (reason : IntakeRefusalReason) : Prop :=
  request.safeImport? = Except.error reason


structure PublicIntakeTheoremPlan where
  imports : List String := ["TetraStereo.Engine.Intake"]
  namespacePath : List String := ["TetraStereo", "Generated"]
  theoremName : String
  statement : String
  proofTerm : String

namespace PublicIntakeTheoremPlan


def toTheoremExport (plan : PublicIntakeTheoremPlan) : LeanTheoremExport where
  imports := plan.imports
  namespacePath := plan.namespacePath
  theoremName := plan.theoremName
  statement := plan.statement
  proofTerm := plan.proofTerm

end PublicIntakeTheoremPlan

/-- Compile a checked safe intake success into a theorem artifact. -/
def compilePublicIntakeSuccess (plan : PublicIntakeTheoremPlan)
    (request : ImportRequest) (result : ChemistryImportResult)
    (h : IntakeSuccessCertificateClaim request result) :
    LeanCertificateArtifact where
  kind := LeanCertificateKind.importNormalization
  title := "Public engine intake success"
  theoremExport := plan.toTheoremExport
  source? := some result.source
  trust? := some result.trust
  boundary? := some result.normalized.boundary
  claim := IntakeSuccessCertificateClaim request result
  proof := h

/-- Compile a checked safe intake refusal into a theorem artifact. -/
def compilePublicIntakeRefusal (plan : PublicIntakeTheoremPlan)
    (request : ImportRequest) (reason : IntakeRefusalReason)
    (h : IntakeRefusalCertificateClaim request reason) :
    LeanCertificateArtifact where
  kind := LeanCertificateKind.importRefusal
  title := "Public engine intake refusal: " ++ reason.label
  theoremExport := plan.toTheoremExport
  claim := IntakeRefusalCertificateClaim request reason
  proof := h

/-! ### Total intake decisions -/

/-- A checked public intake success. -/
structure CertifiedIntakeSuccess (request : ImportRequest) where
  result : ChemistryImportResult
  success : IntakeSuccessCertificateClaim request result
  rawAdmissible : result.raw.Admissible
  normalizedAdmissible : result.normalized.normalized.parsed.Admissible
  theoremPlan : PublicIntakeTheoremPlan
  artifact : LeanCertificateArtifact
  artifact_eq : artifact = compilePublicIntakeSuccess theoremPlan request result success

/-- A checked public intake refusal. -/
structure CertifiedIntakeRefusal (request : ImportRequest) where
  reason : IntakeRefusalReason
  refusal : IntakeRefusalCertificateClaim request reason
  theoremPlan : PublicIntakeTheoremPlan
  artifact : LeanCertificateArtifact
  artifact_eq : artifact = compilePublicIntakeRefusal theoremPlan request reason refusal

namespace CertifiedIntakeSuccess

variable {request : ImportRequest}

/-- The success artifact is checked by construction. -/
theorem artifact_checked (success : CertifiedIntakeSuccess request) :
    success.artifact.claim := by
  rw [success.artifact_eq]
  exact
    (compilePublicIntakeSuccess success.theoremPlan request success.result success.success).checked

/-- Endpoint well-formedness remains available as a projection of the stronger intake contract. -/
theorem rawWellFormed (success : CertifiedIntakeSuccess request) :
    success.result.raw.WellFormed :=
  success.rawAdmissible.1

/-- Unordered bond-record uniqueness is retained from intake for exact hierarchy theorems. -/
theorem rawBondRecordsUnique (success : CertifiedIntakeSuccess request) :
    success.result.raw.BondRecordsUnique :=
  success.rawAdmissible.2

/-- The normalized molecule actually consumed by the official engine is endpoint-well-formed. -/
theorem normalizedWellFormed (success : CertifiedIntakeSuccess request) :
    success.result.normalized.normalized.parsed.WellFormed :=
  success.normalizedAdmissible.1

/-- The normalized molecule actually consumed by the official engine has unique raw edge records. -/
theorem normalizedBondRecordsUnique (success : CertifiedIntakeSuccess request) :
    success.result.normalized.normalized.parsed.BondRecordsUnique :=
  success.normalizedAdmissible.2

end CertifiedIntakeSuccess

namespace CertifiedIntakeRefusal

variable {request : ImportRequest}

/-- The refusal artifact is checked by construction. -/
theorem artifact_checked (refusal : CertifiedIntakeRefusal request) :
    refusal.artifact.claim := by
  rw [refusal.artifact_eq]
  exact
    (compilePublicIntakeRefusal refusal.theoremPlan request refusal.reason refusal.refusal).checked

end CertifiedIntakeRefusal

/-- Total checked decision at the chemistry intake boundary. -/
inductive IntakeDecision (request : ImportRequest) where
  | imported (success : CertifiedIntakeSuccess request)
  | refused (refusal : CertifiedIntakeRefusal request)

namespace IntakeDecision

variable {request : ImportRequest}

/-- Optional normalized import result from a total intake decision. -/
def result? (decision : IntakeDecision request) : Option ChemistryImportResult :=
  match decision with
  | imported success => some success.result
  | refused _ => none

/-- Optional refusal reason from a total intake decision. -/
def reason? (decision : IntakeDecision request) : Option IntakeRefusalReason :=
  match decision with
  | imported _ => none
  | refused refusal => some refusal.reason

/-- The certificate claim carried by this intake decision. -/
def artifactClaim (decision : IntakeDecision request) : Prop :=
  match decision with
  | imported success => success.artifact.claim
  | refused refusal => refusal.artifact.claim

/-- Every total intake decision carries a checked theorem artifact. -/
theorem artifact_checked (decision : IntakeDecision request) : decision.artifactClaim := by
  cases decision with
  | imported success => exact success.artifact_checked
  | refused refusal => exact refusal.artifact_checked

end IntakeDecision

/-- Run the total checked chemistry intake decision. -/
def decideIntake (request : ImportRequest) (plan : PublicIntakeTheoremPlan) :
    IntakeDecision request :=
  match h : request.import? with
  | Except.error error =>
      let reason := IntakeRefusalReason.importError error
      let refusal : IntakeRefusalCertificateClaim request reason := by
        simp [IntakeRefusalCertificateClaim, ImportRequest.safeImport?, h, reason]
      IntakeDecision.refused
        { reason := reason
          refusal := refusal
          artifact := compilePublicIntakeRefusal plan request reason refusal
          artifact_eq := rfl
          theoremPlan := plan }
  | Except.ok result =>
      if hadmissible : result.raw.admissible? then
        let rawAdmissible : result.raw.Admissible :=
          (RawMolecule.admissible?_eq_true_iff result.raw).1 hadmissible
        let normalizedAdmissible : result.normalized.normalized.parsed.Admissible := by
          rw [request.import?_eq_ok_normalizedParsed result h]
          exact result.raw.normalizeUnspecifiedBonds_admissible rawAdmissible
        let success : IntakeSuccessCertificateClaim request result := by
          simp [IntakeSuccessCertificateClaim, ImportRequest.safeImport?, h, hadmissible]
        IntakeDecision.imported
          { result := result
            success := success
            rawAdmissible := rawAdmissible
            normalizedAdmissible := normalizedAdmissible
            theoremPlan := plan
            artifact := compilePublicIntakeSuccess plan request result success
            artifact_eq := rfl }
      else
        let reason := IntakeRefusalReason.rawMoleculeNotAdmissible
        let refusal : IntakeRefusalCertificateClaim request reason := by
          simp [IntakeRefusalCertificateClaim, ImportRequest.safeImport?, h, hadmissible, reason]
        IntakeDecision.refused
          { reason := reason
            refusal := refusal
            theoremPlan := plan
            artifact := compilePublicIntakeRefusal plan request reason refusal
            artifact_eq := rfl }

end
end Engine
end TetraStereo
