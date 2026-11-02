import TetraStereo.Engine.CertificateExporter
import TetraStereo.Engine.Intake
import TetraStereo.Engine.OfficialStereoTransaction
import TetraStereo.OneCenter.MultiCenterDetection

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section











/-- Failure modes for automatic official-stereo request construction. -/
inductive OfficialStereoBuildFailure where
  | centerNotDetected
  deriving DecidableEq, Repr

namespace OfficialStereoBuildFailure

/-- Human-readable diagnostic for request-builder failures. -/
def label : OfficialStereoBuildFailure → String
  | centerNotDetected =>
      "selected atom is not an automatically detected tetrahedral center"

end OfficialStereoBuildFailure






structure OfficialStereoRequestBlueprint where
  normalized : ChemistryNormalizationResult
  annotations : IndexedNoncenterStereoAnnotations := {}
  centerAtom : Fin normalized.parsed.atomCount
  left : Fin 4
  right : Fin 4
  profile : DescriptorSourcePolicyProfile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel : ℕ := normalized.parsed.atomCount + 1
  scheduleFuel : ℕ := 0
  branchFuel : ℕ := normalized.parsed.atomCount + 1
  theoremPlan : PublicOfficialStereoTheoremPlan

namespace OfficialStereoRequestBlueprint

/-- Proof-facing molecular graph derived from the normalized molecule. -/
def graph (blueprint : OfficialStereoRequestBlueprint) :
    MoleculeGraph (Fin blueprint.normalized.parsed.atomCount) :=
  blueprint.normalized.graph

/-- Automatically detected multi-center molecule derived from the normalized graph. -/
def molecule (blueprint : OfficialStereoRequestBlueprint) :
    MultiCenterMolecule (Fin blueprint.normalized.parsed.atomCount) :=
  blueprint.graph.detectedMultiCenterMolecule

/-- The selected center, when the normalized graph detects it as tetrahedral. -/
def center? (blueprint : OfficialStereoRequestBlueprint) :
    Option blueprint.molecule.Center :=
  if hcenter : blueprint.centerAtom ∈ blueprint.molecule.centers then
    some ⟨blueprint.centerAtom, hcenter⟩
  else
    none

/-- Build the proof-facing official-stereo request from this host-facing blueprint. -/
def toOfficialStereoRequest (blueprint : OfficialStereoRequestBlueprint) :
    Except OfficialStereoBuildFailure OfficialStereoRequest :=
  match blueprint.center? with
  | some center =>
      Except.ok
        { normalized := blueprint.normalized
          annotations := blueprint.annotations
          molecule := blueprint.molecule
          profile := blueprint.profile
          graphFuel := blueprint.graphFuel
          scheduleFuel := blueprint.scheduleFuel
          branchFuel := blueprint.branchFuel
          center := center
          localMolecule := blueprint.molecule.toOneCenterMolecule center
          left := blueprint.left
          right := blueprint.right
          theoremPlan := blueprint.theoremPlan }
  | none => Except.error OfficialStereoBuildFailure.centerNotDetected

end OfficialStereoRequestBlueprint

/-- Host-facing official-stereo request spec whose normalized molecule comes from a checked intake
success. -/
structure IntakeOfficialStereoSpec (request : ImportRequest)
    (success : CertifiedIntakeSuccess request) where
  annotations : IndexedNoncenterStereoAnnotations := {}
  centerAtom : Fin success.result.normalized.normalized.parsed.atomCount
  left : Fin 4
  right : Fin 4
  profile : DescriptorSourcePolicyProfile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel : ℕ := success.result.normalized.normalized.parsed.atomCount + 1
  scheduleFuel : ℕ := 0
  branchFuel : ℕ := success.result.normalized.normalized.parsed.atomCount + 1
  theoremPlan : PublicOfficialStereoTheoremPlan

namespace IntakeOfficialStereoSpec

/-- Convert a checked intake success plus host query spec to a normalized request blueprint. -/
def toBlueprint {request : ImportRequest} {success : CertifiedIntakeSuccess request}
    (spec : IntakeOfficialStereoSpec request success) :
    OfficialStereoRequestBlueprint where
  normalized := success.result.normalized.normalized
  annotations := spec.annotations
  centerAtom := spec.centerAtom
  left := spec.left
  right := spec.right
  profile := spec.profile
  graphFuel := spec.graphFuel
  scheduleFuel := spec.scheduleFuel
  branchFuel := spec.branchFuel
  theoremPlan := spec.theoremPlan

end IntakeOfficialStereoSpec

/-- Build an official-stereo request from a checked intake success. -/
def buildOfficialStereoRequestFromIntakeSuccess {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (spec : IntakeOfficialStereoSpec request success) :
    Except OfficialStereoBuildFailure OfficialStereoRequest :=
  spec.toBlueprint.toOfficialStereoRequest

/-- Host-facing metadata for exporting a generated official-stereo transaction certificate.

This keeps certificate naming and theorem rendering out of the chemistry query itself.  A host can
use this compact record instead of manually constructing a `PublicOfficialStereoTheoremPlan` and
the final `CertificateExportEntry`. -/
structure OfficialStereoExportSpec where
  key : String
  description : String
  fileName : String
  imports : List String := ["TetraStereo.Engine.OfficialStereoBuilder"]
  namespacePath : List String := ["TetraStereo", "Generated"]
  theoremName : String
  requestExpr : String
  proofTerm : String

namespace OfficialStereoExportSpec


def theoremPlan (spec : OfficialStereoExportSpec) : PublicOfficialStereoTheoremPlan where
  imports := spec.imports
  namespacePath := spec.namespacePath
  theoremName := spec.theoremName
  requestExpr := spec.requestExpr
  proofTerm := spec.proofTerm

end OfficialStereoExportSpec

/-- Compact host-facing official-stereo query whose normalized molecule comes from a checked intake
success.  The host supplies the chemical question and export metadata; Lean derives the molecular
graph, detected centers, proof-facing request, total decision, and export entry. -/
structure IntakeOfficialStereoQuery (request : ImportRequest)
    (success : CertifiedIntakeSuccess request) where
  annotations : IndexedNoncenterStereoAnnotations := {}
  centerAtom : Fin success.result.normalized.normalized.parsed.atomCount
  left : Fin 4
  right : Fin 4
  profile : DescriptorSourcePolicyProfile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel : ℕ := success.result.normalized.normalized.parsed.atomCount + 1
  scheduleFuel : ℕ := 0
  branchFuel : ℕ := success.result.normalized.normalized.parsed.atomCount + 1
  exportSpec : OfficialStereoExportSpec

namespace IntakeOfficialStereoQuery

/-- Expand a compact host query into the lower-level checked-intake official-stereo spec. -/
def toSpec {request : ImportRequest} {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success) :
    IntakeOfficialStereoSpec request success where
  annotations := query.annotations
  centerAtom := query.centerAtom
  left := query.left
  right := query.right
  profile := query.profile
  graphFuel := query.graphFuel
  scheduleFuel := query.scheduleFuel
  branchFuel := query.branchFuel
  theoremPlan := query.exportSpec.theoremPlan

end IntakeOfficialStereoQuery

/-- Source-only specification for a generated host Lean module wrapping a compact official-stereo
query.  The executable CLI can use this without evaluating the noncomputable query: it renders a
theorem that imports a host module, requires a concrete build proof, and applies the generic
checked-built-query theorem. -/
structure OfficialStereoHostQuerySourceSpec where
  key : String
  description : String
  fileName : String
  imports : List String
  options : List String := ["set_option maxHeartbeats 1000000"]
  namespacePath : List String := ["TetraStereo", "Generated"]
  theoremName : String
  queryExpr : String
  buildProofExpr : String

namespace OfficialStereoHostQuerySourceSpec

/-- The proposition rendered for a generated compact-query certificate source file. -/
def checkedStatement (spec : OfficialStereoHostQuerySourceSpec) : String :=
  "TetraStereo.Engine.OfficialStereoHostQueryClaim " ++ spec.queryExpr

/-- The proof term rendered for a generated compact-query certificate source file. -/
def checkedProofTerm (spec : OfficialStereoHostQuerySourceSpec) : String :=
  "  exact TetraStereo.Engine.officialStereoHostQueryClaim_checked " ++
    spec.queryExpr ++ " " ++ spec.buildProofExpr

/-- Render this source-only host query as a Lean theorem export. -/
def theoremExport (spec : OfficialStereoHostQuerySourceSpec) : LeanTheoremExport where
  imports := spec.imports
  options := spec.options
  namespacePath := spec.namespacePath
  theoremName := spec.theoremName
  statement := spec.checkedStatement
  proofTerm := spec.checkedProofTerm

/-- Render this source-only host query as an executable certificate source entry. -/
def sourceEntry (spec : OfficialStereoHostQuerySourceSpec) : CertificateSourceEntry where
  key := spec.key
  description := spec.description
  fileName := spec.fileName
  source := spec.theoremExport.source

end OfficialStereoHostQuerySourceSpec

namespace OfficialStereoExportSpec

/-- Derive a source-only generated host-query module spec from export metadata.

This is the registry-facing companion to `IntakeOfficialStereoQuery`: the host still names the Lean
query expression, build proof, and generated theorem, while the key, file name, imports, namespace,
and default description come from the same export spec used by the checked transaction. -/
def hostQuerySourceSpec (spec : OfficialStereoExportSpec)
    (queryExpr buildProofExpr theoremName : String) :
    OfficialStereoHostQuerySourceSpec where
  key := spec.key
  description := "checked " ++ spec.description
  fileName := spec.fileName
  imports := spec.imports
  namespacePath := spec.namespacePath
  theoremName := theoremName
  queryExpr := queryExpr
  buildProofExpr := buildProofExpr

end OfficialStereoExportSpec

namespace IntakeOfficialStereoQuery

/-- Derive a generated source-registry spec directly from a compact host query. -/
def hostQuerySourceSpec {request : ImportRequest} {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success)
    (queryExpr buildProofExpr theoremName : String) :
    OfficialStereoHostQuerySourceSpec :=
  query.exportSpec.hostQuerySourceSpec queryExpr buildProofExpr theoremName

/-- Derive a generated source-registry entry directly from a compact host query. -/
def hostQuerySourceEntry {request : ImportRequest} {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success)
    (queryExpr buildProofExpr theoremName : String) :
    CertificateSourceEntry :=
  (query.hostQuerySourceSpec queryExpr buildProofExpr theoremName).sourceEntry

end IntakeOfficialStereoQuery

namespace OfficialStereoDecision

/-- The theorem artifact carried by a total official-stereo decision. -/
def artifact {request : OfficialStereoRequest} :
    OfficialStereoDecision request → LeanCertificateArtifact
  | certified certificate => certificate.artifact
  | refused refusal => refusal.artifact

/-- The artifact exposed by a total official-stereo decision is checked. -/
theorem artifact_claim {request : OfficialStereoRequest}
    (decision : OfficialStereoDecision request) : decision.artifact.claim := by
  cases decision with
  | certified certificate => exact certificate.artifact_checked
  | refused refusal => exact refusal.artifact_checked

end OfficialStereoDecision

/-- Turn a public official-stereo decision into a named certificate-export entry. -/
def certificateExportEntryOfOfficialStereoDecision {request : OfficialStereoRequest}
    (key description fileName : String) (decision : OfficialStereoDecision request) :
    CertificateExportEntry where
  key := key
  description := description
  fileName := fileName
  source := decision.artifact.source
  artifact := decision.artifact

/-- A fully prepared official-stereo transaction: request, total decision, and export entry. -/
structure PreparedOfficialStereoTransaction where
  request : OfficialStereoRequest
  decision : OfficialStereoDecision request
  key : String
  description : String
  fileName : String
  exportEntry : CertificateExportEntry
  exportEntry_eq :
    exportEntry =
      certificateExportEntryOfOfficialStereoDecision key description fileName decision

namespace PreparedOfficialStereoTransaction

/-- The prepared export entry carries a checked theorem artifact. -/
theorem exportEntry_checked (prepared : PreparedOfficialStereoTransaction) :
    prepared.exportEntry.artifact.claim := by
  rw [prepared.exportEntry_eq]
  exact prepared.decision.artifact_claim

/-- The executable source-entry view of a prepared transaction. -/
def sourceEntry (prepared : PreparedOfficialStereoTransaction) : CertificateSourceEntry :=
  prepared.exportEntry.toSourceEntry

end PreparedOfficialStereoTransaction

/-- Build, decide, and package one official-stereo transaction from a normalized blueprint. -/
def prepareOfficialStereoTransaction (blueprint : OfficialStereoRequestBlueprint)
    (key description fileName : String) :
    Except OfficialStereoBuildFailure PreparedOfficialStereoTransaction :=
  match blueprint.toOfficialStereoRequest with
  | Except.error failure => Except.error failure
  | Except.ok request =>
      let decision := decideOfficialStereo request
      let exportEntry :=
        certificateExportEntryOfOfficialStereoDecision key description fileName decision
      Except.ok
        { request := request
          decision := decision
          key := key
          description := description
          fileName := fileName
          exportEntry := exportEntry
          exportEntry_eq := rfl }

/-- Build, decide, and package one official-stereo transaction from a checked intake success. -/
def prepareOfficialStereoTransactionFromIntakeSuccess {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (spec : IntakeOfficialStereoSpec request success)
    (key description fileName : String) :
    Except OfficialStereoBuildFailure PreparedOfficialStereoTransaction :=
  prepareOfficialStereoTransaction spec.toBlueprint key description fileName

/-- Build, decide, and package a prepared official-stereo transaction from a compact host query. -/
def prepareOfficialStereoTransactionFromIntakeQuery {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
  (query : IntakeOfficialStereoQuery request success) :
    Except OfficialStereoBuildFailure PreparedOfficialStereoTransaction :=
  prepareOfficialStereoTransactionFromIntakeSuccess query.toSpec
    query.exportSpec.key query.exportSpec.description query.exportSpec.fileName

/-- Total checked-on-success proposition for compact official-stereo host queries.

This is useful as an internal totality lemma, but it is intentionally weaker than the generated
host-facing certificate claim: failed builds make this proposition true. -/
@[irreducible] def OfficialStereoHostQueryCheckedClaim {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success) : Prop :=
  match prepareOfficialStereoTransactionFromIntakeQuery query with
  | Except.ok prepared => prepared.exportEntry.artifact.claim
  | Except.error _ => True

/-- Predicate recording that a compact host query produced a prepared transaction. -/
@[irreducible] def OfficialStereoHostQueryBuilds {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success) : Prop :=
  match prepareOfficialStereoTransactionFromIntakeQuery query with
  | Except.ok _ => True
  | Except.error _ => False

/-- Strong generated-certificate proposition for compact official-stereo host queries.

The definition is intentionally irreducible at generated-source boundaries: concrete host queries
can be expensive to normalize, so generated theorem files should check the named claim rather than
unfolding the full prepared transaction while elaborating a theorem statement. Unlike
`OfficialStereoHostQueryCheckedClaim`, this claim is false unless the query actually builds. -/
@[irreducible] def OfficialStereoHostQueryClaim {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success) : Prop :=
  ∃ prepared,
    prepareOfficialStereoTransactionFromIntakeQuery query = Except.ok prepared ∧
      prepared.exportEntry.artifact.claim

/-- Successful prepared transactions produced by the builder always carry checked artifacts. -/
theorem prepareOfficialStereoTransaction_checked
    (blueprint : OfficialStereoRequestBlueprint) (key description fileName : String) :
    match prepareOfficialStereoTransaction blueprint key description fileName with
    | Except.ok prepared => prepared.exportEntry.artifact.claim
    | Except.error _ => True := by
  unfold prepareOfficialStereoTransaction
  cases h : blueprint.toOfficialStereoRequest with
  | error failure =>
      simp
  | ok request =>
      change (decideOfficialStereo request).artifact.claim
      exact (decideOfficialStereo request).artifact_claim

/-- Successful prepared transactions from checked intake successes always carry checked artifacts. -/
theorem prepareOfficialStereoTransactionFromIntakeSuccess_checked {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (spec : IntakeOfficialStereoSpec request success) (key description fileName : String) :
    match prepareOfficialStereoTransactionFromIntakeSuccess spec key description fileName with
    | Except.ok prepared => prepared.exportEntry.artifact.claim
    | Except.error _ => True := by
  exact prepareOfficialStereoTransaction_checked spec.toBlueprint key description fileName

/-- Successful compact host-query transactions always carry checked artifacts. -/
theorem prepareOfficialStereoTransactionFromIntakeQuery_checked {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success) :
    match prepareOfficialStereoTransactionFromIntakeQuery query with
    | Except.ok prepared => prepared.exportEntry.artifact.claim
    | Except.error _ => True := by
  exact prepareOfficialStereoTransactionFromIntakeSuccess_checked query.toSpec
    query.exportSpec.key query.exportSpec.description query.exportSpec.fileName

/-- Total host-query checked-on-success claims are checked by construction. -/
theorem officialStereoHostQueryCheckedClaim_checked {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success) :
    OfficialStereoHostQueryCheckedClaim query := by
  unfold OfficialStereoHostQueryCheckedClaim
  exact prepareOfficialStereoTransactionFromIntakeQuery_checked query

/-- Generated host-query claims require both a successful build and a checked prepared artifact. -/
theorem officialStereoHostQueryClaim_checked {request : ImportRequest}
    {success : CertifiedIntakeSuccess request}
    (query : IntakeOfficialStereoQuery request success)
    (hbuild : OfficialStereoHostQueryBuilds query) :
    OfficialStereoHostQueryClaim query := by
  unfold OfficialStereoHostQueryClaim OfficialStereoHostQueryBuilds at *
  cases hprepared : prepareOfficialStereoTransactionFromIntakeQuery query with
  | error failure =>
      simp [hprepared] at hbuild
  | ok prepared =>
      refine ⟨prepared, rfl, ?_⟩
      have hchecked := prepareOfficialStereoTransactionFromIntakeQuery_checked query
      rw [hprepared] at hchecked
      exact hchecked

end
end Engine
end TetraStereo
