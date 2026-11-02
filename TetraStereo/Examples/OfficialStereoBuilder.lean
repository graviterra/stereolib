import TetraStereo.Engine.OfficialStereoBuilder
import TetraStereo.OneCenter.OfficialUniformTerminalLigandTie
import TetraStereo.KernelOnly
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TetraStereo
namespace Examples
namespace OfficialStereoBuilder

open OneCenter

noncomputable section

/-!
  Checked examples for the automatic official-stereo request builder.

  The important point of this file is not a chemically interesting descriptor; it is the engine
  boundary.  A checked intake success is converted automatically into a proof-facing molecular
  graph, detected multi-center molecule, selected center proof, local one-center request, public
  decision, and certificate export entry.

  This successor preserves the original `C(F)(O)(N)Cl` automatic-bridge chain, but removes the
  hand-built request fallback and the unsound refusal claim associated with it: the request is now
  the actual successful builder output.  A second, fully concrete `CCl4` construction is added.  Its
  four ligands are genuinely tied by the actual rule-major engine, so the actual builder decision
  really is a refusal at unresolved official priorities, and that refusal is the exported artifact.
-/

/-! ## Original compact automatic-bridge chain (preserved) -/

/-- Tetrahedral raw molecule used to test automatic request construction from checked intake. -/
def autoBridgeRaw : RawMolecule where
  atoms :=
    [ AtomSpec.aliphatic Element.C
    , AtomSpec.aliphatic Element.F
    , AtomSpec.aliphatic Element.O
    , AtomSpec.aliphatic Element.N
    , AtomSpec.aliphatic Element.Cl
    ]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single }
    ]

/-- Bridge-packet intake request for the automatic request-builder smoke test. -/
def autoBridgeImportRequest : Engine.ImportRequest :=
  Engine.ImportRequest.bridgePacket
    (rawMoleculePacket autoBridgeRaw ChemistryImportTrust.proofCertifiedAdapter)

/-- Concrete import result for the proof-certified bridge packet. -/
def autoBridgeImportResult : ChemistryImportResult :=
  importExternalRawMoleculePacket
    (rawMoleculePacket autoBridgeRaw ChemistryImportTrust.proofCertifiedAdapter)

/-- The bridge packet passes the checked intake boundary. -/
theorem autoBridgeSafeImport_eq_ok :
    autoBridgeImportRequest.safeImport? = Except.ok autoBridgeImportResult :=
  rfl


def autoBridgeIntakeTheoremPlan : Engine.PublicIntakeTheoremPlan where
  imports := ["TetraStereo.Engine.OfficialStereoBuilder",
    "TetraStereo.Examples.OfficialStereoBuilder"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "auto_bridge_intake_imports"
  statement :=
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeIntakeSuccess.artifact.claim"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoBuilder.autoBridgeIntakeSuccess_checked"

/-- Checked intake success used as the source for automatic official-stereo request construction. -/
def autoBridgeIntakeSuccess :
    Engine.CertifiedIntakeSuccess autoBridgeImportRequest where
  result := autoBridgeImportResult
  success := autoBridgeSafeImport_eq_ok
  rawAdmissible := (RawMolecule.admissible?_eq_true_iff autoBridgeRaw).1 rfl
  normalizedAdmissible := autoBridgeRaw.normalizeUnspecifiedBonds_admissible
    ((RawMolecule.admissible?_eq_true_iff autoBridgeRaw).1 rfl)
  theoremPlan := autoBridgeIntakeTheoremPlan
  artifact :=
    Engine.compilePublicIntakeSuccess autoBridgeIntakeTheoremPlan autoBridgeImportRequest
      autoBridgeImportResult autoBridgeSafeImport_eq_ok
  artifact_eq := rfl

/-- The intake artifact remains checked before request construction begins. -/
theorem autoBridgeIntakeSuccess_checked :
    autoBridgeIntakeSuccess.artifact.claim :=
  autoBridgeIntakeSuccess.artifact_checked






def autoBridgeOfficialTheoremPlan : Engine.PublicOfficialStereoTheoremPlan where
  imports := ["TetraStereo.Engine.OfficialStereoBuilder",
    "TetraStereo.Examples.OfficialStereoBuilder"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "auto_bridge_official_stereo_checked"
  requestExpr := "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeRequest"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared_checked"

/-- Host-facing export metadata for the compact official-stereo query. -/
def autoBridgeExportSpec : Engine.OfficialStereoExportSpec where
  key := "auto-bridge-official-stereo-checked"
  description := "auto-built official-stereo prepared transaction from checked intake"
  fileName := "AutoBridgeOfficialStereoChecked.lean"
  imports := ["TetraStereo.Engine.OfficialStereoBuilder",
    "TetraStereo.Examples.OfficialStereoBuilder"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "auto_bridge_official_stereo_checked"
  requestExpr := "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeRequest"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared_checked"

/-- Host-facing spec: choose atom `0` as the center and compare two local branches. -/
def autoBridgeSpec :
    Engine.IntakeOfficialStereoSpec autoBridgeImportRequest autoBridgeIntakeSuccess where
  annotations := {}
  centerAtom := ⟨0, by decide⟩
  left := 0
  right := 1
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  theoremPlan := autoBridgeOfficialTheoremPlan

/-- Compact host-facing query: checked intake plus the chemical question and export metadata. -/
def autoBridgeQuery :
    Engine.IntakeOfficialStereoQuery autoBridgeImportRequest autoBridgeIntakeSuccess where
  annotations := {}
  centerAtom := ⟨0, by decide⟩
  left := 0
  right := 1
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  exportSpec := autoBridgeExportSpec

/-- The compact host query expands to the same lower-level checked-intake spec. -/
theorem autoBridgeQuery_toSpec_eq :
    autoBridgeQuery.toSpec = autoBridgeSpec :=
  rfl

/-- Source-only generated host module spec for the compact official-stereo query. -/
def autoBridgeHostQuerySourceSpec : Engine.OfficialStereoHostQuerySourceSpec :=
  autoBridgeQuery.hostQuerySourceSpec
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeQuery"
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeHostQueryBuilds"
    "auto_bridge_official_stereo_query_checked"

/-- Automatically generated source-registry entry for the compact host query. -/
def autoBridgeHostQuerySourceEntry : Engine.CertificateSourceEntry :=
  autoBridgeQuery.hostQuerySourceEntry
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeQuery"
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeHostQueryBuilds"
    "auto_bridge_official_stereo_query_checked"

/-- The generated source-registry entry uses the host-facing export key. -/
theorem autoBridgeHostQuerySourceEntry_key :
    autoBridgeHostQuerySourceEntry.key = "auto-bridge-official-stereo-checked" :=
  rfl

/-- The normalized-intake spec converted to an automatic request blueprint. -/
def autoBridgeBlueprint : Engine.OfficialStereoRequestBlueprint :=
  autoBridgeSpec.toBlueprint

/-- Atom `0` is automatically detected as a tetrahedral center in the normalized graph. -/
theorem autoBridgeCenter_mem :
    (⟨0, by decide⟩ : Fin autoBridgeBlueprint.normalized.parsed.atomCount) ∈
      autoBridgeBlueprint.molecule.centers := by
  simp [autoBridgeBlueprint, Engine.IntakeOfficialStereoSpec.toBlueprint, autoBridgeSpec,
    Engine.OfficialStereoRequestBlueprint.molecule, Engine.OfficialStereoRequestBlueprint.graph,
    MoleculeGraph.detectedMultiCenterMolecule, MoleculeGraph.tetrahedralCenterSet]
  decide

/-- The automatic blueprint successfully builds a proof-facing request. -/
theorem autoBridgeBlueprint_builds :
    (match autoBridgeBlueprint.toOfficialStereoRequest with
      | Except.ok _ => true
      | Except.error _ => false) = true :=
  rfl

/-- The automatic blueprint actually takes the successful `ok` path. -/
theorem autoBridgeBlueprint_builds_ok :
    ∃ request, autoBridgeBlueprint.toOfficialStereoRequest = Except.ok request := by
  cases h : autoBridgeBlueprint.toOfficialStereoRequest with
  | ok request => exact ⟨request, rfl⟩
  | error failure =>
      have hbool := autoBridgeBlueprint_builds
      rw [h] at hbool
      cases hbool

/-- Request obtained from the actual automatic builder, with no fallback branch and no hand-built
local molecule.  The extraction is justified by the proved successful build above. -/
def autoBridgeRequest : Engine.OfficialStereoRequest :=
  Classical.choose autoBridgeBlueprint_builds_ok

/-- The extracted request is exactly the request the automatic blueprint builds. -/
theorem autoBridgeRequest_spec :
    autoBridgeBlueprint.toOfficialStereoRequest = Except.ok autoBridgeRequest :=
  Classical.choose_spec autoBridgeBlueprint_builds_ok

/-- Total decision produced by the automatically built official-stereo request. -/
def autoBridgeDecision : Engine.OfficialStereoDecision autoBridgeRequest :=
  Engine.decideOfficialStereo autoBridgeRequest

/-- Full builder result: checked intake success to prepared certificate export entry. -/
def autoBridgePreparedResult :
    Except Engine.OfficialStereoBuildFailure Engine.PreparedOfficialStereoTransaction :=
  Engine.prepareOfficialStereoTransactionFromIntakeQuery autoBridgeQuery

/-- The full builder path succeeds. -/
theorem autoBridgePreparedResult_builds :
    (match autoBridgePreparedResult with
      | Except.ok _ => true
      | Except.error _ => false) = true :=
  rfl

/-- The full builder path really returns a prepared transaction. -/
theorem autoBridgePreparedResult_ok :
    ∃ prepared, autoBridgePreparedResult = Except.ok prepared := by
  cases h : autoBridgePreparedResult with
  | ok prepared => exact ⟨prepared, rfl⟩
  | error failure =>
      have hbool := autoBridgePreparedResult_builds
      rw [h] at hbool
      cases hbool

/-- The actual prepared transaction produced by the automatic builder. -/
def autoBridgePrepared : Engine.PreparedOfficialStereoTransaction :=
  Classical.choose autoBridgePreparedResult_ok

/-- The extracted prepared transaction is the builder's own successful output. -/
theorem autoBridgePrepared_spec :
    autoBridgePreparedResult = Except.ok autoBridgePrepared :=
  Classical.choose_spec autoBridgePreparedResult_ok

/-- The builder's prepared export entry carries a checked artifact. -/
theorem autoBridgePrepared_checked :
    autoBridgePrepared.exportEntry.artifact.claim :=
  autoBridgePrepared.exportEntry_checked






def autoBridgeCheckedTheoremExport : LeanTheoremExport where
  imports := ["TetraStereo.Engine.OfficialStereoBuilder",
    "TetraStereo.Examples.OfficialStereoBuilder"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "auto_bridge_official_stereo_checked"
  statement :=
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared.exportEntry.artifact.claim"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared_checked"





def autoBridgeCheckedArtifact : LeanCertificateArtifact :=
  { autoBridgePrepared.exportEntry.artifact with
    theoremExport := autoBridgeCheckedTheoremExport }

/-- The registered wrapper's claim is the prepared artifact's checked claim. -/
theorem autoBridgeCheckedArtifact_claim :
    autoBridgeCheckedArtifact.claim :=
  autoBridgePrepared_checked

/-- The compact host query really builds a prepared transaction. -/
theorem autoBridgeHostQueryBuilds :
    Engine.OfficialStereoHostQueryBuilds autoBridgeQuery := by
  unfold Engine.OfficialStereoHostQueryBuilds
  change (match autoBridgePreparedResult with
    | Except.ok _ => True
    | Except.error _ => False)
  cases h : autoBridgePreparedResult with
  | ok prepared =>
      trivial
  | error failure =>
      have hbool := autoBridgePreparedResult_builds
      rw [h] at hbool
      simp at hbool

/-- The compact host-query claim proves that the query built a checked prepared transaction. -/
theorem autoBridgeHostQueryClaim_checked :
    Engine.OfficialStereoHostQueryClaim autoBridgeQuery :=
  Engine.officialStereoHostQueryClaim_checked autoBridgeQuery autoBridgeHostQueryBuilds

/-! ## The actual `CCl4` construction

The raw molecule below enters through the proof-certified bridge-packet boundary, becomes a checked
`CertifiedIntakeSuccess`, is converted by `IntakeOfficialStereoSpec` / `IntakeOfficialStereoQuery`
into a blueprint, and is finally built by the actual `toOfficialStereoRequest` function.  The
request is extracted from the builder's successful output; it is not hand-built. -/

/-- Carbon tetrachloride: carbon `0` singly bonded to the four chlorine atoms `1, 2, 3, 4`. -/
def ccl4Raw : RawMolecule where
  atoms :=
    [ AtomSpec.aliphatic Element.C
    , AtomSpec.aliphatic Element.Cl
    , AtomSpec.aliphatic Element.Cl
    , AtomSpec.aliphatic Element.Cl
    , AtomSpec.aliphatic Element.Cl
    ]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single }
    ]

/-- Proof-certified bridge-packet intake request for `CCl4`. -/
def ccl4ImportRequest : Engine.ImportRequest :=
  Engine.ImportRequest.bridgePacket
    (rawMoleculePacket ccl4Raw ChemistryImportTrust.proofCertifiedAdapter)

/-- Concrete checked-intake result for the `CCl4` bridge packet. -/
def ccl4ImportResult : ChemistryImportResult :=
  importExternalRawMoleculePacket
    (rawMoleculePacket ccl4Raw ChemistryImportTrust.proofCertifiedAdapter)

/-- The concrete `CCl4` packet passes the checked intake boundary. -/
theorem ccl4SafeImport_eq_ok :
    ccl4ImportRequest.safeImport? = Except.ok ccl4ImportResult :=
  rfl

/-- The raw `CCl4` molecule is structurally admissible. -/
theorem ccl4Raw_admissible : ccl4Raw.Admissible :=
  (RawMolecule.admissible?_eq_true_iff ccl4Raw).1 (by decide)

/-- The normalized `CCl4` molecule is structurally admissible. -/
theorem ccl4Normalized_admissible :
    ccl4Raw.normalizeUnspecifiedBonds.Admissible :=
  ccl4Raw.normalizeUnspecifiedBonds_admissible ccl4Raw_admissible


def ccl4IntakeTheoremPlan : Engine.PublicIntakeTheoremPlan where
  imports := ["TetraStereo.Engine.OfficialStereoBuilder",
    "TetraStereo.Examples.OfficialStereoBuilder"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "ccl4_intake_imports"
  statement :=
    "TetraStereo.Examples.OfficialStereoBuilder.ccl4IntakeSuccess.artifact.claim"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoBuilder.ccl4IntakeSuccess_checked"

/-- Checked intake success for the concrete `CCl4` raw molecule. -/
def ccl4IntakeSuccess :
    Engine.CertifiedIntakeSuccess ccl4ImportRequest where
  result := ccl4ImportResult
  success := ccl4SafeImport_eq_ok
  rawAdmissible := ccl4Raw_admissible
  normalizedAdmissible := ccl4Normalized_admissible
  theoremPlan := ccl4IntakeTheoremPlan
  artifact :=
    Engine.compilePublicIntakeSuccess ccl4IntakeTheoremPlan ccl4ImportRequest
      ccl4ImportResult ccl4SafeImport_eq_ok
  artifact_eq := rfl

/-- The `CCl4` intake artifact is checked before any request construction. -/
theorem ccl4IntakeSuccess_checked :
    ccl4IntakeSuccess.artifact.claim :=
  ccl4IntakeSuccess.artifact_checked


def ccl4OfficialTheoremPlan : Engine.PublicOfficialStereoTheoremPlan where
  imports := ["TetraStereo.Engine.OfficialStereoBuilder",
    "TetraStereo.OneCenter.OfficialUniformTerminalLigandTie",
    "TetraStereo.Examples.OfficialStereoBuilder"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "ccl4_official_stereo_refusal"
  requestExpr := "TetraStereo.Examples.OfficialStereoBuilder.ccl4Request"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoBuilder.ccl4Request_refusal_claim"

/-- Host-facing export metadata for the concrete `CCl4` query. -/
def ccl4ExportSpec : Engine.OfficialStereoExportSpec where
  key := "ccl4-official-stereo-refusal"
  description := "checked actual CCl4 automatic-builder refusal from checked intake"
  fileName := "CCl4OfficialStereoRefusal.lean"
  imports := ["TetraStereo.Engine.OfficialStereoBuilder",
    "TetraStereo.OneCenter.OfficialUniformTerminalLigandTie",
    "TetraStereo.Examples.OfficialStereoBuilder"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "ccl4_official_stereo_refusal"
  requestExpr := "TetraStereo.Examples.OfficialStereoBuilder.ccl4Request"
  proofTerm :=
    "  exact TetraStereo.Examples.OfficialStereoBuilder.ccl4Request_refusal_claim"

/-- Checked-intake spec: atom `0` is the carbon center; compare the first two chlorine ligands. -/
def ccl4Spec :
    Engine.IntakeOfficialStereoSpec ccl4ImportRequest ccl4IntakeSuccess where
  annotations := {}
  centerAtom := ⟨0, by decide⟩
  left := 0
  right := 1
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  theoremPlan := ccl4OfficialTheoremPlan

/-- Compact host-facing `CCl4` query. -/
def ccl4Query :
    Engine.IntakeOfficialStereoQuery ccl4ImportRequest ccl4IntakeSuccess where
  annotations := {}
  centerAtom := ⟨0, by decide⟩
  left := 0
  right := 1
  graphFuel := 0
  scheduleFuel := 0
  branchFuel := 0
  exportSpec := ccl4ExportSpec

/-- The compact query expands to the same lower-level checked-intake spec. -/
theorem ccl4Query_toSpec_eq :
    ccl4Query.toSpec = ccl4Spec :=
  rfl

/-- The source-only generated host-query spec for the concrete `CCl4` query. -/
def ccl4HostQuerySourceSpec : Engine.OfficialStereoHostQuerySourceSpec :=
  ccl4Query.hostQuerySourceSpec
    "TetraStereo.Examples.OfficialStereoBuilder.ccl4Query"
    "TetraStereo.Examples.OfficialStereoBuilder.ccl4HostQueryBuilds"
    "ccl4_official_stereo_query_checked"

/-- The generated source-registry entry for the concrete `CCl4` query. -/
def ccl4HostQuerySourceEntry : Engine.CertificateSourceEntry :=
  ccl4Query.hostQuerySourceEntry
    "TetraStereo.Examples.OfficialStereoBuilder.ccl4Query"
    "TetraStereo.Examples.OfficialStereoBuilder.ccl4HostQueryBuilds"
    "ccl4_official_stereo_query_checked"

/-- The `CCl4` source entry uses the `CCl4` export key. -/
theorem ccl4HostQuerySourceEntry_key :
    ccl4HostQuerySourceEntry.key = "ccl4-official-stereo-refusal" :=
  rfl

/-- The normalized checked-intake spec converted to an automatic request blueprint. -/
def ccl4Blueprint : Engine.OfficialStereoRequestBlueprint :=
  ccl4Spec.toBlueprint

/-- Atom `0` is genuinely detected as a tetrahedral center in the normalized `CCl4` graph. -/
theorem ccl4Center_mem :
    (⟨0, by decide⟩ : Fin ccl4Blueprint.normalized.parsed.atomCount) ∈
      ccl4Blueprint.molecule.centers := by
  simp [ccl4Blueprint, Engine.IntakeOfficialStereoSpec.toBlueprint, ccl4Spec,
    Engine.OfficialStereoRequestBlueprint.molecule, Engine.OfficialStereoRequestBlueprint.graph,
    MoleculeGraph.detectedMultiCenterMolecule, MoleculeGraph.tetrahedralCenterSet]
  decide

/-- The `CCl4` blueprint's center selector returns the detected center. -/
theorem ccl4Blueprint_center?_eq_some :
    ccl4Blueprint.center? =
      some ⟨⟨0, by decide⟩, ccl4Center_mem⟩ := by
  unfold Engine.OfficialStereoRequestBlueprint.center?
  split
  · rfl
  · exact absurd ccl4Center_mem (by assumption)

/-- The explicit payload of the builder's successful `CCl4` branch.

Its `localMolecule` is exactly the blueprint's automatically derived one-center view; it is not an
independent (fallback) molecule. -/
def ccl4RequestConcrete : Engine.OfficialStereoRequest where
  normalized := ccl4Blueprint.normalized
  annotations := ccl4Blueprint.annotations
  molecule := ccl4Blueprint.molecule
  profile := ccl4Blueprint.profile
  graphFuel := ccl4Blueprint.graphFuel
  scheduleFuel := ccl4Blueprint.scheduleFuel
  branchFuel := ccl4Blueprint.branchFuel
  center := ⟨⟨0, by decide⟩, ccl4Center_mem⟩
  localMolecule :=
    ccl4Blueprint.molecule.toOneCenterMolecule
      ⟨⟨0, by decide⟩, ccl4Center_mem⟩
  left := ccl4Blueprint.left
  right := ccl4Blueprint.right
  theoremPlan := ccl4Blueprint.theoremPlan

@[simp] theorem ccl4RequestConcrete_graphFuel :
    ccl4RequestConcrete.graphFuel = 0 :=
  rfl

@[simp] theorem ccl4RequestConcrete_scheduleFuel :
    ccl4RequestConcrete.scheduleFuel = 0 :=
  rfl

@[simp] theorem ccl4RequestConcrete_branchFuel :
    ccl4RequestConcrete.branchFuel = 0 :=
  rfl

@[simp] theorem ccl4RequestConcrete_left : ccl4RequestConcrete.left = 0 :=
  rfl

@[simp] theorem ccl4RequestConcrete_right : ccl4RequestConcrete.right = 1 :=
  rfl

/-- The actual builder returns exactly the explicit payload. -/
theorem ccl4Blueprint_toOfficialStereoRequest_eq :
    ccl4Blueprint.toOfficialStereoRequest = Except.ok ccl4RequestConcrete := by
  unfold Engine.OfficialStereoRequestBlueprint.toOfficialStereoRequest
  rw [ccl4Blueprint_center?_eq_some]
  rfl

/-- The `CCl4` blueprint succeeds under the actual builder. -/
theorem ccl4Blueprint_builds :
    (match ccl4Blueprint.toOfficialStereoRequest with
      | Except.ok _ => true
      | Except.error _ => false) = true :=
  rfl

/-- Existence form of the successful `CCl4` build. -/
theorem ccl4Blueprint_builds_ok :
    ∃ request, ccl4Blueprint.toOfficialStereoRequest = Except.ok request :=
  ⟨ccl4RequestConcrete, ccl4Blueprint_toOfficialStereoRequest_eq⟩

/-- The request actually produced by the automatic builder for the checked `CCl4` intake. -/
def ccl4Request : Engine.OfficialStereoRequest :=
  Classical.choose ccl4Blueprint_builds_ok

/-- Specification of the `CCl4` builder extraction. -/
theorem ccl4Request_spec :
    ccl4Blueprint.toOfficialStereoRequest = Except.ok ccl4Request :=
  Classical.choose_spec ccl4Blueprint_builds_ok

/-- The extracted request is the explicit successful payload. -/
theorem ccl4Request_eq_concrete :
    ccl4Request = ccl4RequestConcrete := by
  have h := ccl4Request_spec
  rw [ccl4Blueprint_toOfficialStereoRequest_eq] at h
  injection h with h'
  exact h'.symm

/-- The extracted request's normalization is the checked `CCl4` intake normalization. -/
theorem ccl4Request_normalized_eq_intake :
    ccl4Request.normalized = ccl4IntakeSuccess.result.normalized.normalized := by
  rw [ccl4Request_eq_concrete]
  rfl

/-- The extracted request's normalization is literally `normalizeRawMolecule ccl4Raw`. -/
theorem ccl4Request_normalized_eq :
    ccl4Request.normalized = normalizeRawMolecule ccl4Raw := by
  rw [ccl4Request_normalized_eq_intake]
  rfl

/-! ### Structural facts about the four actual selected ligands

Nothing below enumerates the opaque noncomputable ligand equivalence.  The facts are derived from
the actual `ligandAtom_adj` field and the concrete normalized graph. -/

/-- The selected center is the concrete carbon atom `0`. -/
theorem ccl4Concrete_center_eq :
    ccl4RequestConcrete.oneCenter.center = (0 : Fin 5) := by
  apply Fin.ext
  decide

/-- Every actual selected ligand has nonzero atom index. -/
theorem ccl4Concrete_ligand_val_ne_zero (i : Fin 4) :
    (ccl4RequestConcrete.oneCenter.ligandAtom i).val ≠ 0 := by
  intro hzero
  have hne := ccl4RequestConcrete.oneCenter.ligandAtom_ne_center i
  apply hne
  rw [ccl4Concrete_center_eq]
  exact Fin.ext hzero

/-- Every actual selected ligand is one of the concrete chlorine atoms `1, 2, 3, 4`. -/
theorem ccl4Concrete_ligand_val_cases (i : Fin 4) :
    (ccl4RequestConcrete.oneCenter.ligandAtom i).val = 1 ∨
      (ccl4RequestConcrete.oneCenter.ligandAtom i).val = 2 ∨
      (ccl4RequestConcrete.oneCenter.ligandAtom i).val = 3 ∨
      (ccl4RequestConcrete.oneCenter.ligandAtom i).val = 4 := by
  have hlt : (ccl4RequestConcrete.oneCenter.ligandAtom i).val < 5 :=
    (ccl4RequestConcrete.oneCenter.ligandAtom i).isLt
  have hne := ccl4Concrete_ligand_val_ne_zero i
  omega

/-- Every actual selected ligand is one of the four concrete `Fin 5` chlorine atoms. -/
theorem ccl4Concrete_ligand_cases (i : Fin 4) :
    ccl4RequestConcrete.oneCenter.ligandAtom i = (1 : Fin 5) ∨
      ccl4RequestConcrete.oneCenter.ligandAtom i = (2 : Fin 5) ∨
      ccl4RequestConcrete.oneCenter.ligandAtom i = (3 : Fin 5) ∨
      ccl4RequestConcrete.oneCenter.ligandAtom i = (4 : Fin 5) := by
  rcases ccl4Concrete_ligand_val_cases i with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- Each selected ligand has exactly the center as its graph neighbor. -/
theorem ccl4Concrete_ligand_neighborFinset_eq_center (i : Fin 4) :
    ccl4RequestConcrete.oneCenter.mol.neighborFinset
        (ccl4RequestConcrete.oneCenter.ligandAtom i) =
      {ccl4RequestConcrete.oneCenter.center} := by
  rcases ccl4Concrete_ligand_cases i with h | h | h | h <;>
    rw [h, ccl4Concrete_center_eq] <;>
    decide

/-- Each selected ligand is joined to the center by a single bond. -/
theorem ccl4Concrete_ligand_bond_eq_one (i : Fin 4) :
    ccl4RequestConcrete.oneCenter.mol.bond
        (ccl4RequestConcrete.oneCenter.ligandAtom i)
        ccl4RequestConcrete.oneCenter.center = 1 := by
  rcases ccl4Concrete_ligand_cases i with h | h | h | h <;>
    rw [h, ccl4Concrete_center_eq] <;>
    decide

/-- Actual terminal-root lemma: a `rootFromEdge` whose current atom has only its parent as neighbor
and whose bond to that parent is single has no official children. -/
theorem officialCIPChildren_rootFromEdge_eq_nil_of_unique_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (parent current : V)
    (hunique : m.neighborFinset current = {parent})
    (hbond : m.bond current parent = 1) :
    m.officialCIPChildren (OfficialCIPNode.rootFromEdge parent current) = [] := by
  classical
  unfold MoleculeGraph.officialCIPChildren
  simp [OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.rootFromEdge,
    OfficialCIPNodeProvenance.isDuplicateLeaf,
    MoleculeGraph.officialChildCopies, OfficialCIPNode.parent?,
    MoleculeGraph.officialNeighborCopies, Finset.toList_singleton,
    hunique, hbond]

/-- Every actual selected `CCl4` ligand root is terminal under the actual child enumerator. -/
theorem ccl4Concrete_root_children_nil (i : Fin 4) :
    ccl4RequestConcrete.oneCenter.mol.officialCIPChildren
        (OfficialCIPNode.rootFromEdge ccl4RequestConcrete.oneCenter.center
          (ccl4RequestConcrete.oneCenter.ligandAtom i)) = [] :=
  officialCIPChildren_rootFromEdge_eq_nil_of_unique_neighbor
    ccl4RequestConcrete.oneCenter.mol ccl4RequestConcrete.oneCenter.center
    (ccl4RequestConcrete.oneCenter.ligandAtom i)
    (ccl4Concrete_ligand_neighborFinset_eq_center i)
    (ccl4Concrete_ligand_bond_eq_one i)

/-- Any two actual selected `CCl4` ligands carry the same atomic number. -/
theorem ccl4Concrete_ligand_atomZ_eq (i j : Fin 4) :
    ccl4RequestConcrete.oneCenter.mol.atomZ
        (ccl4RequestConcrete.oneCenter.ligandAtom i) =
      ccl4RequestConcrete.oneCenter.mol.atomZ
        (ccl4RequestConcrete.oneCenter.ligandAtom j) := by
  rcases ccl4Concrete_ligand_cases i with h | h | h | h <;>
    rcases ccl4Concrete_ligand_cases j with h' | h' | h' | h' <;>
    rw [h, h'] <;>
    decide

/-- Any two actual selected `CCl4` ligands carry the same isotope mass. -/
theorem ccl4Concrete_ligand_atomMass_eq (i j : Fin 4) :
    ccl4RequestConcrete.oneCenter.mol.atomMass
        (ccl4RequestConcrete.oneCenter.ligandAtom i) =
      ccl4RequestConcrete.oneCenter.mol.atomMass
        (ccl4RequestConcrete.oneCenter.ligandAtom j) := by
  rcases ccl4Concrete_ligand_cases i with h | h | h | h <;>
    rcases ccl4Concrete_ligand_cases j with h' | h' | h' | h' <;>
    rw [h, h'] <;>
    decide

/-! ### Detector contexts are empty

All detected `CCl4` units are unassigned single-bond conformational candidates (`kind? = none`), so
they seed no initial descriptor values.  At schedule fuel zero and branch fuel zero the detector
environment is therefore the initial environment, and the branch source search filters out every
unit. -/

/-- Every detected `CCl4` unit has no initially seeded descriptor values. -/
theorem ccl4Concrete_units_initialValuesEmpty :
    ccl4RequestConcrete.detection.units.all
        (fun unit => unit.initialValues.isEmpty) = true := by
  decide

/-- Pointwise version of unit-initial-value emptiness. -/
theorem ccl4Concrete_unit_initialValues_nil
    (unit : ccl4RequestConcrete.detection.Unit) :
    (ccl4RequestConcrete.detection.unitAt unit).initialValues = [] := by
  have h := (List.all_eq_true.mp ccl4Concrete_units_initialValuesEmpty)
    (ccl4RequestConcrete.detection.unitAt unit)
    (List.get_mem ccl4RequestConcrete.detection.units unit)
  exact List.isEmpty_iff.mp h

/-- Zero schedule fuel leaves the initial descriptor environment unchanged. -/
theorem ccl4Concrete_finalEnvironment_eq_initial :
    ccl4RequestConcrete.finalEnvironment =
      ccl4RequestConcrete.detection.initialEnvironment := by
  simp [Engine.OfficialStereoRequest.finalEnvironment, Engine.OfficialStereoRequest.output,
    OfficialDetectorOutput.finalEnvironment,
    OfficialUnitDetectionResult.toOfficialDetectorOutput]

/-- No detector unit carries an official descriptor value in the initial environment. -/
theorem ccl4Concrete_hasAnyValue_false
    (unit : ccl4RequestConcrete.detection.Unit) :
    ccl4RequestConcrete.detection.initialEnvironment.hasAnyValue unit = false := by
  have hvalues : (ccl4RequestConcrete.detection.unitAt unit).initialValues = [] :=
    ccl4Concrete_unit_initialValues_nil unit
  simp [OfficialUnitDetectionResult.initialEnvironment,
    OfficialDescriptorEnvironment.hasAnyValue, firstDescriptorProjection?, hvalues]

/-- The request's policy has no official-node frontier at any depth. -/
theorem ccl4Concrete_policy_officialNodesAtDepth_eq_empty
    (center : ccl4RequestConcrete.molecule.Center) (i : Fin 4) (depth : ℕ) :
    ccl4RequestConcrete.policy.officialNodesAtDepth center i depth = [] := by
  rfl

/-- The official-node source contribution is empty. -/
theorem ccl4Concrete_nodeSources_empty
    (center : ccl4RequestConcrete.molecule.Center) (i : Fin 4) (depth : ℕ) :
    ccl4RequestConcrete.molecule.officialNodeDescriptorUnitSources
        ccl4RequestConcrete.finalEnvironment ccl4RequestConcrete.policy center i
        (ccl4RequestConcrete.policy.officialNodesAtDepth center i depth) = [] := by
  rw [ccl4Concrete_policy_officialNodesAtDepth_eq_empty]
  simp [MultiCenterMolecule.officialNodeDescriptorUnitSources]

/-- At every depth the state-source contribution is empty. -/
theorem ccl4Concrete_stateSources_empty
    (center : ccl4RequestConcrete.molecule.Center) (i : Fin 4) (depth : ℕ) :
    (ccl4RequestConcrete.molecule.branchFrontier center i depth).flatMap
        (fun state =>
          let sourceKind :=
            if state.isDuplicate then
              BranchDescriptorSourceKind.duplicateAtom
            else
              BranchDescriptorSourceKind.atomSupport
          (ccl4RequestConcrete.policy.unitsAtAtom state.current).filterMap fun unit =>
            if ccl4RequestConcrete.finalEnvironment.hasAnyValue unit &&
                ccl4RequestConcrete.policy.includeStateSource center i state sourceKind unit then
              some ({ atom? := some state.current, sourceKind := sourceKind, unit := unit } :
                BranchDescriptorUnitSource ccl4RequestConcrete.molecule
                  ccl4RequestConcrete.detection.Unit)
            else
              none) = [] := by
  rw [List.flatMap_eq_nil_iff]
  intro state _
  dsimp only
  rw [List.filterMap_eq_nil_iff]
  intro unit _
  have hany : ccl4RequestConcrete.finalEnvironment.hasAnyValue unit = false := by
    rw [ccl4Concrete_finalEnvironment_eq_initial]
    exact ccl4Concrete_hasAnyValue_false unit
  simp [hany]

/-- At every depth the full descriptor-source list is empty. -/
theorem ccl4Concrete_sourcesAtDepth_empty
    (center : ccl4RequestConcrete.molecule.Center) (i : Fin 4) (depth : ℕ) :
    ccl4RequestConcrete.molecule.branchDescriptorUnitSourcesAtDepth
        ccl4RequestConcrete.finalEnvironment ccl4RequestConcrete.policy center i depth = [] := by
  unfold MultiCenterMolecule.branchDescriptorUnitSourcesAtDepth
  dsimp only
  rw [ccl4Concrete_stateSources_empty, ccl4Concrete_nodeSources_empty]
  rfl

/-- At branch fuel zero no descriptor sources are found. -/
theorem ccl4Concrete_sourcesWithin_zero_empty
    (center : ccl4RequestConcrete.molecule.Center) (i : Fin 4) :
    ccl4RequestConcrete.molecule.branchDescriptorUnitSourcesWithin
        ccl4RequestConcrete.finalEnvironment ccl4RequestConcrete.policy center i 0 = [] := by
  unfold MultiCenterMolecule.branchDescriptorUnitSourcesWithin
    MultiCenterMolecule.branchDescriptorUnitSourcesFrom
  exact ccl4Concrete_sourcesAtDepth_empty center i 0

/-- Every branch context of the actual `CCl4` request is empty. -/
theorem ccl4Concrete_context_empty (i : Fin 4) :
    ccl4RequestConcrete.compareContext i =
      CIPRuleEngine.OfficialLigandRuleContext.empty := by
  unfold Engine.OfficialStereoRequest.compareContext
    Engine.OfficialStereoRequest.branchContext
    Engine.OfficialStereoRequest.branchContextAt
    MultiCenterMolecule.officialBranchContextFromDescriptorSourceDetectorWithin
    MultiCenterMolecule.officialBranchContextFromDescriptorSourcePolicyWithin
  change officialContextOfDescriptorUnitSources
    (ccl4RequestConcrete.finalEnvironment)
    (ccl4RequestConcrete.molecule.branchDescriptorUnitSourcesWithin
      ccl4RequestConcrete.finalEnvironment ccl4RequestConcrete.policy
      ccl4RequestConcrete.center i 0) =
    CIPRuleEngine.OfficialLigandRuleContext.empty
  rw [ccl4Concrete_sourcesWithin_zero_empty]
  exact officialContextOfDescriptorUnitSources_nil
    (m := ccl4RequestConcrete.molecule) ccl4RequestConcrete.finalEnvironment

/-! ### The actual rule-major tie and the genuine refusal -/

/-- At graph fuel zero the actual engine returns a completed certificate for the two selected
chlorine branches, and its outcome is the exact tie `Ordering.eq`. -/
theorem ccl4Concrete_certificate_eq :
    ∃ certificate, ccl4RequestConcrete.certificate = some certificate ∧
      certificate.outcome = Ordering.eq := by
  obtain ⟨certificate, hcomputed, houtcome⟩ :=
    OneCenterMolecule.cipOfficialCompareWithFuel_terminal_tie
      ccl4RequestConcrete.oneCenter ccl4RequestConcrete.compareContext 0
      ccl4RequestConcrete.left ccl4RequestConcrete.right
      (ccl4Concrete_root_children_nil ccl4RequestConcrete.left)
      (ccl4Concrete_root_children_nil ccl4RequestConcrete.right)
      (ccl4Concrete_ligand_atomZ_eq ccl4RequestConcrete.left ccl4RequestConcrete.right)
      (ccl4Concrete_ligand_atomMass_eq ccl4RequestConcrete.left ccl4RequestConcrete.right)
      (ccl4Concrete_context_empty ccl4RequestConcrete.left)
      (ccl4Concrete_context_empty ccl4RequestConcrete.right)
  refine ⟨certificate, ?_, houtcome⟩
  unfold Engine.OfficialStereoRequest.certificate
  rw [ccl4RequestConcrete_graphFuel]
  exact hcomputed

/-- The actual extracted request certifies the tie. -/
theorem ccl4Request_certificate_eq :
    ∃ certificate, ccl4Request.certificate = some certificate ∧
      certificate.outcome = Ordering.eq := by
  obtain ⟨certificate, hcertificate, houtcome⟩ := ccl4Concrete_certificate_eq
  refine ⟨certificate, ?_, houtcome⟩
  rw [ccl4Request_eq_concrete]
  exact hcertificate

/-- The actual extracted request's outcome is the exact tie. -/
theorem ccl4Request_outcome_eq :
    ccl4Request.outcome = some Ordering.eq := by
  obtain ⟨certificate, hcertificate, houtcome⟩ := ccl4Request_certificate_eq
  unfold Engine.OfficialStereoRequest.outcome
  rw [hcertificate]
  simp [houtcome]

/-- The actual extracted request is not certificate-ready: its own computed outcome ties. -/
theorem ccl4Request_certificateReady_false :
    ccl4Request.certificateReady = false := by
  obtain ⟨certificate, hcertificate, houtcome⟩ := ccl4Request_certificate_eq
  unfold Engine.OfficialStereoRequest.certificateReady
    Engine.OfficialStereoRequest.outcomeDecisive
    Engine.OfficialStereoRequest.compiled
    Engine.OfficialStereoRequest.outcome
  rw [hcertificate]
  simp [Engine.OfficialStereoRequest.orderingDecisive, houtcome]

/-- The request's own refusal reason is exactly unresolved official priorities. -/
theorem ccl4Request_officialRefusalReason_eq :
    ccl4Request.officialRefusalReason? =
      some Engine.RefusalReason.unresolvedOfficialPriorities := by
  obtain ⟨certificate, hcertificate, houtcome⟩ := ccl4Request_certificate_eq
  unfold Engine.OfficialStereoRequest.officialRefusalReason?
  rw [hcertificate]
  simp [houtcome]

/-- Genuine checked refusal claim derived from the actual computed tie. -/
theorem ccl4Request_refusal_claim :
    Engine.OfficialStereoRefusalClaim ccl4Request
      Engine.RefusalReason.unresolvedOfficialPriorities :=
  ⟨ccl4Request_certificateReady_false, ccl4Request_officialRefusalReason_eq⟩

/-- Named checked refusal certificate for the actual `CCl4` automatic-builder request. -/
def ccl4Refusal :
    Engine.CertifiedOfficialStereoRefusal ccl4Request where
  reason := Engine.RefusalReason.unresolvedOfficialPriorities
  proof := ccl4Request_refusal_claim
  artifact :=
    Engine.compileOfficialStereoRefusal ccl4Request
      Engine.RefusalReason.unresolvedOfficialPriorities ccl4Request_refusal_claim
  artifact_eq := rfl

/-- The actual `CCl4` refusal artifact is Lean-checked. -/
theorem ccl4Refusal_checked :
    ccl4Refusal.artifact.claim :=
  ccl4Refusal.artifact_checked

/-- The exported artifact's subject is exactly the checked `CCl4` request and its refusal claim. -/
theorem ccl4Refusal_artifact_subject :
    ccl4Refusal.artifact.claim =
      Engine.OfficialStereoRefusalClaim ccl4Request
        Engine.RefusalReason.unresolvedOfficialPriorities :=
  rfl

/-- Total public decision for the actual `CCl4` request. -/
def ccl4Decision : Engine.OfficialStereoDecision ccl4Request :=
  Engine.decideOfficialStereo ccl4Request

/-- The total `CCl4` decision is the genuine refused branch. -/
theorem ccl4Decision_refused :
    ccl4Decision.outcome? = none := by
  obtain ⟨certificate, hcertificate, houtcome⟩ := ccl4Request_certificate_eq
  unfold ccl4Decision
  exact Engine.OfficialStereoRequest.decideOfficialStereo_outcome_eq_none_of_eq
    ccl4Request hcertificate houtcome

/-- Full builder result for the checked `CCl4` query. -/
def ccl4PreparedResult :
    Except Engine.OfficialStereoBuildFailure Engine.PreparedOfficialStereoTransaction :=
  Engine.prepareOfficialStereoTransactionFromIntakeQuery ccl4Query

/-- The full `CCl4` builder path succeeds. -/
theorem ccl4PreparedResult_builds :
    (match ccl4PreparedResult with
      | Except.ok _ => true
      | Except.error _ => false) = true :=
  rfl

/-- The compact `CCl4` host query really builds a prepared transaction. -/
theorem ccl4HostQueryBuilds :
    Engine.OfficialStereoHostQueryBuilds ccl4Query := by
  unfold Engine.OfficialStereoHostQueryBuilds
  change (match ccl4PreparedResult with
    | Except.ok _ => True
    | Except.error _ => False)
  cases h : ccl4PreparedResult with
  | ok prepared =>
      trivial
  | error failure =>
      have hbool := ccl4PreparedResult_builds
      rw [h] at hbool
      simp at hbool

/-- The compact `CCl4` host query's prepared artifact is checked. -/
theorem ccl4HostQueryClaim_checked :
    Engine.OfficialStereoHostQueryClaim ccl4Query :=
  Engine.officialStereoHostQueryClaim_checked ccl4Query ccl4HostQueryBuilds

/-! ## Kernel-authority guards

These commands reject any non-kernel axiom in the headline endpoints: the actual builder's
request equality, the actual certificate tie and its refusal consequences, and the checked wrapper
used by the public registries. -/

assert_kernel_only ccl4Blueprint_toOfficialStereoRequest_eq
assert_kernel_only ccl4Request_certificate_eq
assert_kernel_only ccl4Request_certificateReady_false
assert_kernel_only ccl4Request_officialRefusalReason_eq
assert_kernel_only ccl4Request_refusal_claim
assert_kernel_only autoBridgePrepared_checked
assert_kernel_only autoBridgeCheckedArtifact_claim

end
end OfficialStereoBuilder
end Examples
end TetraStereo
