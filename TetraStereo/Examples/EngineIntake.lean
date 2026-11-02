import TetraStereo.Engine.Intake

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace EngineIntake

open OneCenter

noncomputable section

/-!
  Checked examples for the production-facing intake spine.

  These examples exercise all three important intake outcomes:

  * an internally parsed OpenSMILES molecule imports successfully;
  * a molfile string is refused because it must enter through an external bridge packet;
  * a malformed bridge packet is refused because executable admission checks fail.
-/

def methaneOpenSMILESStringRequest : Engine.StringImportRequest where
  format := ChemistryImportFormat.openSMILES
  input := "C"

def methaneOpenSMILESRequest : Engine.ImportRequest :=
  Engine.ImportRequest.string methaneOpenSMILESStringRequest

def methaneOpenSMILESPlan : Engine.PublicIntakeTheoremPlan where
  imports := ["TetraStereo.Engine.Intake", "TetraStereo.Examples.EngineIntake"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "methane_opensmiles_intake_imports"
  statement := "TetraStereo.Examples.EngineIntake.methaneOpenSMILESDecision.artifactClaim"
  proofTerm := "  exact TetraStereo.Examples.EngineIntake.methaneOpenSMILESDecision_checked"

def methaneOpenSMILESDecision : Engine.IntakeDecision methaneOpenSMILESRequest :=
  Engine.decideIntake methaneOpenSMILESRequest methaneOpenSMILESPlan

theorem methaneOpenSMILESDecision_imported :
    methaneOpenSMILESDecision.result?.isSome = true := by
  rfl

theorem methaneOpenSMILESDecision_checked : methaneOpenSMILESDecision.artifactClaim :=
  Engine.IntakeDecision.artifact_checked (request := methaneOpenSMILESRequest)
    methaneOpenSMILESDecision

def molfileStringRequest : Engine.ImportRequest :=
  Engine.ImportRequest.string
    { format := ChemistryImportFormat.molfileV2000
      input := "example molfile payload" }

def molfileStringPlan : Engine.PublicIntakeTheoremPlan where
  imports := ["TetraStereo.Engine.Intake", "TetraStereo.Examples.EngineIntake"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "molfile_string_intake_refused_without_bridge"
  statement := "TetraStereo.Examples.EngineIntake.molfileStringDecision.artifactClaim"
  proofTerm := "  exact TetraStereo.Examples.EngineIntake.molfileStringDecision_checked"

def molfileStringDecision : Engine.IntakeDecision molfileStringRequest :=
  Engine.decideIntake molfileStringRequest molfileStringPlan

theorem molfileStringDecision_refused :
    molfileStringDecision.reason? =
      some
        (Engine.IntakeRefusalReason.importError
          (ChemistryImportError.externalBridgeRequired ChemistryImportFormat.molfileV2000)) :=
  rfl

theorem molfileStringDecision_checked : molfileStringDecision.artifactClaim :=
  Engine.IntakeDecision.artifact_checked (request := molfileStringRequest) molfileStringDecision

def malformedRaw : RawMolecule where
  atoms := [AtomSpec.aliphatic Element.C]
  bonds := [{ source := 0, target := 1, kind := ParsedBondKind.single }]

def malformedBridgeRequest : Engine.ImportRequest :=
  Engine.ImportRequest.bridgePacket (rawMoleculePacket malformedRaw)

def malformedBridgePlan : Engine.PublicIntakeTheoremPlan where
  imports := ["TetraStereo.Engine.Intake", "TetraStereo.Examples.EngineIntake"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "malformed_bridge_packet_intake_refused"
  statement := "TetraStereo.Examples.EngineIntake.malformedBridgeDecision.artifactClaim"
  proofTerm := "  exact TetraStereo.Examples.EngineIntake.malformedBridgeDecision_checked"

def malformedBridgeDecision : Engine.IntakeDecision malformedBridgeRequest :=
  Engine.decideIntake malformedBridgeRequest malformedBridgePlan

theorem malformedBridgeDecision_refused :
    malformedBridgeDecision.reason? =
      some Engine.IntakeRefusalReason.rawMoleculeNotAdmissible :=
  rfl

theorem malformedBridgeDecision_checked : malformedBridgeDecision.artifactClaim :=
  Engine.IntakeDecision.artifact_checked (request := malformedBridgeRequest)
    malformedBridgeDecision

/-! ### Duplicate unordered-edge regression -/

/-- External packets cannot rely on parser finalization, so the shared intake invariant must reject
the same tetrahedral duplicate-edge shape independently. -/
def duplicateTetrahedralRaw : RawMolecule where
  atoms := List.replicate 5 (AtomSpec.aliphatic Element.C)
  bonds :=
    [ { source := 0, target := 4, kind := ParsedBondKind.single }
    , { source := 0, target := 1, kind := ParsedBondKind.single }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single }
    ]

theorem duplicateTetrahedralRaw_not_admissible :
    duplicateTetrahedralRaw.admissible? = false := by
  rfl

def duplicateTetrahedralBridgeRequest : Engine.ImportRequest :=
  Engine.ImportRequest.bridgePacket (rawMoleculePacket duplicateTetrahedralRaw)

def duplicateTetrahedralBridgePlan : Engine.PublicIntakeTheoremPlan where
  imports := ["TetraStereo.Engine.Intake", "TetraStereo.Examples.EngineIntake"]
  namespacePath := ["TetraStereo", "Examples", "GeneratedCertificates"]
  theoremName := "duplicate_tetrahedral_bridge_packet_refused"
  statement :=
    "TetraStereo.Examples.EngineIntake.duplicateTetrahedralBridgeDecision.artifactClaim"
  proofTerm :=
    "  exact TetraStereo.Examples.EngineIntake.duplicateTetrahedralBridgeDecision_checked"

def duplicateTetrahedralBridgeDecision :
    Engine.IntakeDecision duplicateTetrahedralBridgeRequest :=
  Engine.decideIntake duplicateTetrahedralBridgeRequest duplicateTetrahedralBridgePlan

theorem duplicateTetrahedralBridgeDecision_refused :
    duplicateTetrahedralBridgeDecision.reason? =
      some Engine.IntakeRefusalReason.rawMoleculeNotAdmissible :=
  rfl

theorem duplicateTetrahedralBridgeDecision_checked :
    duplicateTetrahedralBridgeDecision.artifactClaim :=
  Engine.IntakeDecision.artifact_checked (request := duplicateTetrahedralBridgeRequest)
    duplicateTetrahedralBridgeDecision

end
end EngineIntake
end Examples
end TetraStereo
