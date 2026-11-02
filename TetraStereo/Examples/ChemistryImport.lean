import TetraStereo.OneCenter.ChemistryImport

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace ChemistryImport

open OneCenter

/-- A tiny raw molecule used as a stand-in for external molfile/InChI/RDKit bridge output. -/
def methaneRaw : RawMolecule where
  atoms := [AtomSpec.aliphatic Element.C]
  bonds := []

example :
    (importOpenSMILES "C").isOk = true := by
  rfl

example :
    (match importOpenSMILES "C" with
      | Except.ok result => decide (result.source.format = ChemistryImportFormat.openSMILES)
      | Except.error _ => false) = true := by
  rfl

example :
    parseImportStringAsRaw ChemistryImportFormat.molfileV2000 "molfile text" =
      Except.error
        (ChemistryImportError.externalBridgeRequired ChemistryImportFormat.molfileV2000) :=
  rfl

example :
    parseImportStringAsRaw ChemistryImportFormat.rawMolecule "not a string format" =
      Except.error ChemistryImportError.rawMoleculeRequiresPacket :=
  rfl

example :
    (importExternalRawMoleculePacket (molfilePacket methaneRaw)).source.format =
      ChemistryImportFormat.molfileV2000 :=
  rfl

example :
    (importExternalRawMoleculePacket (rdkitPacket methaneRaw)).trust =
      ChemistryImportTrust.externalToolkit :=
  rfl

example :
    (importExternalRawMoleculePacket (rdkitPacket methaneRaw)).normalized.boundary.importsAromaticity =
      true :=
  rfl

example :
    (importExternalRawMoleculePacket (rdkitPacket methaneRaw)).normalized.boundary.importsResonance =
      true :=
  rfl

example :
    (importExternalRawMoleculePacket (molfilePacket methaneRaw)).normalized.normalized.parsed.atomCount =
      1 :=
  rfl

example :
    (importExternalRawMoleculePacket (rawMoleculePacket methaneRaw)).trust =
      ChemistryImportTrust.userSuppliedRawMolecule :=
  rfl

example :
    (importExternalRawMoleculePacket
      (rawMoleculePacket methaneRaw ChemistryImportTrust.proofCertifiedAdapter)).trust =
      ChemistryImportTrust.proofCertifiedAdapter :=
  rfl

example :
    ChemistryNormalizationPolicy.openSMILESDefault.leanChecksValence = true :=
  rfl

example :
    ChemistryNormalizationPolicy.toolkitBridgeDefault.importsAromaticity = true :=
  rfl

end ChemistryImport
end Examples
end TetraStereo
