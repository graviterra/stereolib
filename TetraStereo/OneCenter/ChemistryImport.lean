import TetraStereo.OneCenter.ChemistrySemantics

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Import boundary for production chemistry inputs.

  `ChemistrySemantics.lean` defines the normalized `RawMolecule` representation and the semantic
  bundles derived from it.  This module is the explicit importer contract in front of that layer.
  Lean currently owns the small OpenSMILES-style parser; molfile, InChI, and RDKit enter through an
  external bridge packet that must provide a `RawMolecule`, declared provenance, and a normalization
  policy.  The point is not to trust every upstream decision blindly: the boundary records which
  chemistry choices are checked by Lean and which are imported as external assumptions.
-/

/-! ### Import formats and trust boundary -/

/-- External molecule formats or producer surfaces that can feed the importer boundary. -/
inductive ChemistryImportFormat where
  | openSMILES
  | molfileV2000
  | molfileV3000
  | inChI
  | rdkitMol
  | rdkitJSON
  | rawMolecule
  deriving DecidableEq, Repr

namespace ChemistryImportFormat

/-- Human-readable format label. -/
def label : ChemistryImportFormat → String
  | openSMILES => "OpenSMILES"
  | molfileV2000 => "Molfile V2000"
  | molfileV3000 => "Molfile V3000"
  | inChI => "InChI"
  | rdkitMol => "RDKit Mol"
  | rdkitJSON => "RDKit JSON"
  | rawMolecule => "RawMolecule"

/-- Whether the current Lean tree has a direct string parser for this format. -/
def hasInternalStringParser : ChemistryImportFormat → Bool
  | openSMILES => true
  | _ => false

/-- Whether this format is expected to enter through an external adapter bridge. -/
def requiresExternalBridge (format : ChemistryImportFormat) : Bool :=
  !format.hasInternalStringParser && format ≠ rawMolecule

@[simp] theorem hasInternalStringParser_openSMILES :
    hasInternalStringParser openSMILES = true :=
  rfl

@[simp] theorem requiresExternalBridge_molfileV2000 :
    requiresExternalBridge molfileV2000 = true :=
  rfl

@[simp] theorem requiresExternalBridge_inChI :
    requiresExternalBridge inChI = true :=
  rfl

@[simp] theorem requiresExternalBridge_rdkitMol :
    requiresExternalBridge rdkitMol = true :=
  rfl

end ChemistryImportFormat

/-- Trust/provenance category for the import step. -/
inductive ChemistryImportTrust where
  | internalLeanParser
  | externalAdapter
  | externalToolkit
  | userSuppliedRawMolecule
  | proofCertifiedAdapter
  deriving DecidableEq, Repr

/-- Original source metadata retained with an imported molecule. -/
structure ChemistryImportSource where
  format : ChemistryImportFormat
  name? : Option String := none
  payloadHash? : Option String := none
  deriving DecidableEq, Repr

/-! ### Normalization policy -/

/-- Valence boundary: what Lean checks versus what is imported. -/
inductive ValenceNormalizationPolicy where
  | lightweightLeanCheck
  | trustExternalValence
  | skipValenceCheck
  deriving DecidableEq, Repr

/-- Aromaticity boundary. -/
inductive AromaticityNormalizationPolicy where
  | openSMILESDefaults
  | preserveInputFlags
  | trustExternalAromaticity
  | suppliedCandidateCycles
  deriving DecidableEq, Repr

/-- Resonance boundary. -/
inductive ResonanceNormalizationPolicy where
  | localizedInputGraph
  | recordAromaticDelocalization
  | trustExternalResonanceClass
  deriving DecidableEq, Repr

/-- Tautomer boundary. -/
inductive TautomerNormalizationPolicy where
  | fixedHydrogenOnly
  | fixedHydrogenWithMobileMetadata
  | trustExternalCanonicalTautomer
  deriving DecidableEq, Repr

/-- Stereochemical annotation boundary. -/
inductive StereobondNormalizationPolicy where
  | preserveInputAnnotations
  | trustExternalStereoPerception
  | ignoreInputStereo
  deriving DecidableEq, Repr

/-- Full declared normalization policy for an imported molecule. -/
structure ChemistryNormalizationPolicy where
  valence : ValenceNormalizationPolicy := ValenceNormalizationPolicy.lightweightLeanCheck
  aromaticity : AromaticityNormalizationPolicy := AromaticityNormalizationPolicy.openSMILESDefaults
  resonance : ResonanceNormalizationPolicy := ResonanceNormalizationPolicy.recordAromaticDelocalization
  tautomer : TautomerNormalizationPolicy := TautomerNormalizationPolicy.fixedHydrogenWithMobileMetadata
  stereobonds : StereobondNormalizationPolicy := StereobondNormalizationPolicy.preserveInputAnnotations
  deriving DecidableEq, Repr

namespace ChemistryNormalizationPolicy

/-- Default policy for the internal OpenSMILES path. -/
def openSMILESDefault : ChemistryNormalizationPolicy := {}

/-- Default policy for external molfile-style imports: preserve the localized input and require
explicit external claims for anything canonicalized upstream. -/
def externalLocalizedDefault : ChemistryNormalizationPolicy where
  valence := ValenceNormalizationPolicy.lightweightLeanCheck
  aromaticity := AromaticityNormalizationPolicy.preserveInputFlags
  resonance := ResonanceNormalizationPolicy.localizedInputGraph
  tautomer := TautomerNormalizationPolicy.fixedHydrogenOnly
  stereobonds := StereobondNormalizationPolicy.preserveInputAnnotations

/-- Default policy for toolkit-produced bridge packets, such as RDKit exports. -/
def toolkitBridgeDefault : ChemistryNormalizationPolicy where
  valence := ValenceNormalizationPolicy.lightweightLeanCheck
  aromaticity := AromaticityNormalizationPolicy.trustExternalAromaticity
  resonance := ResonanceNormalizationPolicy.trustExternalResonanceClass
  tautomer := TautomerNormalizationPolicy.fixedHydrogenWithMobileMetadata
  stereobonds := StereobondNormalizationPolicy.trustExternalStereoPerception

/-- Whether Lean is responsible for checking valence under this policy. -/
def leanChecksValence (policy : ChemistryNormalizationPolicy) : Bool :=
  policy.valence = ValenceNormalizationPolicy.lightweightLeanCheck

/-- Whether aromaticity is imported from an external source under this policy. -/
def importsAromaticity (policy : ChemistryNormalizationPolicy) : Bool :=
  policy.aromaticity = AromaticityNormalizationPolicy.trustExternalAromaticity

/-- Whether resonance canonicalization is imported from an external source under this policy. -/
def importsResonance (policy : ChemistryNormalizationPolicy) : Bool :=
  policy.resonance = ResonanceNormalizationPolicy.trustExternalResonanceClass

/-- Whether tautomer canonicalization is imported from an external source under this policy. -/
def importsTautomer (policy : ChemistryNormalizationPolicy) : Bool :=
  policy.tautomer = TautomerNormalizationPolicy.trustExternalCanonicalTautomer

@[simp] theorem openSMILESDefault_leanChecksValence :
    openSMILESDefault.leanChecksValence = true :=
  rfl

@[simp] theorem toolkitBridgeDefault_importsAromaticity :
    toolkitBridgeDefault.importsAromaticity = true :=
  rfl

@[simp] theorem toolkitBridgeDefault_importsResonance :
    toolkitBridgeDefault.importsResonance = true :=
  rfl

end ChemistryNormalizationPolicy

/-- A compact report of which boundaries are internal checks and which are external assumptions. -/
structure ChemistryNormalizationBoundaryReport where
  leanChecksValence : Bool
  importsAromaticity : Bool
  importsResonance : Bool
  importsTautomer : Bool
  preservesInputStereo : Bool
  deriving DecidableEq, Repr

namespace ChemistryNormalizationBoundaryReport

/-- Build a boundary report from a declared normalization policy. -/
def ofPolicy (policy : ChemistryNormalizationPolicy) : ChemistryNormalizationBoundaryReport where
  leanChecksValence := policy.leanChecksValence
  importsAromaticity := policy.importsAromaticity
  importsResonance := policy.importsResonance
  importsTautomer := policy.importsTautomer
  preservesInputStereo :=
    policy.stereobonds = StereobondNormalizationPolicy.preserveInputAnnotations

end ChemistryNormalizationBoundaryReport

/-! ### Import results and bridge packets -/

/-- Normalization result together with the policy/boundary report that produced it. -/
structure ChemistryPolicyNormalizationResult where
  policy : ChemistryNormalizationPolicy
  normalized : ChemistryNormalizationResult
  boundary : ChemistryNormalizationBoundaryReport

/-- Normalize a `RawMolecule` under an explicitly declared policy.

The current normalization functions are shared for every policy; the policy records the proof/trust
boundary for decisions whose production implementation may later be swapped out. -/
def normalizeRawMoleculeWithPolicy (policy : ChemistryNormalizationPolicy)
    (mol : RawMolecule) (cycles : List AromaticCycle := []) :
    ChemistryPolicyNormalizationResult where
  policy := policy
  normalized := normalizeRawMolecule mol cycles
  boundary := ChemistryNormalizationBoundaryReport.ofPolicy policy

/-- A packet supplied by an external parser/toolkit bridge.  The bridge has already decoded the
format into `RawMolecule`; Lean records the format, provenance, normalization policy, and optional
aromatic-cycle candidates before normalizing. -/
structure ExternalRawMoleculePacket where
  source : ChemistryImportSource
  trust : ChemistryImportTrust
  raw : RawMolecule
  policy : ChemistryNormalizationPolicy := ChemistryNormalizationPolicy.externalLocalizedDefault
  aromaticCycles : List AromaticCycle := []
  notes : List String := []
  deriving Repr

/-- Unified import result. -/
structure ChemistryImportResult where
  source : ChemistryImportSource
  trust : ChemistryImportTrust
  raw : RawMolecule
  normalized : ChemistryPolicyNormalizationResult
  notes : List String := []

/-- Import a predecoded external bridge packet. -/
def importExternalRawMoleculePacket (packet : ExternalRawMoleculePacket) :
    ChemistryImportResult where
  source := packet.source
  trust := packet.trust
  raw := packet.raw
  normalized := normalizeRawMoleculeWithPolicy packet.policy packet.raw packet.aromaticCycles
  notes := packet.notes

/-- Import errors at the string-adapter boundary. -/
inductive ChemistryImportError where
  | parserError (message : ParserError)
  | externalBridgeRequired (format : ChemistryImportFormat)
  | rawMoleculeRequiresPacket
  deriving DecidableEq, Repr

namespace ChemistryImportError

/-- Short diagnostic string. -/
def message : ChemistryImportError → String
  | parserError message => message
  | externalBridgeRequired format =>
      "external bridge required for " ++ format.label
  | rawMoleculeRequiresPacket =>
      "RawMolecule input must enter through an ExternalRawMoleculePacket"

end ChemistryImportError

/-- Parse a supported string format to `RawMolecule`.  At present only the internal OpenSMILES
parser is implemented in Lean; other formats must enter through `ExternalRawMoleculePacket`. -/
def parseImportStringAsRaw (format : ChemistryImportFormat) (input : String) :
    Except ChemistryImportError RawMolecule :=
  match format with
  | ChemistryImportFormat.openSMILES =>
      match parseOpenSMILES input with
      | Except.ok mol => Except.ok mol
      | Except.error error => Except.error (ChemistryImportError.parserError error)
  | ChemistryImportFormat.rawMolecule =>
      Except.error ChemistryImportError.rawMoleculeRequiresPacket
  | other => Except.error (ChemistryImportError.externalBridgeRequired other)

/-- Parse and normalize a supported string format under an explicit policy. -/
def importStringWithPolicy (format : ChemistryImportFormat) (input : String)
    (policy : ChemistryNormalizationPolicy := ChemistryNormalizationPolicy.openSMILESDefault)
    (cycles : List AromaticCycle := []) :
    Except ChemistryImportError ChemistryImportResult := do
  let raw ← parseImportStringAsRaw format input
  Except.ok
    { source := { format := format }
      trust := ChemistryImportTrust.internalLeanParser
      raw := raw
      normalized := normalizeRawMoleculeWithPolicy policy raw cycles }

/-- Convenience entry point for internal OpenSMILES import. -/
def importOpenSMILES (input : String) (cycles : List AromaticCycle := []) :
    Except ChemistryImportError ChemistryImportResult :=
  importStringWithPolicy ChemistryImportFormat.openSMILES input
    ChemistryNormalizationPolicy.openSMILESDefault cycles

/-- Build a molfile bridge packet after an external molfile adapter has decoded atoms/bonds. -/
def molfilePacket (raw : RawMolecule)
    (format : ChemistryImportFormat := ChemistryImportFormat.molfileV2000)
    (policy : ChemistryNormalizationPolicy := ChemistryNormalizationPolicy.externalLocalizedDefault)
    (cycles : List AromaticCycle := []) : ExternalRawMoleculePacket where
  source := { format := format }
  trust := ChemistryImportTrust.externalAdapter
  raw := raw
  policy := policy
  aromaticCycles := cycles

/-- Build an InChI bridge packet after an external InChI adapter has decoded a fixed-H graph. -/
def inChIPacket (raw : RawMolecule)
    (policy : ChemistryNormalizationPolicy := ChemistryNormalizationPolicy.externalLocalizedDefault) :
    ExternalRawMoleculePacket where
  source := { format := ChemistryImportFormat.inChI }
  trust := ChemistryImportTrust.externalAdapter
  raw := raw
  policy := policy
  notes := ["InChI adapter must declare whether this is mobile-H or Fixed-H input."]

/-- Build an RDKit bridge packet after RDKit has exported a molecule into `RawMolecule`. -/
def rdkitPacket (raw : RawMolecule)
    (policy : ChemistryNormalizationPolicy := ChemistryNormalizationPolicy.toolkitBridgeDefault)
    (cycles : List AromaticCycle := []) : ExternalRawMoleculePacket where
  source := { format := ChemistryImportFormat.rdkitMol }
  trust := ChemistryImportTrust.externalToolkit
  raw := raw
  policy := policy
  aromaticCycles := cycles

/-- Build a direct raw-molecule packet for tests, hand-authored molecules, or certified adapters. -/
def rawMoleculePacket (raw : RawMolecule)
    (trust : ChemistryImportTrust := ChemistryImportTrust.userSuppliedRawMolecule)
    (policy : ChemistryNormalizationPolicy := ChemistryNormalizationPolicy.externalLocalizedDefault)
    (cycles : List AromaticCycle := []) : ExternalRawMoleculePacket where
  source := { format := ChemistryImportFormat.rawMolecule }
  trust := trust
  raw := raw
  policy := policy
  aromaticCycles := cycles

/-! ### Small executable facts for the importer story -/

@[simp] theorem parseImportStringAsRaw_molfile_requires_bridge (input : String) :
    parseImportStringAsRaw ChemistryImportFormat.molfileV2000 input =
      Except.error (ChemistryImportError.externalBridgeRequired ChemistryImportFormat.molfileV2000) :=
  rfl

@[simp] theorem parseImportStringAsRaw_inChI_requires_bridge (input : String) :
    parseImportStringAsRaw ChemistryImportFormat.inChI input =
      Except.error (ChemistryImportError.externalBridgeRequired ChemistryImportFormat.inChI) :=
  rfl

@[simp] theorem parseImportStringAsRaw_rawMolecule_requires_packet (input : String) :
    parseImportStringAsRaw ChemistryImportFormat.rawMolecule input =
      Except.error ChemistryImportError.rawMoleculeRequiresPacket :=
  rfl

@[simp] theorem importExternalRawMoleculePacket_format (packet : ExternalRawMoleculePacket) :
    (importExternalRawMoleculePacket packet).source.format = packet.source.format :=
  rfl

@[simp] theorem importExternalRawMoleculePacket_policy (packet : ExternalRawMoleculePacket) :
    (importExternalRawMoleculePacket packet).normalized.policy = packet.policy :=
  rfl

end
end OneCenter
end TetraStereo
