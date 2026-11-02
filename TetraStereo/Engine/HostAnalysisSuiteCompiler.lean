import TetraStereo.Engine.HostClaimCompiler

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section

/-!
  Host analysis suite compiler.

  `HostOfficialStereoRequest` packages one molecule-shaped official-stereo query, and
  `HostStereoClaimRequest` packages broad theorem-family claims.  This module adds the first
  host-facing bundle layer: a typed suite can write all requested packages and a generated manifest
  theorem that imports and references every generated theorem in the bundle.
-/

/-- Kernel-reducible recognition of the generated Lean-source suffix. -/
def hasGeneratedLeanFileSuffix (fileName : String) : Bool :=
  match fileName.toList.reverse with
  | 'n' :: 'a' :: 'e' :: 'l' :: '.' :: _ => true
  | _ => false

/-- File stem used by Lean module imports for generated `.lean` basenames.

This matches the suffix structurally rather than through `String.endsWith`: the latter delegates to
an opaque byte-slice primitive, which prevents generated-shape checks from reducing in the kernel. -/
def generatedLeanFileStem (fileName : String) : String :=
  match fileName.toList.reverse with
  | 'n' :: 'a' :: 'e' :: 'l' :: '.' :: stemRev => String.ofList stemRev.reverse
  | _ => fileName

/-- Validate a generated file basename that must also be importable as a Lean module stem. -/
def validateImportableLeanFileName (label fileName : String) : Except String Unit := do
  validateGeneratedFileName label fileName
  requireHostRequestShape (hasGeneratedLeanFileSuffix fileName)
    (label ++ " must end in .lean for importable suite manifests: " ++ reprStr fileName)
  requireHostRequestShape (leanIdentifierSegment? (generatedLeanFileStem fileName))
    (label ++ " has a file stem that is not a Lean identifier: " ++ reprStr fileName)

/-- Fully qualified module name for a generated source file under a namespace path. -/
def generatedModuleName (namespacePath : List String) (fileName : String) : String :=
  leanQualifiedName namespacePath (generatedLeanFileStem fileName)

/-- Encode one host-facing key character into a collision-resistant Lean identifier fragment. -/
def leanIdentifierSlugChar (char : Char) : String :=
  if ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toList.contains char) then
    String.singleton char
  else
    "_x" ++ toString char.toNat ++ "_"

/-- Stable ASCII Lean-identifier suffix derived from host-facing keys.

The encoding keeps alphanumeric characters and escapes every other codepoint, including `_`, so
keys such as `a-b` and `a_b` cannot collapse to the same generated declaration names. -/
def leanIdentifierSlug (text : String) : String :=
  "k" ++ String.join (text.toList.map leanIdentifierSlugChar)

/-- Collision-resistant generated-name segment retaining the exact host-facing key encoding. -/
def compactGeneratedNameSegment (tag text : String) : String :=
  tag ++ leanIdentifierSlug text

/-- Whether a string list contains a duplicate value. -/
def hasDuplicateStrings : List String → Bool
  | [] => false
  | value :: rest => rest.contains value || hasDuplicateStrings rest

/-- Kernel-reducible prefix check for generated string literals. -/
def charListPrefix? : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | prefixHead :: prefixTail, textHead :: textTail =>
      (prefixHead == textHead) && charListPrefix? prefixTail textTail

/-- Kernel-reducible string prefix check for generated source validation. -/
def stringPrefix? (prefixText text : String) : Bool :=
  charListPrefix? prefixText.toList text.toList

/-- Whether a fully-qualified declaration name syntactically belongs to a module namespace. -/
def qualifiedNameInModule? (moduleName fullName : String) : Bool :=
  stringPrefix? (moduleName ++ ".") fullName

/-- Whether a list contains a value using propositional equality. -/
def listContainsByEquality {α : Type*} [DecidableEq α] (target : α) :
    List α → Bool
  | [] => false
  | value :: rest =>
      if value = target then true else listContainsByEquality target rest

/-- Remove duplicates while preserving the first occurrence of every value. -/
def deduplicateByEqualityAux {α : Type*} [DecidableEq α] (seen : List α) :
    List α → List α
  | [] => []
  | target :: rest =>
      if listContainsByEquality target seen then
        deduplicateByEqualityAux seen rest
      else
        target :: deduplicateByEqualityAux (target :: seen) rest

/-- Remove duplicates while preserving the first occurrence of every value. -/
def deduplicateByEquality {α : Type*} [DecidableEq α] (values : List α) : List α :=
  deduplicateByEqualityAux [] values

/-- Whether two string lists have any shared value. -/
def stringListsIntersect (left right : List String) : Bool :=
  left.any fun value => right.contains value

/-- Request-scoped canonical package key for a broad theorem-family claim. -/
def hostAnalysisClaimPackageKey (requestKey : String) (target : HostStereoClaimTarget) : String :=
  requestKey ++ "::" ++ target.defaultKey

/-- Molecule-specific stereochemical target families witnessed by generated analysis packages. -/
inductive HostMoleculeTargetWitnessKind where
  | noncenterDescriptor
  | graphRelation
  | conformerClaim
  | ensembleClaim
  deriving DecidableEq, Repr

namespace HostMoleculeTargetWitnessKind

/-- Host-facing label for a molecule-specific target witness kind. -/
def label : HostMoleculeTargetWitnessKind → String
  | noncenterDescriptor => "non-center descriptor target"
  | graphRelation => "graph-level relation target"
  | conformerClaim => "conformer claim target"
  | ensembleClaim => "ensemble claim target"

/-- Lean expression for this witness kind in generated source. -/
def expr : HostMoleculeTargetWitnessKind → String
  | noncenterDescriptor => "TetraStereo.Engine.HostMoleculeTargetWitnessKind.noncenterDescriptor"
  | graphRelation => "TetraStereo.Engine.HostMoleculeTargetWitnessKind.graphRelation"
  | conformerClaim => "TetraStereo.Engine.HostMoleculeTargetWitnessKind.conformerClaim"
  | ensembleClaim => "TetraStereo.Engine.HostMoleculeTargetWitnessKind.ensembleClaim"

end HostMoleculeTargetWitnessKind

/-- Coverage source counted by a molecule-specific target witness. -/
inductive HostMoleculeTargetCoverageField where
  | axial
  | planar
  | helical
  | alkene
  | cumulene
  | auxiliaryRule5
  | phantom
  | lonePair
  | multiCenterGraphRelation
  | graphClassifierSound
  | graphClassifierRefusal
  | conformer
  | ensemble
  deriving DecidableEq, Repr

namespace HostMoleculeTargetCoverageField

/-- Lean expression for this coverage field in generated source. -/
def expr : HostMoleculeTargetCoverageField → String
  | axial => "TetraStereo.Engine.HostMoleculeTargetCoverageField.axial"
  | planar => "TetraStereo.Engine.HostMoleculeTargetCoverageField.planar"
  | helical => "TetraStereo.Engine.HostMoleculeTargetCoverageField.helical"
  | alkene => "TetraStereo.Engine.HostMoleculeTargetCoverageField.alkene"
  | cumulene => "TetraStereo.Engine.HostMoleculeTargetCoverageField.cumulene"
  | auxiliaryRule5 => "TetraStereo.Engine.HostMoleculeTargetCoverageField.auxiliaryRule5"
  | phantom => "TetraStereo.Engine.HostMoleculeTargetCoverageField.phantom"
  | lonePair => "TetraStereo.Engine.HostMoleculeTargetCoverageField.lonePair"
  | multiCenterGraphRelation =>
      "TetraStereo.Engine.HostMoleculeTargetCoverageField.multiCenterGraphRelation"
  | graphClassifierSound =>
      "TetraStereo.Engine.HostMoleculeTargetCoverageField.graphClassifierSound"
  | graphClassifierRefusal =>
      "TetraStereo.Engine.HostMoleculeTargetCoverageField.graphClassifierRefusal"
  | conformer => "TetraStereo.Engine.HostMoleculeTargetCoverageField.conformer"
  | ensemble => "TetraStereo.Engine.HostMoleculeTargetCoverageField.ensemble"

/-- Projection name on `HostDetectorCoverage` corresponding to this coverage field. -/
def coverageProjection : HostMoleculeTargetCoverageField → String
  | axial => "axes"
  | planar => "planes"
  | helical => "helices"
  | alkene => "assignedDoubleBonds"
  | cumulene => "cumulenes"
  | auxiliaryRule5 => "auxiliaryRule5Nodes"
  | phantom => "phantomNodes"
  | lonePair => "lonePairNodes"
  | multiCenterGraphRelation => "graphResultCenterCount"
  | graphClassifierSound => "graphResultCenterCount"
  | graphClassifierRefusal => "graphResultCenterCount"
  | conformer => "conformations"
  | ensemble => "ensembles"

/-- Coverage recomputation expression for generated witness source. -/
def countExpr (field : HostMoleculeTargetCoverageField)
    (packetExpr annotationsExpr : String) : String :=
  match field with
  | multiCenterGraphRelation =>
      "TetraStereo.Engine.HostMoleculeGraphResult.detectedTetrahedralCenterCount " ++
        packetExpr
  | graphClassifierSound =>
      "TetraStereo.Engine.HostMoleculeGraphResult.detectedTetrahedralCenterCount " ++
        packetExpr
  | graphClassifierRefusal =>
      "TetraStereo.Engine.HostMoleculeGraphResult.detectedTetrahedralCenterCount " ++
        packetExpr
  | _ =>
      "(TetraStereo.Engine.HostDetectorCoverage.ofPacketAndAnnotations " ++
        packetExpr ++ " " ++ annotationsExpr ++ ")." ++ field.coverageProjection

/-- The broad theorem-family claims required by this coverage field. -/
def requiredClaimTargets : HostMoleculeTargetCoverageField → List HostStereoClaimTarget
  | axial => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | planar => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | helical => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | alkene => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | cumulene => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | auxiliaryRule5 => [HostStereoClaimTarget.officialCIPAssignmentSuccessResolved]
  | phantom => [HostStereoClaimTarget.officialCIPAssignmentSuccessResolved]
  | lonePair => [HostStereoClaimTarget.officialCIPAssignmentSuccessResolved]
  | multiCenterGraphRelation => [HostStereoClaimTarget.multiCenterCipRSClassificationExactlyOne]
  | graphClassifierSound => [HostStereoClaimTarget.graphDescriptorClassifierSound]
  | graphClassifierRefusal => [HostStereoClaimTarget.graphDescriptorClassifierRefusesUnresolved]
  | conformer => [HostStereoClaimTarget.conformationalProfileChiralRefutesAchiral]
  | ensemble => [HostStereoClaimTarget.descriptorChiralEnsembleRefutesAchiral]

/-- Stable package-key segment for this coverage field. -/
def packageKeySegment : HostMoleculeTargetCoverageField → String
  | axial => "axial"
  | planar => "planar"
  | helical => "helical"
  | alkene => "alkene"
  | cumulene => "cumulene"
  | auxiliaryRule5 => "auxiliary-rule5"
  | phantom => "phantom"
  | lonePair => "lone-pair"
  | multiCenterGraphRelation => "multi-center-graph-relation"
  | graphClassifierSound => "graph-classifier-sound"
  | graphClassifierRefusal => "graph-classifier-refusal"
  | conformer => "conformer"
  | ensemble => "ensemble"

/-- Host-facing label expected for witnesses over this coverage field. -/
def expectedTargetLabel : HostMoleculeTargetCoverageField → String
  | axial => "axial descriptor"
  | planar => "planar descriptor"
  | helical => "helical descriptor"
  | alkene => "assigned alkene E/Z descriptor"
  | cumulene => "cumulene path candidate"
  | auxiliaryRule5 => "auxiliary Rule-5 node"
  | phantom => "phantom node"
  | lonePair => "lone-pair node"
  | multiCenterGraphRelation => "multi-center CIP R/S exactly-one classification"
  | graphClassifierSound => "graph descriptor classifier soundness"
  | graphClassifierRefusal => "graph descriptor classifier unresolved-priority refusal"
  | conformer => "profile chirality refutes conformer achirality"
  | ensemble => "descriptor-chiral ensemble refutes descriptor achirality"

/-- Witness kind expected for this coverage field. -/
def expectedKind : HostMoleculeTargetCoverageField → HostMoleculeTargetWitnessKind
  | conformer => HostMoleculeTargetWitnessKind.conformerClaim
  | ensemble => HostMoleculeTargetWitnessKind.ensembleClaim
  | multiCenterGraphRelation => HostMoleculeTargetWitnessKind.graphRelation
  | graphClassifierSound => HostMoleculeTargetWitnessKind.graphRelation
  | graphClassifierRefusal => HostMoleculeTargetWitnessKind.graphRelation
  | axial => HostMoleculeTargetWitnessKind.noncenterDescriptor
  | planar => HostMoleculeTargetWitnessKind.noncenterDescriptor
  | helical => HostMoleculeTargetWitnessKind.noncenterDescriptor
  | alkene => HostMoleculeTargetWitnessKind.noncenterDescriptor
  | cumulene => HostMoleculeTargetWitnessKind.noncenterDescriptor
  | auxiliaryRule5 => HostMoleculeTargetWitnessKind.noncenterDescriptor
  | phantom => HostMoleculeTargetWitnessKind.noncenterDescriptor
  | lonePair => HostMoleculeTargetWitnessKind.noncenterDescriptor

/-- Compact generated-name segment for this coverage field. -/
def nameSuffixSegment : HostMoleculeTargetCoverageField → String
  | axial => "Ax"
  | planar => "Pl"
  | helical => "He"
  | alkene => "Db"
  | cumulene => "Cu"
  | auxiliaryRule5 => "Aux"
  | phantom => "Ph"
  | lonePair => "Lp"
  | multiCenterGraphRelation => "McGraph"
  | graphClassifierSound => "GraphSound"
  | graphClassifierRefusal => "GraphRefuse"
  | conformer => "Conf"
  | ensemble => "Ens"

end HostMoleculeTargetCoverageField

namespace HostMoleculeGraphResult

/-- Deduplicated neighbor indices for one raw atom index. -/
def rawNeighborIndices (raw : RawMolecule) (idx : ℕ) : List ℕ :=
  deduplicateByEquality <|
    raw.bonds.filterMap fun bond =>
      if bond.source == idx then
        some bond.target
      else if bond.target == idx then
        some bond.source
      else
        none

/-- Raw bonds incident to one atom index. -/
def rawIncidentBonds (raw : RawMolecule) (idx : ℕ) : List RawBond :=
  raw.bonds.filter fun bond => bond.source == idx || bond.target == idx

/-- Bond kinds that can participate in a tetrahedral graph-center source witness. -/
def tetrahedralCenterBondKindCompatible : ParsedBondKind → Bool
  | ParsedBondKind.unspecified => true
  | ParsedBondKind.single => true
  | ParsedBondKind.up => true
  | ParsedBondKind.down => true
  | ParsedBondKind.double => false
  | ParsedBondKind.triple => false
  | ParsedBondKind.aromatic => false

/-- Whether a raw atom index is perceived as a tetrahedral graph center by the host boundary.

This is intentionally still a source/evidence predicate, not a full official-CIP resolution claim:
it requires four distinct neighbors and exactly four incident tetrahedral-compatible bond records,
and the generated graph-result theorem separately certifies the graph theorem family. -/
def rawTetrahedralCenterDetected (raw : RawMolecule) (idx : ℕ) : Bool :=
  let incident := rawIncidentBonds raw idx
  decide (idx < raw.atomCount) &&
    decide ((rawNeighborIndices raw idx).length = 4) &&
      decide (incident.length = 4) &&
        incident.all fun bond => tetrahedralCenterBondKindCompatible bond.kind

/-- Raw atom indices perceived as tetrahedral graph centers. -/
def detectedTetrahedralCenterIndices (packet : ExternalRawMoleculePacket) : List ℕ :=
  (List.range packet.raw.atomCount).filter (rawTetrahedralCenterDetected packet.raw)

/-- Count perceived tetrahedral graph centers in the host molecule source. -/
def detectedTetrahedralCenterCount (packet : ExternalRawMoleculePacket) : ℕ :=
  (detectedTetrahedralCenterIndices packet).length

end HostMoleculeGraphResult

/-- Typed graph-result theorem family bound to a generated molecule-specific graph target. -/
inductive HostMoleculeGraphResultEvidenceKind where
  | multiCenterExactlyOne
  | descriptorClassifierSound
  | descriptorClassifierRefusal
  deriving DecidableEq, Repr

namespace HostMoleculeGraphResultEvidenceKind

/-- Lean expression for this graph-result evidence kind. -/
def expr : HostMoleculeGraphResultEvidenceKind → String
  | multiCenterExactlyOne =>
      "TetraStereo.Engine.HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne"
  | descriptorClassifierSound =>
      "TetraStereo.Engine.HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound"
  | descriptorClassifierRefusal =>
      "TetraStereo.Engine.HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal"

/-- Coverage field authenticated by this graph-result evidence kind. -/
def coverageField : HostMoleculeGraphResultEvidenceKind → HostMoleculeTargetCoverageField
  | multiCenterExactlyOne => HostMoleculeTargetCoverageField.multiCenterGraphRelation
  | descriptorClassifierSound => HostMoleculeTargetCoverageField.graphClassifierSound
  | descriptorClassifierRefusal => HostMoleculeTargetCoverageField.graphClassifierRefusal

/-- Stable package-key segment for this graph-result evidence kind. -/
def keySegment : HostMoleculeGraphResultEvidenceKind → String
  | multiCenterExactlyOne => "multi-center-exactly-one"
  | descriptorClassifierSound => "descriptor-classifier-sound"
  | descriptorClassifierRefusal => "descriptor-classifier-refusal"

/-- Compact generated-name segment for this graph-result evidence kind. -/
def nameSuffixSegment : HostMoleculeGraphResultEvidenceKind → String
  | multiCenterExactlyOne => "GraphExact"
  | descriptorClassifierSound => "GraphSoundResult"
  | descriptorClassifierRefusal => "GraphRefusalResult"

end HostMoleculeGraphResultEvidenceKind

/-- Configuration-pair policy used by generated graph-result certificates. -/
inductive HostMoleculeGraphConfigurationPolicy where
  | identityMirror
  | identitySelf
  deriving DecidableEq, Repr

namespace HostMoleculeGraphConfigurationPolicy

/-- Lean expression for this generated graph-configuration policy. -/
def expr : HostMoleculeGraphConfigurationPolicy → String
  | identityMirror =>
      "TetraStereo.Engine.HostMoleculeGraphConfigurationPolicy.identityMirror"
  | identitySelf =>
      "TetraStereo.Engine.HostMoleculeGraphConfigurationPolicy.identitySelf"

/-- Stable package-key segment for this graph-configuration policy. -/
def keySegment : HostMoleculeGraphConfigurationPolicy → String
  | identityMirror => "identity-mirror"
  | identitySelf => "identity-self"

/-- Compact generated-name segment for this graph-configuration policy. -/
def nameSuffixSegment : HostMoleculeGraphConfigurationPolicy → String
  | identityMirror => "Mirror"
  | identitySelf => "Self"

end HostMoleculeGraphConfigurationPolicy

/-- Additional proposition required before a generated graph target may claim a concrete outcome. -/
inductive HostMoleculeGraphOutcomePrecondition where
  | none
  | descriptorMesoLeft
  | descriptorChiralLeft
  deriving DecidableEq, Repr

namespace HostMoleculeGraphOutcomePrecondition

/-- Lean expression for this graph-outcome precondition. -/
def expr : HostMoleculeGraphOutcomePrecondition → String
  | none => "TetraStereo.Engine.HostMoleculeGraphOutcomePrecondition.none"
  | descriptorMesoLeft =>
      "TetraStereo.Engine.HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft"
  | descriptorChiralLeft =>
      "TetraStereo.Engine.HostMoleculeGraphOutcomePrecondition.descriptorChiralLeft"

/-- Stable package-key segment for this graph-outcome precondition. -/
def keySegment : HostMoleculeGraphOutcomePrecondition → String
  | none => "none"
  | descriptorMesoLeft => "descriptor-meso-left"
  | descriptorChiralLeft => "descriptor-chiral-left"

/-- Compact generated-name segment for this graph-outcome precondition. -/
def nameSuffixSegment : HostMoleculeGraphOutcomePrecondition → String
  | none => "Unconditional"
  | descriptorMesoLeft => "IfMeso"
  | descriptorChiralLeft => "IfChiral"

end HostMoleculeGraphOutcomePrecondition

namespace HostMoleculeTargetCoverageField

/-- Graph-result evidence kind required by graph-level coverage fields. -/
def graphResultKind? : HostMoleculeTargetCoverageField →
    Option HostMoleculeGraphResultEvidenceKind
  | multiCenterGraphRelation => some HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne
  | graphClassifierSound => some HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound
  | graphClassifierRefusal => some HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal
  | axial => none
  | planar => none
  | helical => none
  | alkene => none
  | cumulene => none
  | auxiliaryRule5 => none
  | phantom => none
  | lonePair => none
  | conformer => none
  | ensemble => none

/-- Whether this coverage field must bind a molecule-specialized graph theorem-family theorem. -/
def requiresGraphResult (field : HostMoleculeTargetCoverageField) : Bool :=
  field.graphResultKind?.isSome

end HostMoleculeTargetCoverageField

/-- Source-unit identity for exact descriptor/result evidence.

These keys are intentionally separate from user-facing target names: result-bound target
certificates should authenticate a particular detector/source unit, not just an aggregate count
somewhere in the molecule. -/
inductive HostMoleculeDescriptorSourceKey where
  | axial (axisStart axisEnd startHigh startLow endHigh endLow : ℕ)
  | planar (planeAtoms : List ℕ) (pilotAtom highReference lowReference : ℕ)
  | helical (helixPath : List ℕ) (frontReference backReference : ℕ)
  | alkene (left right : ℕ)
  | auxiliaryRule5 (anchor : ℕ) (support : List ℕ) (rootDistance? : Option ℕ)
  | conformer (stateId : String) (support : List ℕ)
  | ensemble (stateId : String) (support : List ℕ)
  deriving DecidableEq, Repr

namespace HostMoleculeDescriptorSourceKey

/-- Sorted duplicate-free natural-number support list used for unordered source supports. -/
def canonicalNatSetList (values : List ℕ) : List ℕ :=
  let sorted := values.mergeSort (fun left right => decide (left ≤ right))
  sorted.eraseDups

/-- Remove one atom index from a source-support list. -/
def removeNat (target : ℕ) : List ℕ → List ℕ
  | [] => []
  | value :: rest =>
      if value = target then
        removeNat target rest
      else
        value :: removeNat target rest

/-- Canonical auxiliary/virtual-node support excludes the anchor and forgets input ordering. -/
def canonicalVirtualSupportList (anchor : ℕ) (support : List ℕ) : List ℕ :=
  removeNat anchor (canonicalNatSetList support)

/-- Boolean membership test for natural-number source supports. -/
def natListContains (target : ℕ) : List ℕ → Bool
  | [] => false
  | value :: rest => decide (value = target) || natListContains target rest

/-- Boolean check that a natural-number support list is strictly ascending. -/
def strictlyAscendingNatList : List ℕ → Bool
  | [] => true
  | [_] => true
  | left :: right :: rest =>
      decide (left < right) && strictlyAscendingNatList (right :: rest)

/-- Canonical representative for source keys with unordered endpoint/support components. -/
def canonical : HostMoleculeDescriptorSourceKey → HostMoleculeDescriptorSourceKey
  | axial axisStart axisEnd startHigh startLow endHigh endLow =>
      axial axisStart axisEnd startHigh startLow endHigh endLow
  | planar planeAtoms pilotAtom highReference lowReference =>
      planar planeAtoms pilotAtom highReference lowReference
  | helical helixPath frontReference backReference =>
      helical helixPath frontReference backReference
  | alkene left right =>
      if left ≤ right then alkene left right else alkene right left
  | auxiliaryRule5 anchor support rootDistance? =>
      auxiliaryRule5 anchor (canonicalVirtualSupportList anchor support) rootDistance?
  | conformer stateId support =>
      conformer stateId (canonicalNatSetList support)
  | ensemble stateId support =>
      ensemble stateId (canonicalNatSetList support)

/-- Whether this source key is already in its canonical public representative form. -/
def isCanonical : HostMoleculeDescriptorSourceKey → Bool
  | axial .. => true
  | planar .. => true
  | helical .. => true
  | alkene left right => decide (left ≤ right)
  | auxiliaryRule5 anchor support _ =>
      strictlyAscendingNatList support && !natListContains anchor support
  | conformer _ support => strictlyAscendingNatList support
  | ensemble _ support => strictlyAscendingNatList support

/-- Coverage family associated with this exact source-unit key. -/
def coverageField : HostMoleculeDescriptorSourceKey → HostMoleculeTargetCoverageField
  | axial .. => HostMoleculeTargetCoverageField.axial
  | planar .. => HostMoleculeTargetCoverageField.planar
  | helical .. => HostMoleculeTargetCoverageField.helical
  | alkene .. => HostMoleculeTargetCoverageField.alkene
  | auxiliaryRule5 .. => HostMoleculeTargetCoverageField.auxiliaryRule5
  | conformer .. => HostMoleculeTargetCoverageField.conformer
  | ensemble .. => HostMoleculeTargetCoverageField.ensemble

/-- Compact numeric list segment for package-key-safe source keys. -/
def natListSegment (values : List ℕ) : String :=
  match values with
  | [] => "none"
  | _ => String.intercalate "-" (values.map fun value => "a" ++ toString value)

/-- Compact optional root-distance segment for package-key-safe source keys. -/
def natOptionSegment : Option ℕ → String
  | none => "root-none"
  | some value => "root-a" ++ toString value

/-- Alphanumeric-only slug character for generated Lean declaration suffixes. -/
def leanNameSlugChar (char : Char) : String :=
  if ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toList.contains char) then
    String.singleton char
  else
    "X" ++ toString char.toNat ++ "X"

/-- Alphanumeric-only slug for generated Lean declaration suffixes. -/
def leanNameSlug (text : String) : String :=
  "K" ++ String.join (text.toList.map leanNameSlugChar)

/-- Compact natural-number list segment for generated Lean declaration suffixes. -/
def natListNameSegment (values : List ℕ) : String :=
  match values with
  | [] => "LNone"
  | _ => "L" ++ String.intercalate "N" (values.map fun value => "A" ++ toString value)

/-- Compact optional root-distance segment for generated Lean declaration suffixes. -/
def natOptionNameSegment : Option ℕ → String
  | none => "RN"
  | some value => "R" ++ toString value

/-- Compact Lean-identifier-safe source key segment for generated declaration/file names. -/
def nameSuffixSegment : HostMoleculeDescriptorSourceKey → String
  | axial axisStart axisEnd startHigh startLow endHigh endLow =>
      "SrcAx" ++ natListNameSegment [axisStart, axisEnd, startHigh, startLow, endHigh, endLow]
  | planar planeAtoms pilotAtom highReference lowReference =>
      "SrcPl" ++ natListNameSegment (planeAtoms ++ [pilotAtom, highReference, lowReference])
  | helical helixPath frontReference backReference =>
      "SrcHe" ++ natListNameSegment (helixPath ++ [frontReference, backReference])
  | alkene left right => "SrcDb" ++ natListNameSegment [left, right]
  | auxiliaryRule5 anchor support rootDistance? =>
      "SrcAux" ++ natListNameSegment (anchor :: support) ++ natOptionNameSegment rootDistance?
  | conformer stateId support =>
      "SrcConf" ++ compactGeneratedNameSegment "Id" stateId ++ natListNameSegment support
  | ensemble stateId support =>
      "SrcEns" ++ compactGeneratedNameSegment "Id" stateId ++ natListNameSegment support

/-- Package-key-safe segment for this exact source-unit key. -/
def keySegment : HostMoleculeDescriptorSourceKey → String
  | axial axisStart axisEnd startHigh startLow endHigh endLow =>
      "source-axial-" ++ natListSegment [axisStart, axisEnd, startHigh, startLow, endHigh, endLow]
  | planar planeAtoms pilotAtom highReference lowReference =>
      "source-planar-" ++ natListSegment (planeAtoms ++ [pilotAtom, highReference, lowReference])
  | helical helixPath frontReference backReference =>
      "source-helical-" ++ natListSegment (helixPath ++ [frontReference, backReference])
  | alkene left right => "source-alkene-" ++ natListSegment [left, right]
  | auxiliaryRule5 anchor support rootDistance? =>
      "source-auxiliary-rule5-" ++ natListSegment (anchor :: support) ++ "-" ++
        natOptionSegment rootDistance?
  | conformer stateId support =>
      "source-conformer-" ++ leanIdentifierSlug stateId ++ "-" ++ natListSegment support
  | ensemble stateId support =>
      "source-ensemble-" ++ leanIdentifierSlug stateId ++ "-" ++ natListSegment support

/-- Render an optional natural number as Lean source. -/
def natOptionExpr : Option ℕ → String
  | none => "none"
  | some value => "some " ++ toString value

/-- Render an exact source-unit key as Lean source. -/
def expr : HostMoleculeDescriptorSourceKey → String
  | axial axisStart axisEnd startHigh startLow endHigh endLow =>
      "TetraStereo.Engine.HostMoleculeDescriptorSourceKey.axial " ++
        String.intercalate " " (List.map toString [axisStart, axisEnd, startHigh, startLow, endHigh, endLow])
  | planar planeAtoms pilotAtom highReference lowReference =>
      "TetraStereo.Engine.HostMoleculeDescriptorSourceKey.planar " ++
        leanNatListExpr planeAtoms ++ " " ++ toString pilotAtom ++ " " ++
        toString highReference ++ " " ++ toString lowReference
  | helical helixPath frontReference backReference =>
      "TetraStereo.Engine.HostMoleculeDescriptorSourceKey.helical " ++
        leanNatListExpr helixPath ++ " " ++ toString frontReference ++ " " ++
        toString backReference
  | alkene left right =>
      "TetraStereo.Engine.HostMoleculeDescriptorSourceKey.alkene " ++ toString left ++ " " ++
        toString right
  | auxiliaryRule5 anchor support rootDistance? =>
      "TetraStereo.Engine.HostMoleculeDescriptorSourceKey.auxiliaryRule5 " ++
        toString anchor ++ " " ++ leanNatListExpr support ++ " (" ++
        natOptionExpr rootDistance? ++ ")"
  | conformer stateId support =>
      "TetraStereo.Engine.HostMoleculeDescriptorSourceKey.conformer " ++
        leanStringLit stateId ++ " " ++ leanNatListExpr support
  | ensemble stateId support =>
      "TetraStereo.Engine.HostMoleculeDescriptorSourceKey.ensemble " ++
        leanStringLit stateId ++ " " ++ leanNatListExpr support

end HostMoleculeDescriptorSourceKey

/-- Exact descriptor/result values that can be authenticated against host-visible typed evidence.

This is deliberately narrower than coverage: a cumulene candidate, phantom node, or lone-pair node
can be covered without yet carrying a descriptor value.  Descriptor-result certificates are emitted
only for target families whose importer annotations or normalized stereobond semantics expose an
actual typed descriptor/kind value. -/
inductive HostMoleculeDescriptorResult where
  | axial (descriptor : AxialDescriptor)
  | planar (descriptor : PlanarDescriptor)
  | helical (descriptor : HelicalDescriptor)
  | alkene (descriptor : DoubleBondStereo)
  | auxiliaryRule5 (descriptor : OfficialRule5Descriptor)
  | conformerKind (kind : OfficialStereogenicUnitKind)
  | ensembleKind (kind : OfficialStereogenicUnitKind)
  deriving DecidableEq, Repr

namespace HostMoleculeDescriptorResult

/-- Coverage field whose source list should contain this descriptor result. -/
def coverageField : HostMoleculeDescriptorResult → HostMoleculeTargetCoverageField
  | axial _ => HostMoleculeTargetCoverageField.axial
  | planar _ => HostMoleculeTargetCoverageField.planar
  | helical _ => HostMoleculeTargetCoverageField.helical
  | alkene _ => HostMoleculeTargetCoverageField.alkene
  | auxiliaryRule5 _ => HostMoleculeTargetCoverageField.auxiliaryRule5
  | conformerKind _ => HostMoleculeTargetCoverageField.conformer
  | ensembleKind _ => HostMoleculeTargetCoverageField.ensemble

/-- Whether the result value is a descriptor the engine is willing to certify as assigned. -/
def assigned : HostMoleculeDescriptorResult → Bool
  | alkene DoubleBondStereo.unspecified => false
  | auxiliaryRule5 descriptor => descriptor.auxiliary
  | conformerKind kind => kind = OfficialStereogenicUnitKind.chiral
  | ensembleKind kind => kind = OfficialStereogenicUnitKind.chiral
  | _ => true

/-- Human-readable descriptor/result label. -/
def label : HostMoleculeDescriptorResult → String
  | axial AxialDescriptor.Ra => "axial R_a descriptor"
  | axial AxialDescriptor.Sa => "axial S_a descriptor"
  | planar PlanarDescriptor.Rp => "planar R_p descriptor"
  | planar PlanarDescriptor.Sp => "planar S_p descriptor"
  | helical HelicalDescriptor.P => "helical P descriptor"
  | helical HelicalDescriptor.M => "helical M descriptor"
  | alkene DoubleBondStereo.E => "alkene E descriptor"
  | alkene DoubleBondStereo.Z => "alkene Z descriptor"
  | alkene DoubleBondStereo.unspecified => "unassigned alkene descriptor"
  | auxiliaryRule5 descriptor =>
      "auxiliary Rule-5 descriptor " ++ reprStr descriptor
  | conformerKind OfficialStereogenicUnitKind.chiral => "chiral conformer kind"
  | conformerKind OfficialStereogenicUnitKind.pseudoasymmetric =>
      "pseudoasymmetric conformer kind"
  | conformerKind OfficialStereogenicUnitKind.nonstereogenic => "nonstereogenic conformer kind"
  | ensembleKind OfficialStereogenicUnitKind.chiral => "descriptor-chiral ensemble kind"
  | ensembleKind OfficialStereogenicUnitKind.pseudoasymmetric =>
      "pseudoasymmetric ensemble kind"
  | ensembleKind OfficialStereogenicUnitKind.nonstereogenic => "nonstereogenic ensemble kind"

/-- Package-key-safe segment for an official Rule-5 descriptor. -/
def officialRule5DescriptorKeySegment (descriptor : OfficialRule5Descriptor) : String :=
  let kind :=
    match descriptor.kind with
    | OfficialRule5DescriptorKind.tetrahedralCenter => "tetrahedral-center"
    | OfficialRule5DescriptorKind.axisOrPlane => "axis-or-plane"
    | OfficialRule5DescriptorKind.doubleBondOrCumulene => "double-bond-or-cumulene"
  let sense :=
    match descriptor.sense with
    | OfficialDescriptorSense.senior => "senior"
    | OfficialDescriptorSense.junior => "junior"
  (if descriptor.auxiliary then "auxiliary-" else "") ++ kind ++ "-" ++ sense

/-- Package-key-safe segment for this exact descriptor result. -/
def keySegment : HostMoleculeDescriptorResult → String
  | axial AxialDescriptor.Ra => "axial-Ra"
  | axial AxialDescriptor.Sa => "axial-Sa"
  | planar PlanarDescriptor.Rp => "planar-Rp"
  | planar PlanarDescriptor.Sp => "planar-Sp"
  | helical HelicalDescriptor.P => "helical-P"
  | helical HelicalDescriptor.M => "helical-M"
  | alkene DoubleBondStereo.E => "alkene-E"
  | alkene DoubleBondStereo.Z => "alkene-Z"
  | alkene DoubleBondStereo.unspecified => "alkene-unspecified"
  | auxiliaryRule5 descriptor => "auxiliary-rule5-" ++ officialRule5DescriptorKeySegment descriptor
  | conformerKind OfficialStereogenicUnitKind.chiral => "conformer-kind-chiral"
  | conformerKind OfficialStereogenicUnitKind.pseudoasymmetric =>
      "conformer-kind-pseudoasymmetric"
  | conformerKind OfficialStereogenicUnitKind.nonstereogenic =>
      "conformer-kind-nonstereogenic"
  | ensembleKind OfficialStereogenicUnitKind.chiral => "ensemble-kind-chiral"
  | ensembleKind OfficialStereogenicUnitKind.pseudoasymmetric =>
      "ensemble-kind-pseudoasymmetric"
  | ensembleKind OfficialStereogenicUnitKind.nonstereogenic =>
      "ensemble-kind-nonstereogenic"

/-- Compact generated-name segment for this exact descriptor result. -/
def nameSuffixSegment : HostMoleculeDescriptorResult → String
  | axial AxialDescriptor.Ra => "ResAxRa"
  | axial AxialDescriptor.Sa => "ResAxSa"
  | planar PlanarDescriptor.Rp => "ResPlRp"
  | planar PlanarDescriptor.Sp => "ResPlSp"
  | helical HelicalDescriptor.P => "ResHeP"
  | helical HelicalDescriptor.M => "ResHeM"
  | alkene DoubleBondStereo.E => "ResDbE"
  | alkene DoubleBondStereo.Z => "ResDbZ"
  | alkene DoubleBondStereo.unspecified => "ResDbUn"
  | auxiliaryRule5 descriptor =>
      "ResAux" ++ compactGeneratedNameSegment "D" (officialRule5DescriptorKeySegment descriptor)
  | conformerKind OfficialStereogenicUnitKind.chiral => "ResConfCh"
  | conformerKind OfficialStereogenicUnitKind.pseudoasymmetric => "ResConfPs"
  | conformerKind OfficialStereogenicUnitKind.nonstereogenic => "ResConfNs"
  | ensembleKind OfficialStereogenicUnitKind.chiral => "ResEnsCh"
  | ensembleKind OfficialStereogenicUnitKind.pseudoasymmetric => "ResEnsPs"
  | ensembleKind OfficialStereogenicUnitKind.nonstereogenic => "ResEnsNs"

/-- Render an exact descriptor result as Lean source. -/
def expr : HostMoleculeDescriptorResult → String
  | axial descriptor =>
      "TetraStereo.Engine.HostMoleculeDescriptorResult.axial " ++
        HostLeanExpr.AxialDescriptor.expr descriptor
  | planar descriptor =>
      "TetraStereo.Engine.HostMoleculeDescriptorResult.planar " ++
        HostLeanExpr.PlanarDescriptor.expr descriptor
  | helical descriptor =>
      "TetraStereo.Engine.HostMoleculeDescriptorResult.helical " ++
        HostLeanExpr.HelicalDescriptor.expr descriptor
  | alkene descriptor =>
      "TetraStereo.Engine.HostMoleculeDescriptorResult.alkene " ++
        HostLeanExpr.DoubleBondStereo.expr descriptor
  | auxiliaryRule5 descriptor =>
      "TetraStereo.Engine.HostMoleculeDescriptorResult.auxiliaryRule5 (" ++
        HostLeanExpr.OfficialRule5Descriptor.expr descriptor ++ ")"
  | conformerKind kind =>
      "TetraStereo.Engine.HostMoleculeDescriptorResult.conformerKind " ++
        HostLeanExpr.OfficialStereogenicUnitKind.expr kind
  | ensembleKind kind =>
      "TetraStereo.Engine.HostMoleculeDescriptorResult.ensembleKind " ++
        HostLeanExpr.OfficialStereogenicUnitKind.expr kind

/-- Source recomputation expression for the exact descriptor-result count.

The executable implementation of `sourceCount` lives in `HostAnalysisRequestBuilder`; generated
target modules import that layer, while this lower suite compiler only needs to render the call. -/
def countExpr (result : HostMoleculeDescriptorResult)
    (packetExpr annotationsExpr : String) : String :=
  "(" ++ result.expr ++ ").sourceCount " ++ packetExpr ++ " " ++ annotationsExpr

/-- Whether a source-unit key belongs to this descriptor result's coverage family. -/
def compatibleSourceKey (result : HostMoleculeDescriptorResult)
    (sourceKey : HostMoleculeDescriptorSourceKey) : Bool :=
  decide (sourceKey.coverageField = result.coverageField)

/-- Source recomputation expression for an exact descriptor-result count at one source key. -/
def countForSourceKeyExpr (result : HostMoleculeDescriptorResult)
    (sourceKey : HostMoleculeDescriptorSourceKey) (packetExpr annotationsExpr : String) : String :=
  "(" ++ result.expr ++ ").sourceCountForKey (" ++ sourceKey.expr ++ ") " ++
    packetExpr ++ " " ++ annotationsExpr

end HostMoleculeDescriptorResult

/-- Descriptor-result evidence carried by a molecule-specific target witness. -/
structure HostMoleculeDescriptorResultEvidence where
  result : HostMoleculeDescriptorResult
  sourceKey : HostMoleculeDescriptorSourceKey
  matchedCount : ℕ := 0
  requiredCount : ℕ := 1
  resultChecked : Bool := false
  deriving DecidableEq, Repr

namespace HostMoleculeDescriptorResultEvidence

/-- Executable readiness predicate for exact descriptor-result evidence. -/
def readyFor (evidence : HostMoleculeDescriptorResultEvidence)
    (coverageField : HostMoleculeTargetCoverageField) (observedCount : ℕ) : Bool :=
  evidence.resultChecked &&
    evidence.result.assigned &&
      evidence.sourceKey.isCanonical &&
        decide (evidence.result.coverageField = coverageField) &&
          evidence.result.compatibleSourceKey evidence.sourceKey &&
            decide (evidence.requiredCount > 0) &&
              decide (evidence.matchedCount ≥ evidence.requiredCount) &&
                decide (evidence.matchedCount ≤ observedCount)

/-- Render exact descriptor-result evidence as Lean source. -/
def expr (evidence : HostMoleculeDescriptorResultEvidence) : String :=
  "some { result := " ++ evidence.result.expr ++
    ", sourceKey := " ++ evidence.sourceKey.expr ++
    ", matchedCount := " ++ toString evidence.matchedCount ++
    ", requiredCount := " ++ toString evidence.requiredCount ++
    ", resultChecked := " ++ leanBoolExpr evidence.resultChecked ++ " }"

end HostMoleculeDescriptorResultEvidence

/-- Graph theorem-family or concrete-outcome evidence carried by a molecule-specific graph target witness.

The evidence object records the graph theorem family being specialized and the source center-count
precondition that anchors the theorem-family specialization to the generated host molecule.  When
`expectedOutcome?` is populated, readiness requires a compiler-supported configuration policy and
the generated source must prove the concrete classifier value in the kernel. -/
structure HostMoleculeGraphResultEvidence where
  kind : HostMoleculeGraphResultEvidenceKind
  sourceCenterCount : ℕ := 0
  requiredCenterCount : ℕ := 1
  configurationPolicy : HostMoleculeGraphConfigurationPolicy :=
    HostMoleculeGraphConfigurationPolicy.identityMirror
  expectedOutcome? : Option CipRSClassRelation := none
  outcomePrecondition : HostMoleculeGraphOutcomePrecondition :=
    HostMoleculeGraphOutcomePrecondition.none
  outcomeChecked : Bool := false
  resultChecked : Bool := false
  deriving DecidableEq, Repr

namespace HostMoleculeGraphResultEvidence

/-- Lean expression for a concrete graph/multi-center `R/S` relation outcome. -/
def cipRSClassRelationExpr : CipRSClassRelation → String
  | CipRSClassRelation.same => "TetraStereo.OneCenter.CipRSClassRelation.same"
  | CipRSClassRelation.enantiomeric => "TetraStereo.OneCenter.CipRSClassRelation.enantiomeric"
  | CipRSClassRelation.diastereomeric => "TetraStereo.OneCenter.CipRSClassRelation.diastereomeric"

/-- Stable package-key segment for a concrete graph/multi-center `R/S` relation outcome. -/
def cipRSClassRelationKeySegment : CipRSClassRelation → String
  | CipRSClassRelation.same => "same"
  | CipRSClassRelation.enantiomeric => "enantiomeric"
  | CipRSClassRelation.diastereomeric => "diastereomeric"

/-- Compact generated-name segment for a concrete graph/multi-center `R/S` relation outcome. -/
def cipRSClassRelationNameSuffixSegment : CipRSClassRelation → String
  | CipRSClassRelation.same => "Same"
  | CipRSClassRelation.enantiomeric => "Enantiomeric"
  | CipRSClassRelation.diastereomeric => "Diastereomeric"

/-- Concrete graph outcomes that this compiler can prove without host-supplied proof terms. -/
def autoOutcomeSupported (kind : HostMoleculeGraphResultEvidenceKind)
    (policy : HostMoleculeGraphConfigurationPolicy)
    (precondition : HostMoleculeGraphOutcomePrecondition)
    (outcome : CipRSClassRelation) : Bool :=
  match kind, policy, precondition, outcome with
  | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound,
      HostMoleculeGraphConfigurationPolicy.identitySelf,
      HostMoleculeGraphOutcomePrecondition.none, CipRSClassRelation.same => true
  | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound,
      HostMoleculeGraphConfigurationPolicy.identityMirror,
      HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft, CipRSClassRelation.same => true
  | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound,
      HostMoleculeGraphConfigurationPolicy.identityMirror,
      HostMoleculeGraphOutcomePrecondition.descriptorChiralLeft,
      CipRSClassRelation.enantiomeric => true
  | _, _, _, _ => false

/-- Executable readiness predicate for molecule-specialized graph theorem-family evidence. -/
def readyFor (evidence : HostMoleculeGraphResultEvidence)
    (coverageField : HostMoleculeTargetCoverageField) (observedCount : ℕ) : Bool :=
  evidence.resultChecked &&
    decide (evidence.kind.coverageField = coverageField) &&
      decide (evidence.requiredCenterCount > 0) &&
        decide (evidence.sourceCenterCount = observedCount) &&
          decide (evidence.sourceCenterCount ≥ evidence.requiredCenterCount) &&
            match evidence.expectedOutcome? with
            | none =>
                decide (evidence.outcomePrecondition = HostMoleculeGraphOutcomePrecondition.none) &&
                  !evidence.outcomeChecked
            | some outcome =>
                evidence.outcomeChecked &&
                  autoOutcomeSupported evidence.kind evidence.configurationPolicy
                    evidence.outcomePrecondition outcome

/-- Render graph-result evidence as Lean source. -/
def expr (evidence : HostMoleculeGraphResultEvidence) : String :=
  "some { kind := " ++ evidence.kind.expr ++
    ", sourceCenterCount := " ++ toString evidence.sourceCenterCount ++
    ", requiredCenterCount := " ++ toString evidence.requiredCenterCount ++
    ", configurationPolicy := " ++ evidence.configurationPolicy.expr ++
    ", expectedOutcome? := " ++
      (match evidence.expectedOutcome? with
      | none => "none"
      | some outcome => "some " ++ cipRSClassRelationExpr outcome) ++
    ", outcomePrecondition := " ++ evidence.outcomePrecondition.expr ++
    ", outcomeChecked := " ++ leanBoolExpr evidence.outcomeChecked ++
    ", resultChecked := " ++ leanBoolExpr evidence.resultChecked ++ " }"

/-- Stable generated-name segment for this graph-result evidence. -/
def nameSuffixSegment (evidence : HostMoleculeGraphResultEvidence) : String :=
  let base := evidence.kind.nameSuffixSegment
  match evidence.expectedOutcome? with
  | none =>
      if evidence.configurationPolicy = HostMoleculeGraphConfigurationPolicy.identityMirror then
        base
      else
        base ++ "_" ++ evidence.configurationPolicy.nameSuffixSegment
  | some outcome =>
      base ++ "_" ++ evidence.configurationPolicy.nameSuffixSegment ++
        (if evidence.outcomePrecondition = HostMoleculeGraphOutcomePrecondition.none then
          ""
        else
          "_" ++ evidence.outcomePrecondition.nameSuffixSegment) ++ "_" ++
        cipRSClassRelationNameSuffixSegment outcome

/-- Stable package-key suffix for this graph-result evidence. -/
def keySuffix (evidence : HostMoleculeGraphResultEvidence) : String :=
  let base := "::graph-result::" ++ evidence.kind.keySegment
  match evidence.expectedOutcome? with
  | none =>
      if evidence.configurationPolicy = HostMoleculeGraphConfigurationPolicy.identityMirror then
        base
      else
        base ++ "::configuration::" ++ evidence.configurationPolicy.keySegment
  | some outcome =>
      base ++ "::configuration::" ++ evidence.configurationPolicy.keySegment ++
        (if evidence.outcomePrecondition = HostMoleculeGraphOutcomePrecondition.none then
          ""
        else
          "::precondition::" ++ evidence.outcomePrecondition.keySegment) ++
        "::outcome::" ++ cipRSClassRelationKeySegment outcome

end HostMoleculeGraphResultEvidence

/-- Molecule-specific witness tying a host analysis target to concrete package metadata and,
when applicable, executable coverage evidence. -/
structure HostMoleculeTargetWitness where
  requestKey : String
  targetKeySuffix : String
  targetDescription : String
  targetLabel : String
  kind : HostMoleculeTargetWitnessKind
  coverageField : HostMoleculeTargetCoverageField
  observedCount : ℕ := 0
  requiredCount : ℕ := 0
  coverageChecked : Bool := false
  descriptorResult? : Option HostMoleculeDescriptorResultEvidence := none
  graphResult? : Option HostMoleculeGraphResultEvidence := none
  theoremFamilyKeys : List String := []
  deriving Repr

namespace HostMoleculeTargetWitness

/-- Coverage evidence must be explicit and non-vacuous for molecule-specific target witnesses. -/
def coverageReady (witness : HostMoleculeTargetWitness) : Bool :=
  witness.coverageChecked &&
    decide (witness.requiredCount > 0) &&
      decide (witness.observedCount ≥ witness.requiredCount)

/-- Exact descriptor-result evidence is optional, but must be internally ready when present. -/
def descriptorResultReady (witness : HostMoleculeTargetWitness) : Bool :=
  match witness.descriptorResult? with
  | none => true
  | some evidence => evidence.readyFor witness.coverageField witness.observedCount

/-- Typed graph-result evidence is required exactly for graph-level target witnesses. -/
def graphResultReady (witness : HostMoleculeTargetWitness) : Bool :=
  match witness.coverageField.graphResultKind?, witness.graphResult? with
  | none, none => true
  | some expectedKind, some evidence =>
      decide (evidence.kind = expectedKind) &&
        decide (evidence.requiredCenterCount = witness.requiredCount) &&
          evidence.readyFor witness.coverageField witness.observedCount
  | _, _ => false

/-- Exact descriptor-result and graph-result evidence are mutually exclusive target modes. -/
def resultEvidenceModeReady (witness : HostMoleculeTargetWitness) : Bool :=
  match witness.descriptorResult?, witness.graphResult? with
  | some _, some _ => false
  | _, _ => true

/-- Stable generated name suffix for this witness. -/
def nameSuffix (witness : HostMoleculeTargetWitness) : String :=
  let base :=
    compactGeneratedNameSegment "Req" witness.requestKey ++ "_" ++
      witness.coverageField.nameSuffixSegment ++ "_" ++
        compactGeneratedNameSegment "Tgt" witness.targetKeySuffix
  match witness.descriptorResult? with
  | none =>
      match witness.graphResult? with
      | none => base
      | some evidence => base ++ "_" ++ evidence.nameSuffixSegment
  | some evidence =>
      base ++ "_" ++ evidence.result.nameSuffixSegment ++ "_" ++
          evidence.sourceKey.nameSuffixSegment

/-- Executable readiness predicate for generated molecule-specific target witnesses. -/
def ready (witness : HostMoleculeTargetWitness) : Bool :=
  hostPackageKeySegment? witness.requestKey &&
    hostPackageKeySegment? witness.targetKeySuffix &&
      witness.targetDescription != "" &&
        witness.targetLabel != "" &&
          decide (witness.kind = witness.coverageField.expectedKind) &&
              decide (witness.targetLabel = witness.coverageField.expectedTargetLabel) &&
              witness.coverageReady &&
                decide
                  (witness.theoremFamilyKeys =
                    witness.coverageField.requiredClaimTargets.map
                      (hostAnalysisClaimPackageKey witness.requestKey)) &&
                  witness.descriptorResultReady &&
                    witness.graphResultReady &&
                      witness.resultEvidenceModeReady &&
                        leanIdentifierRestSafe witness.nameSuffix &&
                          !witness.theoremFamilyKeys.isEmpty &&
                            !hasDuplicateStrings witness.theoremFamilyKeys

/-- Readiness exposes identifier-rest safety of the canonical generated-name suffix. -/
theorem nameSuffix_safe_of_ready (witness : HostMoleculeTargetWitness)
    (hready : witness.ready = true) :
    leanIdentifierRestSafe witness.nameSuffix = true := by
  unfold ready at hready
  simp only [Bool.and_eq_true] at hready
  aesop

/-- Proposition carried by a generated molecule-specific target witness. -/
def claim (witness : HostMoleculeTargetWitness) : Prop :=
  witness.ready = true

/-- Render a witness object as Lean source. -/
def expr (witness : HostMoleculeTargetWitness) : String :=
  "  { requestKey := " ++ leanStringLit witness.requestKey ++ "\n" ++
    "    targetKeySuffix := " ++ leanStringLit witness.targetKeySuffix ++ "\n" ++
    "    targetDescription := " ++ leanStringLit witness.targetDescription ++ "\n" ++
    "    targetLabel := " ++ leanStringLit witness.targetLabel ++ "\n" ++
    "    kind := " ++ witness.kind.expr ++ "\n" ++
    "    coverageField := " ++ witness.coverageField.expr ++ "\n" ++
    "    observedCount := " ++ toString witness.observedCount ++ "\n" ++
    "    requiredCount := " ++ toString witness.requiredCount ++ "\n" ++
    "    coverageChecked := " ++ leanBoolExpr witness.coverageChecked ++ "\n" ++
    "    descriptorResult? := " ++
      (match witness.descriptorResult? with
        | none => "none"
        | some evidence => HostMoleculeDescriptorResultEvidence.expr evidence) ++ "\n" ++
    "    graphResult? := " ++
      (match witness.graphResult? with
        | none => "none"
        | some evidence => HostMoleculeGraphResultEvidence.expr evidence) ++ "\n" ++
    "    theoremFamilyKeys := " ++ leanStringListExpr witness.theoremFamilyKeys ++ " }"

/-- Canonical generated package key for this witness. -/
def expectedPackageKey (witness : HostMoleculeTargetWitness) : String :=
  let base :=
    witness.requestKey ++ "::target-witness::" ++
    witness.coverageField.packageKeySegment ++ "::" ++ witness.targetKeySuffix
  match witness.descriptorResult? with
  | none =>
      match witness.graphResult? with
      | none => base
      | some evidence => base ++ evidence.keySuffix
  | some evidence =>
      base ++ "::descriptor-result::" ++ evidence.result.keySegment ++
        "::source::" ++ evidence.sourceKey.keySegment

/-- Canonical generated file name for this witness. -/
def expectedFileName (witness : HostMoleculeTargetWitness) : String :=
  "HostMoleculeTargetWitness_" ++ witness.nameSuffix ++ ".lean"

/-- Canonical generated definition name for this witness. -/
def expectedDefinitionName (witness : HostMoleculeTargetWitness) : String :=
  "hostMoleculeTargetWitness_" ++ witness.nameSuffix

/-- Canonical generated coverage theorem name for this witness. -/
def expectedCoverageTheoremName (witness : HostMoleculeTargetWitness) : String :=
  "host_molecule_target_witness_" ++ witness.nameSuffix ++ "_coverage"

/-- Canonical generated checked theorem name for this witness. -/
def expectedTheoremName (witness : HostMoleculeTargetWitness) : String :=
  "host_molecule_target_witness_" ++ witness.nameSuffix ++ "_checked"

/-- Canonical generated descriptor-result theorem name for this witness, when result-bound. -/
def expectedDescriptorResultTheoremName (witness : HostMoleculeTargetWitness) : String :=
  "host_molecule_target_witness_" ++ witness.nameSuffix ++ "_descriptor_result"

/-- Canonical generated graph-result theorem name for this witness, when graph-result-bound. -/
def expectedGraphResultTheoremName (witness : HostMoleculeTargetWitness) : String :=
  "host_molecule_target_witness_" ++ witness.nameSuffix ++ "_graph_result"

/-- Canonical theorem-family package keys required by this witness. -/
def expectedTheoremFamilyKeys (witness : HostMoleculeTargetWitness) : List String :=
  witness.coverageField.requiredClaimTargets.map (hostAnalysisClaimPackageKey witness.requestKey)

/-- Canonical host-facing key for the public target certificate layered over this witness. -/
def expectedCertificateKey (witness : HostMoleculeTargetWitness) : String :=
  match witness.descriptorResult?, witness.graphResult? with
  | some _, _ => witness.expectedPackageKey ++ "::descriptor-result-certificate"
  | none, some _ => witness.expectedPackageKey ++ "::graph-result-certificate"
  | none, none => witness.expectedPackageKey ++ "::coverage-certificate"

/-- Canonical generated definition name for the public target certificate over this witness. -/
def expectedCertificateDefinitionName (witness : HostMoleculeTargetWitness) : String :=
  "hostMoleculeTargetCertificate_" ++ witness.nameSuffix

/-- Canonical generated checked theorem name for the public target certificate over this witness. -/
def expectedCertificateTheoremName (witness : HostMoleculeTargetWitness) : String :=
  "host_molecule_target_certificate_" ++ witness.nameSuffix ++ "_checked"

/-- Canonical witness declaration names are identifier-safe once their shared suffix is safe. -/
theorem expectedDefinitionName_identifier_safe (witness : HostMoleculeTargetWitness)
    (hsuffix : leanIdentifierRestSafe witness.nameSuffix = true) :
    leanIdentifierSegment? witness.expectedDefinitionName = true := by
  simpa [expectedDefinitionName, String.append_assoc] using
    leanIdentifierSegment_host_parts_safe "MoleculeTargetWitness_" witness.nameSuffix ""
      (by rfl) hsuffix (by rfl)

theorem expectedCoverageTheoremName_identifier_safe (witness : HostMoleculeTargetWitness)
    (hsuffix : leanIdentifierRestSafe witness.nameSuffix = true) :
    leanIdentifierSegment? witness.expectedCoverageTheoremName = true := by
  simpa [expectedCoverageTheoremName, String.append_assoc] using
    leanIdentifierSegment_host_parts_safe "_molecule_target_witness_" witness.nameSuffix "_coverage"
      (by rfl) hsuffix (by rfl)

theorem expectedTheoremName_identifier_safe (witness : HostMoleculeTargetWitness)
    (hsuffix : leanIdentifierRestSafe witness.nameSuffix = true) :
    leanIdentifierSegment? witness.expectedTheoremName = true := by
  simpa [expectedTheoremName, String.append_assoc] using
    leanIdentifierSegment_host_parts_safe "_molecule_target_witness_" witness.nameSuffix "_checked"
      (by rfl) hsuffix (by rfl)

theorem expectedDescriptorResultTheoremName_identifier_safe (witness : HostMoleculeTargetWitness)
    (hsuffix : leanIdentifierRestSafe witness.nameSuffix = true) :
    leanIdentifierSegment? witness.expectedDescriptorResultTheoremName = true := by
  simpa [expectedDescriptorResultTheoremName, String.append_assoc] using
    leanIdentifierSegment_host_parts_safe "_molecule_target_witness_" witness.nameSuffix
      "_descriptor_result" (by rfl) hsuffix (by rfl)

theorem expectedGraphResultTheoremName_identifier_safe (witness : HostMoleculeTargetWitness)
    (hsuffix : leanIdentifierRestSafe witness.nameSuffix = true) :
    leanIdentifierSegment? witness.expectedGraphResultTheoremName = true := by
  simpa [expectedGraphResultTheoremName, String.append_assoc] using
    leanIdentifierSegment_host_parts_safe "_molecule_target_witness_" witness.nameSuffix
      "_graph_result" (by rfl) hsuffix (by rfl)

theorem expectedCertificateDefinitionName_identifier_safe (witness : HostMoleculeTargetWitness)
    (hsuffix : leanIdentifierRestSafe witness.nameSuffix = true) :
    leanIdentifierSegment? witness.expectedCertificateDefinitionName = true := by
  simpa [expectedCertificateDefinitionName, String.append_assoc] using
    leanIdentifierSegment_host_parts_safe "MoleculeTargetCertificate_" witness.nameSuffix ""
      (by rfl) hsuffix (by rfl)

theorem expectedCertificateTheoremName_identifier_safe (witness : HostMoleculeTargetWitness)
    (hsuffix : leanIdentifierRestSafe witness.nameSuffix = true) :
    leanIdentifierSegment? witness.expectedCertificateTheoremName = true := by
  simpa [expectedCertificateTheoremName, String.append_assoc] using
    leanIdentifierSegment_host_parts_safe "_molecule_target_certificate_" witness.nameSuffix "_checked"
      (by rfl) hsuffix (by rfl)

end HostMoleculeTargetWitness

/-- Public, molecule-specific target-certificate object layered over a target witness.

The witness is the proof kernel; this certificate is the host-facing transaction object.  It binds
the witness to its exact generated theorem declarations, coverage source, recomputed source count,
and theorem-family dependencies so downstream adapters can consume a checked target-certificate
theorem rather than a raw coverage witness. -/
structure HostMoleculeTargetCertificate where
  key : String
  witness : HostMoleculeTargetWitness
  namespacePath : List String := []
  witnessTheoremFullName : String
  coverageTheoremFullName : String
  certificateTheoremFullName : String
  coverageSourceModule : String
  coverageSourcePacketName : String
  coverageSourceAnnotationsName : String
  coverageSourceBlueprintName : String
  coverageSourceOwnerName : String
  coverageSourceOwnerKey : String
  sourceCoverageCount : ℕ := 0
  sourceDescriptorResultCount : ℕ := 0
  sourceGraphResultCenterCount : ℕ := 0
  sourceGraphResultChecked : Bool := false
  theoremFamilyKeys : List String := []
  deriving Repr

namespace HostMoleculeTargetCertificate

/-- Source count expected by the public certificate for optional descriptor-result evidence. -/
def expectedSourceDescriptorResultCount (certificate : HostMoleculeTargetCertificate) : ℕ :=
  match certificate.witness.descriptorResult? with
  | none => 0
  | some evidence => evidence.matchedCount

/-- Source count expected by the public certificate for optional graph-result evidence. -/
def expectedSourceGraphResultCenterCount (certificate : HostMoleculeTargetCertificate) : ℕ :=
  match certificate.witness.graphResult? with
  | none => 0
  | some evidence => evidence.sourceCenterCount

/-- Source checked flag expected by the public certificate for optional graph-result evidence. -/
def expectedSourceGraphResultChecked (certificate : HostMoleculeTargetCertificate) : Bool :=
  match certificate.witness.graphResult? with
  | none => false
  | some evidence => evidence.resultChecked

/-- Canonical owner-key declaration name derived from the selected source module. -/
def expectedCoverageSourceOwnerName (certificate : HostMoleculeTargetCertificate) : String :=
  certificate.coverageSourceModule ++ "." ++ hostOfficialStereoOwnerRequestKeyDeclarationName

/-- Source expressions in a public certificate must all come from its declared source module. -/
def coverageSourceNamesReady (certificate : HostMoleculeTargetCertificate) : Bool :=
  qualifiedNameInModule? certificate.coverageSourceModule certificate.coverageSourcePacketName &&
    qualifiedNameInModule? certificate.coverageSourceModule certificate.coverageSourceAnnotationsName &&
      qualifiedNameInModule? certificate.coverageSourceModule certificate.coverageSourceBlueprintName &&
        certificate.coverageSourceOwnerName == certificate.expectedCoverageSourceOwnerName

/-- Executable readiness predicate for a public molecule-specific target certificate. -/
def ready (certificate : HostMoleculeTargetCertificate) : Bool :=
  certificate.key == certificate.witness.expectedCertificateKey &&
    certificate.witness.ready &&
      !certificate.namespacePath.isEmpty &&
        certificate.witnessTheoremFullName ==
            leanQualifiedName certificate.namespacePath certificate.witness.expectedTheoremName &&
          certificate.coverageTheoremFullName ==
              leanQualifiedName certificate.namespacePath
                certificate.witness.expectedCoverageTheoremName &&
            certificate.certificateTheoremFullName ==
                leanQualifiedName certificate.namespacePath
                  certificate.witness.expectedCertificateTheoremName &&
              certificate.coverageSourceModule != "" &&
                certificate.coverageSourceNamesReady &&
                  certificate.coverageSourceOwnerKey == certificate.witness.requestKey &&
                    certificate.sourceCoverageCount == certificate.witness.observedCount &&
                      certificate.sourceDescriptorResultCount ==
                          certificate.expectedSourceDescriptorResultCount &&
                        certificate.sourceGraphResultCenterCount ==
                            certificate.expectedSourceGraphResultCenterCount &&
                          certificate.sourceGraphResultChecked ==
                              certificate.expectedSourceGraphResultChecked &&
                            certificate.theoremFamilyKeys ==
                                certificate.witness.theoremFamilyKeys

/-- Render a public target certificate object as Lean source, referencing a generated witness def. -/
def expr (certificate : HostMoleculeTargetCertificate)
    (witnessExpr sourceOwnerExpr sourceCoverageExpr sourceDescriptorResultExpr
      sourceGraphResultExpr sourceGraphCheckedExpr : String) : String :=
  "  { key := " ++ leanStringLit certificate.key ++ "\n" ++
    "    witness := " ++ witnessExpr ++ "\n" ++
    "    namespacePath := " ++ leanStringListExpr certificate.namespacePath ++ "\n" ++
    "    witnessTheoremFullName := " ++
      leanStringLit certificate.witnessTheoremFullName ++ "\n" ++
    "    coverageTheoremFullName := " ++
      leanStringLit certificate.coverageTheoremFullName ++ "\n" ++
    "    certificateTheoremFullName := " ++
      leanStringLit certificate.certificateTheoremFullName ++ "\n" ++
    "    coverageSourceModule := " ++ leanStringLit certificate.coverageSourceModule ++ "\n" ++
    "    coverageSourcePacketName := " ++ leanStringLit certificate.coverageSourcePacketName ++ "\n" ++
    "    coverageSourceAnnotationsName := " ++
      leanStringLit certificate.coverageSourceAnnotationsName ++ "\n" ++
    "    coverageSourceBlueprintName := " ++
      leanStringLit certificate.coverageSourceBlueprintName ++ "\n" ++
    "    coverageSourceOwnerName := " ++ leanStringLit certificate.coverageSourceOwnerName ++ "\n" ++
    "    coverageSourceOwnerKey := " ++ sourceOwnerExpr ++ "\n" ++
    "    sourceCoverageCount := " ++ sourceCoverageExpr ++ "\n" ++
    "    sourceDescriptorResultCount := " ++ sourceDescriptorResultExpr ++ "\n" ++
    "    sourceGraphResultCenterCount := " ++ sourceGraphResultExpr ++ "\n" ++
    "    sourceGraphResultChecked := " ++ sourceGraphCheckedExpr ++ "\n" ++
    "    theoremFamilyKeys := " ++ leanStringListExpr certificate.theoremFamilyKeys ++ " }"

end HostMoleculeTargetCertificate

/-- Host-facing request for a generated molecule-specific target witness theorem. -/
structure HostMoleculeTargetWitnessRequest where
  key : String
  description : String
  witness : HostMoleculeTargetWitness
  fileName : String
  namespacePath : List String := ["TetraStereoGenerated", "HostTargetWitnesses"]
  definitionName : String
  theoremName : String
  coverageSourceModule : String
  coverageSourcePacketName : String
  coverageSourceAnnotationsName : String
  coverageSourceBlueprintName : String
  coverageSourceOwnerName : String
  coverageTheoremName : String
  dependencyTheoremNames : List String := []
  imports : List String := ["TetraStereo.Engine.HostAnalysisRequestBuilder"]
  options : List String := ["set_option maxHeartbeats 1000000", "set_option maxRecDepth 10000"]
  deriving Repr

namespace HostMoleculeTargetWitnessRequest

/-- Import module for this generated target-witness source. -/
def moduleName (request : HostMoleculeTargetWitnessRequest) : String :=
  generatedModuleName request.namespacePath request.fileName

/-- Fully-qualified theorem name emitted by this generated target-witness source. -/
def theoremFullName (request : HostMoleculeTargetWitnessRequest) : String :=
  leanQualifiedName request.namespacePath request.theoremName

/-- Fully-qualified witness definition name emitted by this generated target-witness source. -/
def definitionFullName (request : HostMoleculeTargetWitnessRequest) : String :=
  leanQualifiedName request.namespacePath request.definitionName

/-- Generated definition name for the public certificate layered over this witness. -/
def certificateDefinitionName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.witness.expectedCertificateDefinitionName

/-- Generated checked theorem name for the public certificate layered over this witness. -/
def certificateTheoremName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.witness.expectedCertificateTheoremName

/-- Fully-qualified certificate definition name emitted by this generated target source. -/
def certificateDefinitionFullName (request : HostMoleculeTargetWitnessRequest) : String :=
  leanQualifiedName request.namespacePath request.certificateDefinitionName

/-- Fully-qualified public certificate theorem name emitted by this generated target source. -/
def certificateTheoremFullName (request : HostMoleculeTargetWitnessRequest) : String :=
  leanQualifiedName request.namespacePath request.certificateTheoremName

/-- Generated public certificate object layered over this witness request. -/
def certificate (request : HostMoleculeTargetWitnessRequest) :
    HostMoleculeTargetCertificate where
  key := request.witness.expectedCertificateKey
  witness := request.witness
  namespacePath := request.namespacePath
  witnessTheoremFullName := request.theoremFullName
  coverageTheoremFullName := leanQualifiedName request.namespacePath request.coverageTheoremName
  certificateTheoremFullName := request.certificateTheoremFullName
  coverageSourceModule := request.coverageSourceModule
  coverageSourcePacketName := request.coverageSourcePacketName
  coverageSourceAnnotationsName := request.coverageSourceAnnotationsName
  coverageSourceBlueprintName := request.coverageSourceBlueprintName
  coverageSourceOwnerName := request.coverageSourceOwnerName
  coverageSourceOwnerKey := request.witness.requestKey
  sourceCoverageCount := request.witness.observedCount
  sourceDescriptorResultCount :=
    match request.witness.descriptorResult? with
    | none => 0
    | some evidence => evidence.matchedCount
  sourceGraphResultCenterCount :=
    match request.witness.graphResult? with
    | none => 0
    | some evidence => evidence.sourceCenterCount
  sourceGraphResultChecked :=
    match request.witness.graphResult? with
    | none => false
    | some evidence => evidence.resultChecked
  theoremFamilyKeys := request.witness.theoremFamilyKeys

/-- Canonical owner-key declaration name derived only from the selected source module. -/
def expectedCoverageSourceOwnerName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.coverageSourceModule ++ "." ++ hostOfficialStereoOwnerRequestKeyDeclarationName

/-- Source expressions in a witness request must all come from its declared source module. -/
def coverageSourceNamesReady (request : HostMoleculeTargetWitnessRequest) : Bool :=
  qualifiedNameInModule? request.coverageSourceModule request.coverageSourcePacketName &&
    qualifiedNameInModule? request.coverageSourceModule request.coverageSourceAnnotationsName &&
      qualifiedNameInModule? request.coverageSourceModule request.coverageSourceBlueprintName &&
        request.coverageSourceOwnerName == request.expectedCoverageSourceOwnerName

/-- Generated descriptor-result theorem name, present only for result-bound target witnesses. -/
def descriptorResultTheoremName? (request : HostMoleculeTargetWitnessRequest) : Option String :=
  match request.witness.descriptorResult? with
  | none => none
  | some _ => some request.witness.expectedDescriptorResultTheoremName

/-- Fully-qualified descriptor-result theorem name, if this witness is result-bound. -/
def descriptorResultTheoremFullName? (request : HostMoleculeTargetWitnessRequest) :
    Option String :=
  request.descriptorResultTheoremName?.map fun name => leanQualifiedName request.namespacePath name

/-- Generated graph-result theorem name, present only for graph-result-bound target witnesses. -/
def graphResultTheoremName? (request : HostMoleculeTargetWitnessRequest) : Option String :=
  match request.witness.graphResult? with
  | none => none
  | some _ => some request.witness.expectedGraphResultTheoremName

/-- Fully-qualified graph-result theorem name, if this witness is graph-result-bound. -/
def graphResultTheoremFullName? (request : HostMoleculeTargetWitnessRequest) :
    Option String :=
  request.graphResultTheoremName?.map fun name => leanQualifiedName request.namespacePath name

/-- Generated atom type expression for the host molecule source. -/
def coverageSourceAtomTypeExpr (request : HostMoleculeTargetWitnessRequest) : String :=
  "Fin (" ++ request.coverageSourceBlueprintName ++ ").normalized.parsed.atomCount"

/-- Generated proof-facing graph expression for the host molecule source. -/
def coverageSourceGraphExpr (request : HostMoleculeTargetWitnessRequest) : String :=
  "(" ++ request.coverageSourceBlueprintName ++ ").graph"

/-- Generated proof-facing multi-center molecule expression for the host molecule source. -/
def coverageSourceMoleculeExpr (request : HostMoleculeTargetWitnessRequest) : String :=
  "(" ++ request.coverageSourceBlueprintName ++ ").molecule"

/-- Generated identity graph-configuration declaration name. -/
def graphConfigurationLeftName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.definitionName ++ "GraphConfigurationLeft"

/-- Generated mirror graph-configuration declaration name. -/
def graphConfigurationRightName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.definitionName ++ "GraphConfigurationRight"

/-- Generated identity multi-center configuration declaration name. -/
def multiConfigurationLeftName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.definitionName ++ "MultiConfigurationLeft"

/-- Generated mirror multi-center configuration declaration name. -/
def multiConfigurationRightName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.definitionName ++ "MultiConfigurationRight"

/-- Generated configuration declarations required by this graph-result target. -/
def graphResultConfigurationNames (request : HostMoleculeTargetWitnessRequest) : List String :=
  match request.witness.graphResult? with
  | some { kind := HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne, .. } =>
      [request.multiConfigurationLeftName, request.multiConfigurationRightName]
  | some { kind := HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound, .. } =>
      [request.graphConfigurationLeftName, request.graphConfigurationRightName]
  | some { kind := HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal, .. } =>
      [request.graphConfigurationLeftName, request.graphConfigurationRightName]
  | none => []

/-- Fully-qualified declarations emitted by this generated target-witness source. -/
def declarationNames (request : HostMoleculeTargetWitnessRequest) : List String :=
  [ request.definitionFullName
  , leanQualifiedName request.namespacePath request.coverageTheoremName
  , request.theoremFullName
  ] ++
    (match request.descriptorResultTheoremName? with
      | none => []
      | some name => [leanQualifiedName request.namespacePath name]) ++
    (request.graphResultConfigurationNames.map fun name =>
      leanQualifiedName request.namespacePath name) ++
    (match request.graphResultTheoremName? with
      | none => []
      | some name => [leanQualifiedName request.namespacePath name]) ++
      [ request.certificateDefinitionFullName
      , request.certificateTheoremFullName ]

/-- Namespace-open lines for the generated target-witness package. -/
def namespaceOpenLines (request : HostMoleculeTargetWitnessRequest) : List String :=
  request.namespacePath.map fun namespaceName => "namespace " ++ namespaceName

/-- Namespace-close lines for the generated target-witness package. -/
def namespaceCloseLines (request : HostMoleculeTargetWitnessRequest) : List String :=
  request.namespacePath.reverse.map fun namespaceName => "end " ++ namespaceName

/-- Proof lines forcing dependency theorems to have the expected theorem-family proposition. -/
def dependencyReferenceLines (request : HostMoleculeTargetWitnessRequest) : List String :=
  (request.witness.coverageField.requiredClaimTargets.zip request.dependencyTheoremNames).map
    fun pair => "    have _ : " ++ pair.1.statement ++ " := " ++ pair.2

/-- The generated coverage statement tying the witness count to source molecule data. -/
def coverageStatement (request : HostMoleculeTargetWitnessRequest) : String :=
  request.definitionName ++ ".observedCount = " ++
    request.witness.coverageField.countExpr
      request.coverageSourcePacketName request.coverageSourceAnnotationsName

/-- The generated exact descriptor-result statement, when this target is result-bound. -/
def descriptorResultStatement? (request : HostMoleculeTargetWitnessRequest) :
    Option String :=
  request.witness.descriptorResult?.map fun evidence =>
    request.definitionName ++ ".descriptorResult?.map (fun evidence => evidence.matchedCount) = " ++
      "some (" ++ evidence.result.countForSourceKeyExpr evidence.sourceKey
        request.coverageSourcePacketName request.coverageSourceAnnotationsName ++ ")"

/-- Source lines for the optional exact descriptor-result theorem. -/
def descriptorResultTheoremLines (request : HostMoleculeTargetWitnessRequest) :
    List String :=
  match request.descriptorResultTheoremName?, request.descriptorResultStatement? with
  | some theoremName, some statement =>
      [ ""
      , "/-- The exact descriptor-result count is recomputed from the generated molecule source. -/"
      , "theorem " ++ theoremName ++ " :"
      , "    " ++ statement ++ " :="
      , "  by decide" ]
  | _, _ => []

/-- Source lines for graph/multi-center configurations used by a graph-result theorem. -/
def graphResultConfigurationLines (request : HostMoleculeTargetWitnessRequest) : List String :=
  match request.witness.graphResult? with
  | some evidence =>
    match evidence.kind with
    | HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne =>
      let policy := evidence.configurationPolicy
      [ ""
      , "/-- Identity multi-center configuration for the generated graph-result theorem. -/"
      , "def " ++ request.multiConfigurationLeftName ++ " :"
      , "    TetraStereo.OneCenter.MultiCenterMolecule.Configuration (" ++
          request.coverageSourceMoleculeExpr ++ ") :="
      , "  fun _ => 1"
      , ""
      , (match policy with
          | HostMoleculeGraphConfigurationPolicy.identityMirror =>
              "/-- Mirror multi-center configuration for the generated graph-result theorem. -/"
          | HostMoleculeGraphConfigurationPolicy.identitySelf =>
              "/-- Self multi-center configuration for the generated graph-result theorem. -/")
      , "def " ++ request.multiConfigurationRightName ++ " :"
      , "    TetraStereo.OneCenter.MultiCenterMolecule.Configuration (" ++
          request.coverageSourceMoleculeExpr ++ ") :="
      , (match policy with
          | HostMoleculeGraphConfigurationPolicy.identityMirror =>
              "  (" ++ request.coverageSourceMoleculeExpr ++ ").mirrorConfiguration " ++
                request.multiConfigurationLeftName
          | HostMoleculeGraphConfigurationPolicy.identitySelf =>
              "  " ++ request.multiConfigurationLeftName) ]
    | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound =>
      let policy := evidence.configurationPolicy
      [ ""
      , "/-- Identity graph configuration for the generated graph-result theorem. -/"
      , "def " ++ request.graphConfigurationLeftName ++ " :"
      , "    TetraStereo.OneCenter.MoleculeGraph.GraphConfiguration (" ++
          request.coverageSourceGraphExpr ++ ") :="
      , "  fun _ => 1"
      , ""
      , (match policy with
          | HostMoleculeGraphConfigurationPolicy.identityMirror =>
              "/-- Mirror graph configuration for the generated graph-result theorem. -/"
          | HostMoleculeGraphConfigurationPolicy.identitySelf =>
              "/-- Self graph configuration for the generated graph-result theorem. -/")
      , "def " ++ request.graphConfigurationRightName ++ " :"
      , "    TetraStereo.OneCenter.MoleculeGraph.GraphConfiguration (" ++
          request.coverageSourceGraphExpr ++ ") :="
      , (match policy with
          | HostMoleculeGraphConfigurationPolicy.identityMirror =>
              "  (" ++ request.coverageSourceGraphExpr ++
                ").detectedStereoSystem.mirrorConfiguration " ++ request.graphConfigurationLeftName
          | HostMoleculeGraphConfigurationPolicy.identitySelf =>
              "  " ++ request.graphConfigurationLeftName) ]
    | HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal =>
      let policy := evidence.configurationPolicy
      [ ""
      , "/-- Identity graph configuration for the generated graph-result theorem. -/"
      , "def " ++ request.graphConfigurationLeftName ++ " :"
      , "    TetraStereo.OneCenter.MoleculeGraph.GraphConfiguration (" ++
          request.coverageSourceGraphExpr ++ ") :="
      , "  fun _ => 1"
      , ""
      , (match policy with
          | HostMoleculeGraphConfigurationPolicy.identityMirror =>
              "/-- Mirror graph configuration for the generated graph-result theorem. -/"
          | HostMoleculeGraphConfigurationPolicy.identitySelf =>
              "/-- Self graph configuration for the generated graph-result theorem. -/")
      , "def " ++ request.graphConfigurationRightName ++ " :"
      , "    TetraStereo.OneCenter.MoleculeGraph.GraphConfiguration (" ++
          request.coverageSourceGraphExpr ++ ") :="
      , (match policy with
          | HostMoleculeGraphConfigurationPolicy.identityMirror =>
              "  (" ++ request.coverageSourceGraphExpr ++
                ").detectedStereoSystem.mirrorConfiguration " ++ request.graphConfigurationLeftName
          | HostMoleculeGraphConfigurationPolicy.identitySelf =>
              "  " ++ request.graphConfigurationLeftName) ]
  | none => []

/-- The generated graph-result statement, when this target is graph-result-bound. -/
def graphResultStatement? (request : HostMoleculeTargetWitnessRequest) : Option String :=
  request.witness.graphResult?.map fun evidence =>
    match evidence.expectedOutcome? with
    | none =>
        match evidence.kind with
        | HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne =>
            "((" ++ request.coverageSourceMoleculeExpr ++
              ").CipRSConfigurationClassificationExactlyOne " ++
              request.multiConfigurationLeftName ++ " " ++ request.multiConfigurationRightName ++ ")"
        | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound =>
            "((" ++ request.coverageSourceGraphExpr ++
              ").GraphCipRSDescriptorClassificationHolds " ++
              request.graphConfigurationLeftName ++ " " ++ request.graphConfigurationRightName ++
              " ((" ++ request.coverageSourceGraphExpr ++
              ").graphCipRSDescriptorClassifier " ++ request.graphConfigurationLeftName ++ " " ++
              request.graphConfigurationRightName ++ "))"
        | HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal =>
            "(¬ (" ++ request.coverageSourceGraphExpr ++
              ").GraphStereogenicByCIPDescriptor → (" ++ request.coverageSourceGraphExpr ++
              ").graphCipRSDescriptorClassifier? " ++ request.graphConfigurationLeftName ++ " " ++
              request.graphConfigurationRightName ++ " = none)"
    | some outcome =>
        match evidence.kind with
        | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound =>
            let outcomeExpr := HostMoleculeGraphResultEvidence.cipRSClassRelationExpr outcome
            let outcomeStatement :=
              "(((" ++ request.coverageSourceGraphExpr ++
                ").graphCipRSDescriptorClassifier " ++ request.graphConfigurationLeftName ++ " " ++
                request.graphConfigurationRightName ++ " = " ++ outcomeExpr ++ ") ∧ ((" ++
                request.coverageSourceGraphExpr ++
                ").GraphCipRSDescriptorClassificationHolds " ++
                request.graphConfigurationLeftName ++ " " ++ request.graphConfigurationRightName ++
                " " ++ outcomeExpr ++ ") ∧ ((" ++ request.coverageSourceGraphExpr ++
                ").GraphStereogenicByCIPDescriptor → (" ++ request.coverageSourceGraphExpr ++
                ").graphCipRSDescriptorClassifier? " ++ request.graphConfigurationLeftName ++ " " ++
                request.graphConfigurationRightName ++ " = some " ++ outcomeExpr ++ "))"
            match evidence.outcomePrecondition with
            | HostMoleculeGraphOutcomePrecondition.none => outcomeStatement
            | HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft =>
                "((" ++ request.coverageSourceGraphExpr ++
                  ").GraphMesoBySymmetryDescriptor " ++ request.graphConfigurationLeftName ++
                  " → " ++ outcomeStatement ++ ")"
            | HostMoleculeGraphOutcomePrecondition.descriptorChiralLeft =>
                "((" ++ request.coverageSourceGraphExpr ++
                  ").GraphChiralBySymmetryDescriptor " ++ request.graphConfigurationLeftName ++
                  " → " ++ outcomeStatement ++ ")"
        | _ =>
            "(False)"

/-- Source lines for the optional graph-result theorem. -/
def graphResultTheoremLines (request : HostMoleculeTargetWitnessRequest) : List String :=
  match request.graphResultTheoremName?, request.graphResultStatement?,
    request.witness.graphResult?, request.dependencyTheoremNames with
  | some theoremName, some statement, some evidence, dependencyTheoremName :: _ =>
      let proofLines :=
        match evidence.expectedOutcome? with
        | some CipRSClassRelation.same =>
            match evidence.kind, evidence.configurationPolicy, evidence.outcomePrecondition with
            | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound,
                HostMoleculeGraphConfigurationPolicy.identitySelf,
                HostMoleculeGraphOutcomePrecondition.none =>
                [ "  have h : TetraStereo.Engine.graphDescriptorClassifierSoundClaim :="
                , "    " ++ dependencyTheoremName
                , "  have hclassifier :"
                , "      (" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier " ++ request.graphConfigurationLeftName ++
                    " " ++ request.graphConfigurationRightName ++
                    " = TetraStereo.OneCenter.CipRSClassRelation.same := by"
                , "    simpa [" ++ request.graphConfigurationRightName ++ "] using"
                , "      ((" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier_self_same " ++
                    request.graphConfigurationLeftName ++ ")"
                , "  constructor"
                , "  · exact hclassifier"
                , "  · constructor"
                , "    · have hsound := h (" ++ request.coverageSourceAtomTypeExpr ++ ") (" ++
                    request.coverageSourceGraphExpr ++ ") " ++ request.graphConfigurationLeftName ++
                    " " ++ request.graphConfigurationRightName
                , "      simpa [hclassifier] using hsound"
                , "    · intro hresolved"
                , "      have hsafe :="
                , "        (" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier?_eq_some_same_of_stereogenicByCIPDescriptor_self " ++
                    "hresolved " ++ request.graphConfigurationLeftName
                , "      simpa [" ++ request.graphConfigurationRightName ++ "] using hsafe" ]
            | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound,
                HostMoleculeGraphConfigurationPolicy.identityMirror,
                HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft =>
                [ "  have h : TetraStereo.Engine.graphDescriptorClassifierSoundClaim :="
                , "    " ++ dependencyTheoremName
                , "  intro hpre"
                , "  have hclassifier :"
                , "      (" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier " ++ request.graphConfigurationLeftName ++
                    " " ++ request.graphConfigurationRightName ++
                    " = TetraStereo.OneCenter.CipRSClassRelation.same := by"
                , "    simpa [" ++ request.graphConfigurationRightName ++ "] using"
                , "      ((" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier_self_mirror_same_of_meso " ++
                    "(cfg := " ++ request.graphConfigurationLeftName ++ ") hpre)"
                , "  constructor"
                , "  · exact hclassifier"
                , "  · constructor"
                , "    · have hsound := h (" ++ request.coverageSourceAtomTypeExpr ++ ") (" ++
                    request.coverageSourceGraphExpr ++ ") " ++ request.graphConfigurationLeftName ++
                    " " ++ request.graphConfigurationRightName
                , "      simpa [hclassifier] using hsound"
                , "    · intro hresolved"
                , "      have hsafe :="
                , "        (" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier?_eq_some_same_of_stereogenicByCIPDescriptor_self_mirror " ++
                    "hresolved (cfg := " ++ request.graphConfigurationLeftName ++ ") hpre"
                , "      simpa [" ++ request.graphConfigurationRightName ++ "] using hsafe" ]
            | _, _, _ =>
                [ "  contradiction" ]
        | some CipRSClassRelation.enantiomeric =>
            match evidence.kind, evidence.configurationPolicy, evidence.outcomePrecondition with
            | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound,
                HostMoleculeGraphConfigurationPolicy.identityMirror,
                HostMoleculeGraphOutcomePrecondition.descriptorChiralLeft =>
                [ "  have h : TetraStereo.Engine.graphDescriptorClassifierSoundClaim :="
                , "    " ++ dependencyTheoremName
                , "  intro hpre"
                , "  have hclassifier :"
                , "      (" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier " ++ request.graphConfigurationLeftName ++
                    " " ++ request.graphConfigurationRightName ++
                    " = TetraStereo.OneCenter.CipRSClassRelation.enantiomeric := by"
                , "    simpa [" ++ request.graphConfigurationRightName ++ "] using"
                , "      ((" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier_self_mirror_enantiomeric_of_chiral " ++
                    "(cfg := " ++ request.graphConfigurationLeftName ++ ") hpre)"
                , "  constructor"
                , "  · exact hclassifier"
                , "  · constructor"
                , "    · have hsound := h (" ++ request.coverageSourceAtomTypeExpr ++ ") (" ++
                    request.coverageSourceGraphExpr ++ ") " ++ request.graphConfigurationLeftName ++
                    " " ++ request.graphConfigurationRightName
                , "      simpa [hclassifier] using hsound"
                , "    · intro hresolved"
                , "      have hsafe :="
                , "        (" ++ request.coverageSourceGraphExpr ++
                    ").graphCipRSDescriptorClassifier?_eq_some_enantiomeric_of_stereogenicByCIPDescriptor_self_mirror " ++
                    "hresolved (cfg := " ++ request.graphConfigurationLeftName ++ ") hpre"
                , "      simpa [" ++ request.graphConfigurationRightName ++ "] using hsafe" ]
            | _, _, _ =>
                [ "  contradiction" ]
        | some _ =>
            [ "  contradiction" ]
        | none =>
            match evidence.kind with
            | HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne =>
                [ "  have h : TetraStereo.Engine.multiCenterCipRSClassificationExactlyOneClaim :="
                , "    " ++ dependencyTheoremName
                , "  exact h (" ++ request.coverageSourceAtomTypeExpr ++ ") (" ++
                    request.coverageSourceMoleculeExpr ++ ") " ++
                      request.multiConfigurationLeftName ++ " " ++ request.multiConfigurationRightName ]
            | HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound =>
                [ "  have h : TetraStereo.Engine.graphDescriptorClassifierSoundClaim :="
                , "    " ++ dependencyTheoremName
                , "  exact h (" ++ request.coverageSourceAtomTypeExpr ++ ") (" ++
                    request.coverageSourceGraphExpr ++ ") " ++ request.graphConfigurationLeftName ++ " " ++
                      request.graphConfigurationRightName ]
            | HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal =>
                [ "  have h : TetraStereo.Engine.graphDescriptorClassifierRefusesUnresolvedClaim :="
                , "    " ++ dependencyTheoremName
                , "  exact h (" ++ request.coverageSourceAtomTypeExpr ++ ") (" ++
                    request.coverageSourceGraphExpr ++ ") " ++ request.graphConfigurationLeftName ++ " " ++
                      request.graphConfigurationRightName ]
      [ ""
      , "/-- The graph theorem family or concrete graph outcome is proved for the generated molecule source. -/"
      , "theorem " ++ theoremName ++ " :"
      , "    " ++ statement ++ " := by" ] ++ proofLines
  | _, _, _, _ => []

/-- Generated source expression for the public certificate's exact descriptor-result count. -/
def sourceDescriptorResultCountExpr (request : HostMoleculeTargetWitnessRequest) : String :=
  match request.witness.descriptorResult? with
  | none => "0"
  | some evidence =>
      evidence.result.countForSourceKeyExpr evidence.sourceKey request.coverageSourcePacketName
        request.coverageSourceAnnotationsName

/-- Generated source expression for the public certificate's graph-result center count. -/
def sourceGraphResultCenterCountExpr (request : HostMoleculeTargetWitnessRequest) : String :=
  match request.witness.graphResult? with
  | none => "0"
  | some _ =>
      "TetraStereo.Engine.HostMoleculeGraphResult.detectedTetrahedralCenterCount " ++
        request.coverageSourcePacketName

/-- Generated source expression for the public certificate's graph-result checked flag. -/
def sourceGraphResultCheckedExpr (request : HostMoleculeTargetWitnessRequest) : String :=
  match request.witness.graphResult? with
  | none => "false"
  | some evidence => leanBoolExpr evidence.resultChecked

/-- Proof lines for the readiness half of the generated checked witness theorem. -/
def readinessProofLines (request : HostMoleculeTargetWitnessRequest) : List String :=
  match request.dependencyTheoremNames with
  | [] =>
      [ "  · change " ++ request.definitionName ++ ".ready = true"
      , "    decide" ]
  | _ =>
      [ "  ·" ] ++ request.dependencyReferenceLines ++
        [ "    change " ++ request.definitionName ++ ".ready = true"
        , "    decide" ]

/-- Proposition proved by the generated checked witness theorem. -/
def witnessTheoremStatement (request : HostMoleculeTargetWitnessRequest) : String :=
  let resultStatements :=
    (match request.descriptorResultStatement? with
      | none => []
      | some statement => [statement]) ++
    (match request.graphResultStatement? with
      | none => []
      | some statement => [statement])
  String.intercalate " ∧ " ([request.definitionName ++ ".claim", request.coverageStatement] ++
    resultStatements)

/-- Proof lines for the generated checked witness theorem. -/
def witnessTheoremProofLines (request : HostMoleculeTargetWitnessRequest) : List String :=
  let resultTheoremNames :=
    (match request.descriptorResultTheoremName? with
      | none => []
      | some theoremName => [theoremName]) ++
    (match request.graphResultTheoremName? with
      | none => []
      | some theoremName => [theoremName])
  match resultTheoremNames with
  | [] =>
      [ "  constructor" ] ++ request.readinessProofLines ++
        [ "  · exact " ++ request.coverageTheoremName ]
  | theoremName :: _ =>
      [ "  constructor" ] ++ request.readinessProofLines ++
        [ "  · constructor"
        , "    · exact " ++ request.coverageTheoremName
        , "    · exact " ++ theoremName ]

/-- Proposition tail proved by the public target-certificate theorem after readiness. -/
def certificateProofTailStatement (request : HostMoleculeTargetWitnessRequest) : String :=
  request.witnessTheoremStatement

/-- Proof lines for the proposition tail of the public target-certificate theorem. -/
def certificateProofTailLines (request : HostMoleculeTargetWitnessRequest) : List String :=
  let resultTheoremNames :=
    (match request.descriptorResultTheoremName? with
      | none => []
      | some theoremName => [theoremName]) ++
    (match request.graphResultTheoremName? with
      | none => []
      | some theoremName => [theoremName])
  match resultTheoremNames with
  | [] =>
      [ "  · constructor"
      , "    · exact (" ++ request.theoremName ++ ").1"
      , "    · exact " ++ request.coverageTheoremName ]
  | theoremName :: _ =>
      [ "  · constructor"
      , "    · exact (" ++ request.theoremName ++ ").1"
      , "    · constructor"
      , "      · exact " ++ request.coverageTheoremName
      , "      · exact " ++ theoremName ]

/-- Render the generated target-witness theorem source. -/
def source (request : HostMoleculeTargetWitnessRequest) : String :=
  OneCenter.joinLines
    (request.imports.map (fun moduleName => "import " ++ moduleName) ++
      [""] ++ request.options ++ [""] ++ request.namespaceOpenLines ++
        [ ""
        , "/-- Molecule-specific target witness generated from a host analysis request. -/"
        , "def " ++ request.definitionName ++
            " : TetraStereo.Engine.HostMoleculeTargetWitness :="
        , request.witness.expr
        , ""
        , "/-- The observed witness count is recomputed from the generated molecule source. -/"
        , "theorem " ++ request.coverageTheoremName ++ " :"
        , "    " ++ request.coverageStatement ++ " :="
        , "  by decide"
        ] ++ request.descriptorResultTheoremLines ++ request.graphResultConfigurationLines ++
          request.graphResultTheoremLines ++
        [ ""
        , "/-- The generated target witness passes readiness and source-coverage checks. -/"
        , "theorem " ++ request.theoremName ++ " :"
        , "    " ++ request.witnessTheoremStatement ++ " := by"
        ] ++ request.witnessTheoremProofLines ++
        [ ""
        , "/-- Public molecule-specific target certificate generated from the target witness. -/"
        , "def " ++ request.certificateDefinitionName ++
            " : TetraStereo.Engine.HostMoleculeTargetCertificate :="
        , request.certificate.expr request.definitionName request.coverageSourceOwnerName
            (request.witness.coverageField.countExpr
              request.coverageSourcePacketName request.coverageSourceAnnotationsName)
            request.sourceDescriptorResultCountExpr request.sourceGraphResultCenterCountExpr
            request.sourceGraphResultCheckedExpr
        , ""
        , "/-- The public target certificate passes readiness and source-coverage checks. -/"
        , "theorem " ++ request.certificateTheoremName ++ " :"
        , "    " ++ request.certificateDefinitionName ++ ".ready = true ∧ " ++
            request.certificateProofTailStatement ++ " := by"
        , "  constructor"
        , "  · change " ++ request.certificateDefinitionName ++ ".ready = true"
        , "    decide"
        ] ++ request.certificateProofTailLines ++
        [ "" ] ++ request.namespaceCloseLines)

/-- Source-registry entry for this generated molecule-specific target witness. -/
def sourceEntry (request : HostMoleculeTargetWitnessRequest) : CertificateSourceEntry where
  key := request.key
  description := request.description
  fileName := request.fileName
  source := request.source

/-- Generated declaration names checked before writing a target-witness package. -/
def generatedLeanNames (request : HostMoleculeTargetWitnessRequest) : List String :=
  [ request.definitionName
  , request.coverageTheoremName
  , request.theoremName
  , request.certificateDefinitionName
  , request.certificateTheoremName ] ++
    (match request.descriptorResultTheoremName? with
    | none => []
    | some name => [name]) ++
    request.graphResultConfigurationNames ++
    (match request.graphResultTheoremName? with
    | none => []
    | some name => [name])

/-- Canonically named witness requests have identifier-safe generated declaration lists. -/
theorem generatedLeanNames_all_safe (request : HostMoleculeTargetWitnessRequest)
    (hsuffix : leanIdentifierRestSafe request.witness.nameSuffix = true)
    (hdefinition : request.definitionName = request.witness.expectedDefinitionName)
    (hcoverage : request.coverageTheoremName = request.witness.expectedCoverageTheoremName)
    (htheorem : request.theoremName = request.witness.expectedTheoremName) :
    request.generatedLeanNames.all leanIdentifierSegment? = true := by
  have hdefinitionSafe :=
    HostMoleculeTargetWitness.expectedDefinitionName_identifier_safe request.witness hsuffix
  have hcoverageSafe :=
    HostMoleculeTargetWitness.expectedCoverageTheoremName_identifier_safe request.witness hsuffix
  have htheoremSafe :=
    HostMoleculeTargetWitness.expectedTheoremName_identifier_safe request.witness hsuffix
  have hdescriptorSafe :=
    HostMoleculeTargetWitness.expectedDescriptorResultTheoremName_identifier_safe request.witness hsuffix
  have hgraphResultSafe :=
    HostMoleculeTargetWitness.expectedGraphResultTheoremName_identifier_safe request.witness hsuffix
  have hcertificateDefinitionSafe :=
    HostMoleculeTargetWitness.expectedCertificateDefinitionName_identifier_safe request.witness hsuffix
  have hcertificateTheoremSafe :=
    HostMoleculeTargetWitness.expectedCertificateTheoremName_identifier_safe request.witness hsuffix
  have hgraphLeftSafe : leanIdentifierSegment? request.graphConfigurationLeftName = true := by
    unfold graphConfigurationLeftName
    rw [hdefinition]
    simpa [HostMoleculeTargetWitness.expectedDefinitionName, String.append_assoc] using
      leanIdentifierSegment_host_parts_safe "MoleculeTargetWitness_" request.witness.nameSuffix
        "GraphConfigurationLeft" (by rfl) hsuffix (by rfl)
  have hgraphRightSafe : leanIdentifierSegment? request.graphConfigurationRightName = true := by
    unfold graphConfigurationRightName
    rw [hdefinition]
    simpa [HostMoleculeTargetWitness.expectedDefinitionName, String.append_assoc] using
      leanIdentifierSegment_host_parts_safe "MoleculeTargetWitness_" request.witness.nameSuffix
        "GraphConfigurationRight" (by rfl) hsuffix (by rfl)
  have hmultiLeftSafe : leanIdentifierSegment? request.multiConfigurationLeftName = true := by
    unfold multiConfigurationLeftName
    rw [hdefinition]
    simpa [HostMoleculeTargetWitness.expectedDefinitionName, String.append_assoc] using
      leanIdentifierSegment_host_parts_safe "MoleculeTargetWitness_" request.witness.nameSuffix
        "MultiConfigurationLeft" (by rfl) hsuffix (by rfl)
  have hmultiRightSafe : leanIdentifierSegment? request.multiConfigurationRightName = true := by
    unfold multiConfigurationRightName
    rw [hdefinition]
    simpa [HostMoleculeTargetWitness.expectedDefinitionName, String.append_assoc] using
      leanIdentifierSegment_host_parts_safe "MoleculeTargetWitness_" request.witness.nameSuffix
        "MultiConfigurationRight" (by rfl) hsuffix (by rfl)
  have hcertificateDefinition :
      request.certificateDefinitionName = request.witness.expectedCertificateDefinitionName := rfl
  have hcertificateTheorem :
      request.certificateTheoremName = request.witness.expectedCertificateTheoremName := rfl
  have hdescriptorNames :
      (match request.descriptorResultTheoremName? with
        | none => []
        | some name => [name]).all leanIdentifierSegment? = true := by
    unfold descriptorResultTheoremName?
    cases hdescriptor : request.witness.descriptorResult? <;>
      simp [hdescriptorSafe]
  have hgraphConfigurations :
      request.graphResultConfigurationNames.all leanIdentifierSegment? = true := by
    unfold graphResultConfigurationNames
    cases hgraph : request.witness.graphResult? with
    | none => simp
    | some evidence =>
        cases evidence with
        | mk kind sourceCenterCount requiredCenterCount configurationPolicy expectedOutcome?
            outcomePrecondition outcomeChecked resultChecked =>
            cases kind <;>
              simp [hgraphLeftSafe, hgraphRightSafe, hmultiLeftSafe, hmultiRightSafe]
  have hgraphResultNames :
      (match request.graphResultTheoremName? with
        | none => []
        | some name => [name]).all leanIdentifierSegment? = true := by
    unfold graphResultTheoremName?
    cases hgraph : request.witness.graphResult? <;>
      simp [hgraphResultSafe]
  unfold generatedLeanNames
  simp [List.all_append, hdefinition, hcoverage, htheorem, hcertificateDefinition,
    hcertificateTheorem, hdefinitionSafe, hcoverageSafe, htheoremSafe,
    hcertificateDefinitionSafe, hcertificateTheoremSafe, hdescriptorNames,
    hgraphConfigurations, hgraphResultNames]

/-- Validate target-witness package names and source-module metadata. -/
def validateMetadataShape (request : HostMoleculeTargetWitnessRequest) : Except String Unit := do
  requireHostRequestShape (request.key ≠ "")
    "host molecule target witness key must not be empty"
  requireHostRequestShape (request.description ≠ "")
    "host molecule target witness description must not be empty"
  validateNamespacePath "namespacePath" request.namespacePath
  validateModuleNames "imports" request.imports
  validateOptionLines "options" request.options
  validateImportableLeanFileName "fileName" request.fileName
  validateLeanNames "generated target-witness names" request.generatedLeanNames
  validateModuleNames "coverageSourceModule" [request.coverageSourceModule]
  validateModuleNames "coverageSourcePacketName" [request.coverageSourcePacketName]
  validateModuleNames "coverageSourceAnnotationsName" [request.coverageSourceAnnotationsName]
  validateModuleNames "coverageSourceBlueprintName" [request.coverageSourceBlueprintName]
  validateModuleNames "coverageSourceOwnerName" [request.coverageSourceOwnerName]
  requireHostRequestShape
    (request.coverageSourceOwnerName == request.expectedCoverageSourceOwnerName)
    "host molecule target witness coverage owner declaration is not canonical for the source module"
  requireHostRequestShape request.coverageSourceNamesReady
    "host molecule target witness source declarations must belong to the coverage source module"

/-- Validate canonical witness identity, declarations, and theorem dependencies. -/
def validateIdentityShape (request : HostMoleculeTargetWitnessRequest) : Except String Unit := do
  requireHostRequestShape (request.key = request.witness.expectedPackageKey)
    "host molecule target witness package key does not match witness identity"
  requireHostRequestShape (request.fileName = request.witness.expectedFileName)
    "host molecule target witness fileName does not match witness identity"
  requireHostRequestShape (request.definitionName = request.witness.expectedDefinitionName)
    "host molecule target witness definitionName does not match witness identity"
  requireHostRequestShape (request.coverageTheoremName = request.witness.expectedCoverageTheoremName)
    "host molecule target witness coverageTheoremName does not match witness identity"
  requireHostRequestShape (request.theoremName = request.witness.expectedTheoremName)
    "host molecule target witness theoremName does not match witness identity"
  requireHostRequestShape (request.witness.theoremFamilyKeys = request.witness.expectedTheoremFamilyKeys)
    "host molecule target witness theorem-family keys do not match witness coverage field"
  requireHostRequestShape (request.definitionName ≠ request.theoremName)
    "host molecule target witness has colliding definition and theorem names"
  requireHostRequestShape (!hasDuplicateStrings request.declarationNames)
    "host molecule target witness contains duplicate generated declarations"
  validateModuleNames "dependencyTheoremNames" request.dependencyTheoremNames
  requireHostRequestShape
    (request.dependencyTheoremNames.length = request.witness.theoremFamilyKeys.length)
    "host molecule target witness dependency theorem count does not match theorem-family keys"
  requireHostRequestShape (!hasDuplicateStrings request.dependencyTheoremNames)
    "host molecule target witness contains duplicate dependency theorem names"

/-- Validate executable witness and public-certificate readiness. -/
def validateReadinessShape (request : HostMoleculeTargetWitnessRequest) : Except String Unit := do
  requireHostRequestShape request.witness.ready
    "host molecule target witness does not satisfy executable readiness checks"
  requireHostRequestShape request.certificate.ready
    "host molecule target certificate does not satisfy executable readiness checks"

/-- Validate host-supplied metadata and executable witness readiness. -/
def validateGeneratedShape (request : HostMoleculeTargetWitnessRequest) : Except String Unit := do
  request.validateMetadataShape
  request.validateIdentityShape
  request.validateReadinessShape

/-- Source path for this generated target-witness package under an output root. -/
def packageSourcePath (request : HostMoleculeTargetWitnessRequest) (packageRoot : String) :
    System.FilePath :=
  System.FilePath.mk
    (packageRoot ++ "/" ++ HostOfficialStereoRequest.pathStem request.namespacePath ++ "/" ++
      request.fileName)

/-- Write this generated target-witness package to an importable Lean file. -/
def writePackageSource (request : HostMoleculeTargetWitnessRequest) (packageRoot : String) :
    IO System.FilePath := do
  match request.validateGeneratedShape with
  | Except.ok () => pure ()
  | Except.error message => throw (IO.userError message)
  let path := request.packageSourcePath packageRoot
  writeLeanSourceFile path request.sourceEntry.source

end HostMoleculeTargetWitnessRequest

/-- Host-facing request for a generated analysis-suite package. -/
structure HostAnalysisSuiteRequest where
  key : String
  description : String
  officialStereoRequests : List HostOfficialStereoRequest := []
  claimRequests : List HostStereoClaimRequest := []
  witnessRequests : List HostMoleculeTargetWitnessRequest := []
  namespacePath : List String := ["TetraStereoGenerated", "HostSuites"]
  fileName : String := "HostAnalysisSuite.lean"
  theoremName : String := "host_analysis_suite_checked"
  options : List String := ["set_option maxHeartbeats 1000000"]

namespace HostAnalysisSuiteRequest

/-- Import module for one generated official-stereo certificate source. -/
def officialCertificateModuleName (request : HostOfficialStereoRequest) : String :=
  generatedModuleName request.certificateNamespacePath request.certificateFileName

/-- Theorem name for one generated official-stereo certificate source. -/
def officialCertificateTheoremName (request : HostOfficialStereoRequest) : String :=
  leanQualifiedName request.certificateNamespacePath request.certificateTheoremName

/-- Import module for one generated broad host-claim source. -/
def claimModuleName (request : HostStereoClaimRequest) : String :=
  generatedModuleName request.namespacePath request.fileName

/-- Theorem name for one generated broad host-claim source. -/
def claimTheoremName (request : HostStereoClaimRequest) : String :=
  leanQualifiedName request.namespacePath request.theoremName

/-- Import module for one generated molecule-specific target witness source. -/
def witnessModuleName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.moduleName

/-- Theorem name for one generated molecule-specific target witness source. -/
def witnessTheoremName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.theoremFullName

/-- Public target-certificate theorem name for one generated molecule-specific target source. -/
def witnessCertificateTheoremName (request : HostMoleculeTargetWitnessRequest) : String :=
  request.certificateTheoremFullName

/-- Importable module name for this suite's generated manifest. -/
def manifestModuleName (request : HostAnalysisSuiteRequest) : String :=
  generatedModuleName request.namespacePath request.fileName

/-- Generated module imports required by this suite's manifest. -/
def manifestImportModules (request : HostAnalysisSuiteRequest) : List String :=
  (request.officialStereoRequests.map officialCertificateModuleName) ++
    (request.claimRequests.map claimModuleName) ++
      (request.witnessRequests.map witnessModuleName)

/-- Generated theorem references checked by this suite's manifest. -/
def manifestTheoremNames (request : HostAnalysisSuiteRequest) : List String :=
  (request.officialStereoRequests.map officialCertificateTheoremName) ++
    (request.claimRequests.map claimTheoremName) ++
      (request.witnessRequests.map witnessCertificateTheoremName)

/-- Fully-qualified theorem name emitted by this suite's generated manifest. -/
def manifestTheoremFullName (request : HostAnalysisSuiteRequest) : String :=
  leanQualifiedName request.namespacePath request.theoremName

/-- Fully-qualified generated theorem names visible after importing the whole suite. -/
def suiteTheoremNames (request : HostAnalysisSuiteRequest) : List String :=
  request.manifestTheoremNames ++ [request.manifestTheoremFullName]

/-- Fully-qualified generated target-witness definition names visible after importing the suite. -/
def witnessDefinitionNames (request : HostAnalysisSuiteRequest) : List String :=
  request.witnessRequests.map fun witnessRequest => witnessRequest.definitionFullName

/-- Fully-qualified generated target-certificate definition names visible after importing the suite. -/
def witnessCertificateDefinitionNames (request : HostAnalysisSuiteRequest) : List String :=
  request.witnessRequests.map fun witnessRequest => witnessRequest.certificateDefinitionFullName

/-- Fully-qualified declarations emitted by generated target-witness packages. -/
def witnessDeclarationNames (request : HostAnalysisSuiteRequest) : List String :=
  request.witnessRequests.flatMap fun witnessRequest => witnessRequest.declarationNames

/-- Generated host module names required by official-stereo certificate modules. -/
def officialHostModuleNames (request : HostAnalysisSuiteRequest) : List String :=
  request.officialStereoRequests.map HostOfficialStereoRequest.moduleName

/-- Find an official host request included in this suite by generated module name. -/
def officialRequestByModule? (request : HostAnalysisSuiteRequest) (moduleName : String) :
    Option HostOfficialStereoRequest :=
  request.officialStereoRequests.find? fun officialRequest => officialRequest.moduleName == moduleName

/-- Canonical generated packet declaration for an included official host request. -/
def officialCoveragePacketName (request : HostOfficialStereoRequest) : String :=
  request.fullName request.packetName

/-- Canonical generated annotations expression for an included official host request. -/
def officialCoverageAnnotationsName (request : HostOfficialStereoRequest) : String :=
  request.fullName request.blueprintName ++ ".annotations"

/-- Canonical generated blueprint declaration for an included official host request. -/
def officialCoverageBlueprintName (request : HostOfficialStereoRequest) : String :=
  request.fullName request.blueprintName

/-- Canonical generated owner-key declaration for an included official host request. -/
def officialCoverageOwnerRequestKeyName (request : HostOfficialStereoRequest) : String :=
  request.fullName request.ownerRequestKeyName

/-- Fully-qualified host declarations imported transitively by official-stereo certificates. -/
def officialHostDeclarationNames (request : HostAnalysisSuiteRequest) : List String :=
  request.officialStereoRequests.flatMap HostOfficialStereoRequest.hostDeclarationNames

/-- Fully-qualified declarations generated by the suite and its imported generated packages. -/
def suiteDeclarationNames (request : HostAnalysisSuiteRequest) : List String :=
  request.officialHostDeclarationNames ++
    (request.officialStereoRequests.map officialCertificateTheoremName) ++
      (request.claimRequests.map claimTheoremName) ++
        request.witnessDeclarationNames ++
          [request.manifestTheoremFullName]

/-- Host-facing keys for official-stereo packages included in the suite. -/
def officialPackageKeys (request : HostAnalysisSuiteRequest) : List String :=
  request.officialStereoRequests.map fun officialRequest => officialRequest.key

/-- Host-facing keys for broad claim packages included in the suite. -/
def claimPackageKeys (request : HostAnalysisSuiteRequest) : List String :=
  request.claimRequests.map fun claimRequest => claimRequest.key

/-- Find a broad claim request included in this suite by host-facing key. -/
def claimRequestByKey? (request : HostAnalysisSuiteRequest) (key : String) :
    Option HostStereoClaimRequest :=
  request.claimRequests.find? fun claimRequest => claimRequest.key == key

/-- Generated claim modules required by a target witness's theorem-family keys. -/
def claimModulesForKeys (request : HostAnalysisSuiteRequest) (keys : List String) : List String :=
  keys.filterMap fun key =>
    (request.claimRequestByKey? key).map fun claimRequest =>
      HostAnalysisSuiteRequest.claimModuleName claimRequest

/-- Generated claim theorems required by a target witness's theorem-family keys. -/
def claimTheoremsForKeys (request : HostAnalysisSuiteRequest) (keys : List String) : List String :=
  keys.filterMap fun key =>
    (request.claimRequestByKey? key).map fun claimRequest =>
      HostAnalysisSuiteRequest.claimTheoremName claimRequest

/-- Exact import list expected for a suite-authenticated target witness. -/
def expectedWitnessImports
    (request : HostAnalysisSuiteRequest) (witnessRequest : HostMoleculeTargetWitnessRequest) :
    List String :=
  ["TetraStereo.Engine.HostAnalysisRequestBuilder", witnessRequest.coverageSourceModule] ++
    request.claimModulesForKeys witnessRequest.witness.theoremFamilyKeys

/-- Exact dependency theorem list expected for a suite-authenticated target witness. -/
def expectedWitnessDependencyTheorems
    (request : HostAnalysisSuiteRequest) (witnessRequest : HostMoleculeTargetWitnessRequest) :
    List String :=
  request.claimTheoremsForKeys witnessRequest.witness.theoremFamilyKeys

/-- Host-facing keys for molecule-specific target witness packages included in the suite. -/
def witnessPackageKeys (request : HostAnalysisSuiteRequest) : List String :=
  request.witnessRequests.map fun witnessRequest => witnessRequest.key

/-- Host-facing keys for public target certificates included in the suite. -/
def witnessCertificateKeys (request : HostAnalysisSuiteRequest) : List String :=
  request.witnessRequests.map fun witnessRequest => witnessRequest.certificate.key

/-- Host-facing keys for every generated child package included in the suite. -/
def packageKeys (request : HostAnalysisSuiteRequest) : List String :=
  request.officialPackageKeys ++ request.claimPackageKeys ++ request.witnessPackageKeys ++
    request.witnessCertificateKeys

/-- Namespace-open lines for the generated suite manifest. -/
def namespaceOpenLines (request : HostAnalysisSuiteRequest) : List String :=
  request.namespacePath.map fun namespaceName => "namespace " ++ namespaceName

/-- Namespace-close lines for the generated suite manifest. -/
def namespaceCloseLines (request : HostAnalysisSuiteRequest) : List String :=
  request.namespacePath.reverse.map fun namespaceName => "end " ++ namespaceName

/-- Validate the suite-level fields that precede nested generated-package checks. -/
def validateHeaderShape (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape (hostPackageKeySegment? request.key)
    "host analysis suite key must be one package-key segment"
  requireHostRequestShape (request.description != "")
    "host analysis suite description must not be empty"
  requireHostRequestShape
    (!request.officialStereoRequests.isEmpty || !request.claimRequests.isEmpty ||
      !request.witnessRequests.isEmpty)
    "host analysis suite must contain at least one generated package"
  validateNamespacePath "namespacePath" request.namespacePath
  validateOptionLines "options" request.options
  validateImportableLeanFileName "fileName" request.fileName
  validateLeanNames "generated theorem names" [request.theoremName]

/-- Validate every nested official-stereochemistry package in suite order. -/
def validateOfficialRequestShapes (request : HostAnalysisSuiteRequest) : Except String Unit := do
  for officialRequest in request.officialStereoRequests do
    officialRequest.validateGeneratedShape
    requireHostRequestShape (officialRequest.ownerRequestKey == request.key)
      "host analysis suite official-stereo package owner does not match suite request key"
    requireHostRequestShape (hostPackageKeySegment? officialRequest.packageKeySuffix)
      "host analysis suite official-stereo package suffix is not one package-key segment"
    requireHostRequestShape
      (officialRequest.key == hostScopedPackageKey request.key officialRequest.packageKeySuffix)
      "host analysis suite official-stereo package key is not canonical for its owner"
    validateImportableLeanFileName
      ("certificateFileName for " ++ officialRequest.key) officialRequest.certificateFileName

/-- Validate every nested broad-claim package in suite order. -/
def validateClaimRequestShapes (request : HostAnalysisSuiteRequest) : Except String Unit := do
  for claimRequest in request.claimRequests do
    claimRequest.validateGeneratedShape
    requireHostRequestShape
      (claimRequest.key = hostAnalysisClaimPackageKey request.key claimRequest.target)
      "host analysis suite claim package key is not canonical for its owner"
    validateImportableLeanFileName
      ("claim fileName for " ++ claimRequest.key) claimRequest.fileName

/-- Validate the graph-result evidence attached to one suite-authenticated target witness. -/
def validateWitnessGraphResultShape
    (_request : HostAnalysisSuiteRequest) (witnessRequest : HostMoleculeTargetWitnessRequest)
    (coverageSourceRequest : HostOfficialStereoRequest) : Except String Unit := do
  if witnessRequest.witness.coverageField.requiresGraphResult then
    let sourceCenterCount :=
      HostMoleculeGraphResult.detectedTetrahedralCenterCount coverageSourceRequest.packet
    requireHostRequestShape
      (witnessRequest.witness.observedCount = sourceCenterCount)
      "host analysis suite graph target witness count does not match source host module"
    match witnessRequest.witness.graphResult? with
    | none =>
        throw "host analysis suite graph target witness is missing graph-result evidence"
    | some evidence =>
        requireHostRequestShape
          (evidence.sourceCenterCount = sourceCenterCount)
          "host analysis suite graph-result evidence count does not match source host module"
        requireHostRequestShape
          (evidence.requiredCenterCount = witnessRequest.witness.requiredCount)
          "host analysis suite graph-result required center count does not match witness requirement"
  else
    pure ()

/-- Validate a target witness against the included host module that owns its coverage source. -/
def validateWitnessCoverageSourceShape
    (request : HostAnalysisSuiteRequest) (witnessRequest : HostMoleculeTargetWitnessRequest)
    (coverageSourceRequest : HostOfficialStereoRequest) : Except String Unit := do
  requireHostRequestShape
    (coverageSourceRequest.ownerRequestKey == witnessRequest.witness.requestKey)
    "host analysis suite target witness coverage source owner does not match the witness request"
  requireHostRequestShape
    (coverageSourceRequest.key ==
      hostScopedPackageKey
        coverageSourceRequest.ownerRequestKey coverageSourceRequest.packageKeySuffix)
    "host analysis suite target witness coverage source key is not canonical for its owner"
  requireHostRequestShape
    (witnessRequest.coverageSourcePacketName =
      HostAnalysisSuiteRequest.officialCoveragePacketName coverageSourceRequest)
    "host analysis suite target witness coverage packet does not match source host module"
  requireHostRequestShape
    (witnessRequest.coverageSourceAnnotationsName =
      HostAnalysisSuiteRequest.officialCoverageAnnotationsName coverageSourceRequest)
    "host analysis suite target witness coverage annotations do not match source host module"
  requireHostRequestShape
    (witnessRequest.coverageSourceBlueprintName =
      HostAnalysisSuiteRequest.officialCoverageBlueprintName coverageSourceRequest)
    "host analysis suite target witness coverage blueprint does not match source host module"
  requireHostRequestShape
    (witnessRequest.coverageSourceOwnerName =
      HostAnalysisSuiteRequest.officialCoverageOwnerRequestKeyName coverageSourceRequest)
    "host analysis suite target witness coverage owner declaration does not match source host module"
  request.validateWitnessGraphResultShape witnessRequest coverageSourceRequest

/-- Validate one theorem-family dependency key against its included broad-claim package. -/
def validateWitnessClaimKeyShape
    (request : HostAnalysisSuiteRequest) (key : String) : Except String Unit := do
  match request.claimRequestByKey? key with
  | none =>
      throw "host analysis suite contains target witness dependency key absent from claims"
  | some claimRequest =>
      requireHostRequestShape (key = hostAnalysisClaimPackageKey request.key claimRequest.target)
        "host analysis suite target witness dependency key is not canonical for its claim target"

/-- Validate theorem-family dependency keys in their supplied order. -/
def validateWitnessClaimKeyList (request : HostAnalysisSuiteRequest) :
    List String → Except String Unit
  | [] => pure ()
  | key :: rest => do
      request.validateWitnessClaimKeyShape key
      request.validateWitnessClaimKeyList rest

/-- Validate a target witness's exact included claim packages, imports, and theorem dependencies. -/
def validateWitnessDependencyShape
    (request : HostAnalysisSuiteRequest) (witnessRequest : HostMoleculeTargetWitnessRequest) :
    Except String Unit := do
  requireHostRequestShape
    (witnessRequest.witness.theoremFamilyKeys.all fun key => request.claimPackageKeys.contains key)
    "host analysis suite contains target witness dependency keys absent from claim packages"
  request.validateWitnessClaimKeyList witnessRequest.witness.theoremFamilyKeys
  requireHostRequestShape
    (witnessRequest.imports = request.expectedWitnessImports witnessRequest)
    "host analysis suite target witness imports do not match included claim packages"
  requireHostRequestShape
    (witnessRequest.dependencyTheoremNames =
      request.expectedWitnessDependencyTheorems witnessRequest)
    "host analysis suite target witness theorem dependencies do not match included claim packages"

/-- Validate one target-witness package and its exact suite dependencies. -/
def validateWitnessRequestShape
    (request : HostAnalysisSuiteRequest) (witnessRequest : HostMoleculeTargetWitnessRequest) :
    Except String Unit := do
  witnessRequest.validateGeneratedShape
  requireHostRequestShape (witnessRequest.witness.requestKey == request.key)
    "host analysis suite contains a target witness for a different request key"
  requireHostRequestShape
    (request.officialHostModuleNames.contains witnessRequest.coverageSourceModule)
    "host analysis suite target witness coverage source is not an included host module"
  match request.officialRequestByModule? witnessRequest.coverageSourceModule with
  | none =>
      throw "host analysis suite target witness coverage source module is absent"
  | some coverageSourceRequest =>
      request.validateWitnessCoverageSourceShape witnessRequest coverageSourceRequest
  request.validateWitnessDependencyShape witnessRequest

/-- Validate a list of target-witness packages in order. -/
def validateWitnessRequestList (request : HostAnalysisSuiteRequest) :
    List HostMoleculeTargetWitnessRequest → Except String Unit
  | [] => pure ()
  | witnessRequest :: rest => do
      request.validateWitnessRequestShape witnessRequest
      request.validateWitnessRequestList rest

/-- Validate every target-witness package and its exact suite dependencies in suite order. -/
def validateWitnessRequestShapes (request : HostAnalysisSuiteRequest) : Except String Unit :=
  request.validateWitnessRequestList request.witnessRequests

/-- Validate uniqueness of generated host module names. -/
def validateUniqueOfficialHostModules (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape (!hasDuplicateStrings request.officialHostModuleNames)
    "host analysis suite contains duplicate generated host modules"

/-- Validate uniqueness of generated package import module names. -/
def validateUniqueManifestImportModules (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape (!hasDuplicateStrings request.manifestImportModules)
    "host analysis suite contains duplicate generated import modules"

/-- Validate uniqueness of generated theorem names. -/
def validateUniqueSuiteTheoremNames (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape (!hasDuplicateStrings request.suiteTheoremNames)
    "host analysis suite contains duplicate generated theorem names"

/-- Validate uniqueness of every generated declaration name. -/
def validateUniqueSuiteDeclarationNames (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape (!hasDuplicateStrings request.suiteDeclarationNames)
    "host analysis suite contains duplicate generated declaration names"

/-- Validate uniqueness of every generated child package key. -/
def validateUniquePackageKeys (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape (!hasDuplicateStrings request.packageKeys)
    "host analysis suite contains duplicate child package keys"

/-- Validate separation between host declarations and suite theorem declarations. -/
def validateHostSuiteDeclarationSeparation (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape
    (!stringListsIntersect request.officialHostDeclarationNames request.suiteTheoremNames)
    "host analysis suite contains colliding host and suite theorem declarations"

/-- Validate separation between host modules and generated package import modules. -/
def validateHostImportModuleSeparation (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape
    (!stringListsIntersect request.officialHostModuleNames request.manifestImportModules)
    "host analysis suite contains colliding generated host and imported package modules"

/-- Validate that the manifest module does not collide with an imported package module. -/
def validateManifestImportModuleSeparation (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape (!request.manifestImportModules.contains request.manifestModuleName)
    "host analysis suite manifest module collides with a generated package module"

/-- Validate that the manifest module does not collide with a generated host module. -/
def validateManifestHostModuleSeparation (request : HostAnalysisSuiteRequest) : Except String Unit := do
  requireHostRequestShape (!request.officialHostModuleNames.contains request.manifestModuleName)
    "host analysis suite manifest module collides with a generated host module"

/-- Validate uniqueness of suite-wide generated modules and theorem names. -/
def validateGlobalModuleNameShape (request : HostAnalysisSuiteRequest) : Except String Unit := do
  request.validateUniqueOfficialHostModules
  request.validateUniqueManifestImportModules
  request.validateUniqueSuiteTheoremNames

/-- Validate uniqueness and host separation of generated declaration and package names. -/
def validateGlobalDeclarationNameShape (request : HostAnalysisSuiteRequest) : Except String Unit := do
  request.validateUniqueSuiteDeclarationNames
  request.validateUniquePackageKeys
  request.validateHostSuiteDeclarationSeparation

/-- Validate separation among generated host, package, and manifest module names. -/
def validateGlobalModuleSeparationShape (request : HostAnalysisSuiteRequest) : Except String Unit := do
  request.validateHostImportModuleSeparation
  request.validateManifestImportModuleSeparation
  request.validateManifestHostModuleSeparation

/-- Validate suite-wide uniqueness and cross-family generated-name separation. -/
def validateGlobalNameShape (request : HostAnalysisSuiteRequest) : Except String Unit := do
  request.validateGlobalModuleNameShape
  request.validateGlobalDeclarationNameShape
  request.validateGlobalModuleSeparationShape

/-- Validate suite-level generated names and all nested request shapes needed for imports. -/
def validateGeneratedShape (request : HostAnalysisSuiteRequest) : Except String Unit := do
  request.validateHeaderShape
  request.validateOfficialRequestShapes
  request.validateClaimRequestShapes
  request.validateWitnessRequestShapes
  request.validateGlobalNameShape

/-- Source path for this generated suite manifest under a package root. -/
def manifestPath (request : HostAnalysisSuiteRequest) (packageRoot : String) :
    System.FilePath :=
  System.FilePath.mk
    (packageRoot ++ "/" ++ HostOfficialStereoRequest.pathStem request.namespacePath ++ "/" ++
      request.fileName)

/-- Private generated-olean root for modules imported by this suite manifest. -/
def manifestOLeanRoot (_request : HostAnalysisSuiteRequest) (packageRoot : String) : String :=
  if leanPathEntryHasSeparator packageRoot then
    "/tmp/tetrastereo-generated-suite-olean/" ++ leanPathSafeRootName packageRoot
  else
    packageRoot ++ "/.suite-olean"

/-- OLean path for an importable generated file under a generated-olean root. -/
def generatedFileOLeanPath
    (oleanRoot : String) (namespacePath : List String) (fileName : String) :
    System.FilePath :=
  HostOfficialStereoRequest.leanOLeanPathOfNamespace oleanRoot
    (namespacePath ++ [generatedLeanFileStem fileName])

/-- Compiled olean path for one generated host module imported by a suite certificate. -/
def officialHostModuleOLeanPath
    (suite : HostAnalysisSuiteRequest) (packageRoot : String)
    (request : HostOfficialStereoRequest) : System.FilePath :=
  HostOfficialStereoRequest.leanOLeanPathOfNamespace
    (suite.manifestOLeanRoot packageRoot) request.namespacePath

/-- Compiled olean path for one generated official-stereo certificate imported by the manifest. -/
def officialCertificateOLeanPath
    (suite : HostAnalysisSuiteRequest) (packageRoot : String)
    (request : HostOfficialStereoRequest) : System.FilePath :=
  generatedFileOLeanPath (suite.manifestOLeanRoot packageRoot)
    request.certificateNamespacePath request.certificateFileName

/-- Compiled olean path for one generated broad host claim imported by the manifest. -/
def claimOLeanPath
    (suite : HostAnalysisSuiteRequest) (packageRoot : String)
    (request : HostStereoClaimRequest) : System.FilePath :=
  generatedFileOLeanPath (suite.manifestOLeanRoot packageRoot)
    request.namespacePath request.fileName

/-- Compiled olean path for one generated molecule-specific target witness imported by the manifest. -/
def witnessOLeanPath
    (suite : HostAnalysisSuiteRequest) (packageRoot : String)
    (request : HostMoleculeTargetWitnessRequest) : System.FilePath :=
  generatedFileOLeanPath (suite.manifestOLeanRoot packageRoot)
    request.namespacePath request.fileName

/-- Import lines for the generated suite manifest. -/
def importLines (request : HostAnalysisSuiteRequest) : List String :=
  request.manifestImportModules.map fun moduleName => "import " ++ moduleName

/-- Proof lines that make the manifest depend on each generated theorem in the suite. -/
def theoremReferenceLines (request : HostAnalysisSuiteRequest) : List String :=
  request.manifestTheoremNames.map fun theoremName => "  have _ := " ++ theoremName

/-- Render the generated suite manifest source. -/
def manifestSource (request : HostAnalysisSuiteRequest) : String :=
  OneCenter.joinLines
    (request.importLines ++ [""] ++ request.options ++ [""] ++
      request.namespaceOpenLines ++ [""] ++
        [ "/-- This generated manifest imports and references every theorem in the host suite. -/"
        , "theorem " ++ request.theoremName ++ " : True := by" ] ++
          request.theoremReferenceLines ++ ["  trivial", ""] ++ request.namespaceCloseLines)

/-- File paths written for a generated host analysis suite package. -/
structure PackagePaths where
  officialPackagePaths : List HostOfficialStereoRequest.PackagePaths
  claimPaths : List System.FilePath
  witnessPaths : List System.FilePath
  manifestPath : System.FilePath

/-- Write all generated package files and the generated suite manifest. -/
def writePackageSources (request : HostAnalysisSuiteRequest) (packageRoot : String) :
    IO PackagePaths := do
  match request.validateGeneratedShape with
  | Except.ok () => pure ()
  | Except.error message => throw (IO.userError message)
  let mut officialPackagePaths := []
  for officialRequest in request.officialStereoRequests do
    let paths ← officialRequest.writePackageSources packageRoot
    officialPackagePaths := officialPackagePaths.concat paths
  let mut claimPaths := []
  for claimRequest in request.claimRequests do
    let path ← claimRequest.writePackageSource packageRoot
    claimPaths := claimPaths.concat path
  let mut witnessPaths := []
  for witnessRequest in request.witnessRequests do
    let path ← witnessRequest.writePackageSource packageRoot
    witnessPaths := witnessPaths.concat path
  let manifestPath ← writeLeanSourceFile (request.manifestPath packageRoot) request.manifestSource
  pure
    { officialPackagePaths := officialPackagePaths
      claimPaths := claimPaths
      witnessPaths := witnessPaths
      manifestPath := manifestPath }

/-- Result of verifying all generated files in a host analysis suite. -/
structure VerificationResult where
  paths : PackagePaths
  officialHostModuleResults : List CertificateVerificationResult
  officialCertificateCompileResults : List CertificateVerificationResult
  claimCompileResults : List CertificateVerificationResult
  witnessCompileResults : List CertificateVerificationResult
  manifestResult : CertificateVerificationResult

namespace VerificationResult

/-- Whether every verifier/compiler step in the suite succeeded. -/
def passed (result : VerificationResult) : Bool :=
  result.officialHostModuleResults.all CertificateVerificationResult.passed &&
    result.officialCertificateCompileResults.all CertificateVerificationResult.passed &&
      result.claimCompileResults.all CertificateVerificationResult.passed &&
        result.witnessCompileResults.all CertificateVerificationResult.passed &&
          result.manifestResult.passed

end VerificationResult

/-- Generated roots required for the suite manifest to import generated modules. -/
def manifestLeanPathRoots (request : HostAnalysisSuiteRequest) (packageRoot : String) :
    List String :=
  [request.manifestOLeanRoot packageRoot]

/-- Write and verify every generated file in this host analysis suite. -/
def writeAndVerifyPackageSources
    (request : HostAnalysisSuiteRequest) (packageRoot : String) :
    IO VerificationResult := do
  let paths ← request.writePackageSources packageRoot
  let mut officialHostModuleResults := []
  let mut officialCertificateCompileResults := []
  for pair in List.zip request.officialStereoRequests paths.officialPackagePaths do
    let officialRequest := pair.fst
    let officialPaths := pair.snd
    let hostResult ← compileLeanModuleFileWithRoot packageRoot
      officialPaths.hostModulePath
      (request.officialHostModuleOLeanPath packageRoot officialRequest)
    officialHostModuleResults := officialHostModuleResults.concat hostResult
    let certificateResult ← compileLeanModuleFileWithRootAndLeanPathRoots packageRoot
      [request.manifestOLeanRoot packageRoot] officialPaths.certificatePath
      (request.officialCertificateOLeanPath packageRoot officialRequest)
    officialCertificateCompileResults :=
      officialCertificateCompileResults.concat certificateResult
  let mut claimCompileResults := []
  for pair in List.zip request.claimRequests paths.claimPaths do
    let claimRequest := pair.fst
    let path := pair.snd
    let result ← compileLeanModuleFileWithRoot packageRoot path
      (request.claimOLeanPath packageRoot claimRequest)
    claimCompileResults := claimCompileResults.concat result
  let mut witnessCompileResults := []
  for pair in List.zip request.witnessRequests paths.witnessPaths do
    let witnessRequest := pair.fst
    let path := pair.snd
    let result ← compileLeanModuleFileWithRootAndLeanPathRoots packageRoot
      [request.manifestOLeanRoot packageRoot] path
      (request.witnessOLeanPath packageRoot witnessRequest)
    witnessCompileResults := witnessCompileResults.concat result
  let manifestResult ← verifyLeanCertificateFileWithRootAndLeanPathRoots packageRoot
    (request.manifestLeanPathRoots packageRoot) paths.manifestPath
  pure
    { paths := paths
      officialHostModuleResults := officialHostModuleResults
      officialCertificateCompileResults := officialCertificateCompileResults
      claimCompileResults := claimCompileResults
      witnessCompileResults := witnessCompileResults
      manifestResult := manifestResult }

end HostAnalysisSuiteRequest

end
end Engine
end TetraStereo
