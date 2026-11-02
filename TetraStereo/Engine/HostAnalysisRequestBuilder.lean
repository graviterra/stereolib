import TetraStereo.Engine.HostAnalysisSuiteCompiler

set_option autoImplicit false

namespace TetraStereo
namespace Engine

open OneCenter

noncomputable section











/-- Broad theorem-family claim inclusion policy for a molecule-derived host analysis. -/
inductive HostBroadClaimPolicy where
  | none
  | selected (targets : List HostStereoClaimTarget)
  | all
  deriving DecidableEq, Repr

namespace HostBroadClaimPolicy

/-- The concrete theorem-family targets included by this policy. -/
def targets : HostBroadClaimPolicy → List HostStereoClaimTarget
  | none => []
  | selected targets => targets
  | all => HostStereoClaimTarget.all

end HostBroadClaimPolicy

/-- Whether a list contains duplicate values using propositional equality. -/
def hasDuplicateByEquality {α : Type*} [DecidableEq α] : List α → Bool
  | [] => false
  | value :: rest => listContainsByEquality value rest || hasDuplicateByEquality rest

/-- Whether a list of broad theorem-family targets contains a target. -/
def hostStereoClaimTargetListContains (target : HostStereoClaimTarget) :
    List HostStereoClaimTarget → Bool :=
  listContainsByEquality target

/-- Remove duplicate broad theorem-family targets while preserving the first occurrence. -/
def deduplicateHostStereoClaimTargets (targets : List HostStereoClaimTarget) :
    List HostStereoClaimTarget :=
  deduplicateByEquality targets

/-- One official-stereo branch analysis requested for a shared host molecule packet. -/
structure HostOfficialStereoAnalysisTarget where
  keySuffix : String
  description : String
  definitionPrefix : String
  moduleNamespaceSuffix : List String := [definitionPrefix]
  centerAtom : ℕ
  left : ℕ
  right : ℕ
  profile : DescriptorSourcePolicyProfile := DescriptorSourcePolicyProfile.exactDistance
  graphFuel : ℕ := 0
  scheduleFuel : ℕ := 0
  branchFuel : ℕ := 0
  target : HostOfficialStereoCertificateTarget :=
    HostOfficialStereoCertificateTarget.refusal RefusalReason.unresolvedOfficialPriorities
  moduleFileName : String := definitionPrefix ++ "Host.lean"
  certificateFileName : String := definitionPrefix ++ "OfficialStereoCertificate.lean"
  certificateTheoremName : String := definitionPrefix ++ "_official_stereo_query_checked"
  deriving Repr

namespace HostOfficialStereoAnalysisTarget

/-- Validate generated names and file metadata for one molecule-analysis target. -/
def validateGeneratedShape (target : HostOfficialStereoAnalysisTarget) : Except String Unit := do
  validateNamespacePath "moduleNamespaceSuffix" target.moduleNamespaceSuffix
  validateGeneratedFileName "moduleFileName" target.moduleFileName
  validateImportableLeanFileName "certificateFileName" target.certificateFileName
  validateLeanNames "generated analysis target names"
    [ target.definitionPrefix
    , target.certificateTheoremName ]
  requireHostRequestShape (target.keySuffix ≠ "")
    "official-stereo analysis target keySuffix must not be empty"
  requireHostRequestShape (hostPackageKeySegment? target.keySuffix)
    "official-stereo analysis target keySuffix must be one package-key segment"
  requireHostRequestShape (target.description ≠ "")
    "official-stereo analysis target description must not be empty"

end HostOfficialStereoAnalysisTarget

/-- Executable coverage summary for host-facing stereochemical analysis targets.

This deliberately stays at the raw/indexed host boundary so the CLI can validate target coverage
without depending on noncomputable proof-facing detector records. -/
structure HostDetectorCoverage where
  rawDoubleBonds : ℕ := 0
  assignedDoubleBonds : ℕ := 0
  cumulenes : ℕ := 0
  axes : ℕ := 0
  planes : ℕ := 0
  helices : ℕ := 0
  conformations : ℕ := 0
  ensembles : ℕ := 0
  auxiliaryRule5Nodes : ℕ := 0
  phantomNodes : ℕ := 0
  lonePairNodes : ℕ := 0
  total : ℕ := 0
  deriving DecidableEq, Repr

namespace HostDetectorCoverage

/-- Count values satisfying an executable predicate. -/
def countWhere {α : Type*} (predicate : α → Bool) (values : List α) : ℕ :=
  (values.filter predicate).length

/-- Count unique values satisfying an executable predicate. -/
def countUniqueWhere {α : Type*} [DecidableEq α] (predicate : α → Bool)
    (values : List α) : ℕ :=
  (deduplicateByEquality (values.filter predicate)).length

/-- Count unique keys for values satisfying an executable predicate. -/
def countUniqueKeysWhere {α β : Type*} [DecidableEq β] (predicate : α → Bool)
    (key : α → β) (values : List α) : ℕ :=
  (deduplicateByEquality ((values.filter predicate).map key)).length

/-- Count unique keys whose valid records carry exactly one descriptor/result value.

This refuses contradictory duplicated source annotations: if the same geometry/state key carries
both `Rₐ` and `Sₐ`, neither exact result is counted. -/
def countUniqueKeysWithExactValue {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (predicate : α → Bool) (key : α → β) (value : α → γ) (target : γ)
    (values : List α) : ℕ :=
  let validValues := values.filter predicate
  let keys := deduplicateByEquality (validValues.map key)
  (keys.filter fun targetKey =>
    let keyValues :=
      deduplicateByEquality
        ((validValues.filter fun record => decide (key record = targetKey)).map value)
    decide (keyValues = [target])).length

/-- Count unique state identities whose valid records have one stable support and one exact kind. -/
def countUniqueStateKeysWithExactKind {α β : Type*} [DecidableEq β]
    (predicate : α → Bool) (key : α → β) (support : α → Finset ℕ)
    (kind? : α → Option OfficialStereogenicUnitKind) (target : OfficialStereogenicUnitKind)
    (values : List α) : ℕ :=
  let validValues := values.filter predicate
  let keys := deduplicateByEquality (validValues.map key)
  (keys.filter fun targetKey =>
    let keyRecords := validValues.filter fun record => decide (key record = targetKey)
    let supportValues := deduplicateByEquality (keyRecords.map support)
    let kindValues :=
      deduplicateByEquality
        (keyRecords.filterMap kind?)
    decide (supportValues.length = 1 ∧ kindValues = [target])).length

/-- Whether an indexed atom reference is valid for a raw molecule. -/
def atomIndexOK (raw : RawMolecule) (idx : ℕ) : Bool :=
  decide (idx < raw.atomCount)

/-- Whether all indexed atom references are valid for a raw molecule. -/
def atomIndicesOK (raw : RawMolecule) (indices : List ℕ) : Bool :=
  indices.all (atomIndexOK raw)

/-- Whether indexed atom references are pairwise distinct. -/
def atomIndicesDistinct (indices : List ℕ) : Bool :=
  !hasDuplicateByEquality indices

/-- Canonical set key for support lists that proof-facing detectors convert to finsets. -/
def atomSupportKey (indices : List ℕ) : Finset ℕ :=
  indices.toFinset

/-- Identity key for state annotations: explicit IDs identify states; otherwise support does. -/
inductive HostStateIdentityKey where
  | explicit (stateId : String)
  | support (support : Finset ℕ)
  deriving DecidableEq

/-- Canonical identity for a conformer/ensemble state annotation. -/
def stateIdentityKey (stateId : String) (support : List ℕ) : HostStateIdentityKey :=
  if stateId = "" then
    HostStateIdentityKey.support (atomSupportKey support)
  else
    HostStateIdentityKey.explicit stateId

/-- Canonical key for an undirected atom pair. -/
def unorderedPairKey (left right : ℕ) : ℕ × ℕ :=
  if left ≤ right then (left, right) else (right, left)

/-- Whether an indexed axial annotation only references valid atoms. -/
def axialOK (raw : RawMolecule) (record : IndexedDetectedAxialUnit) : Bool :=
  let indices :=
    [ record.axisStart, record.axisEnd, record.startHigh, record.startLow
    , record.endHigh, record.endLow ]
  atomIndicesOK raw indices &&
    record.axisStart != record.axisEnd &&
      record.startHigh != record.startLow &&
        record.endHigh != record.endLow

/-- Geometry key for an indexed axial annotation, ignoring descriptor label. -/
def axialKey (record : IndexedDetectedAxialUnit) : List ℕ :=
  [ record.axisStart, record.axisEnd, record.startHigh, record.startLow
  , record.endHigh, record.endLow ]

/-- Whether an indexed planar annotation only references valid atoms. -/
def planarOK (raw : RawMolecule) (record : IndexedDetectedPlanarUnit) : Bool :=
  atomIndicesOK raw
      (record.planeAtoms ++ [record.pilotAtom, record.highReference, record.lowReference]) &&
    decide (record.planeAtoms.length ≥ 3) &&
      atomIndicesDistinct record.planeAtoms &&
        record.highReference != record.lowReference

/-- Geometry key for an indexed planar annotation, ignoring descriptor label. -/
def planarKey (record : IndexedDetectedPlanarUnit) : List ℕ :=
  record.planeAtoms ++ [record.pilotAtom, record.highReference, record.lowReference]

/-- Whether an indexed helical annotation only references valid atoms. -/
def helicalOK (raw : RawMolecule) (record : IndexedDetectedHelicalUnit) : Bool :=
  atomIndicesOK raw (record.helixPath ++ [record.frontReference, record.backReference]) &&
    decide (record.helixPath.length ≥ 2) &&
      atomIndicesDistinct record.helixPath &&
        record.frontReference != record.backReference

/-- Geometry key for an indexed helical annotation, ignoring descriptor label. -/
def helicalKey (record : IndexedDetectedHelicalUnit) : List ℕ :=
  record.helixPath ++ [record.frontReference, record.backReference]

/-- Whether an indexed conformational-state annotation only references valid atoms. -/
def conformationOK (raw : RawMolecule)
    (record : IndexedDetectedConformationalState) : Bool :=
  atomIndicesOK raw record.support &&
    decide (record.support.length > 0) &&
      atomIndicesDistinct record.support

/-- Identity key for an indexed conformational-state annotation, ignoring optional kind label. -/
def conformationKey (record : IndexedDetectedConformationalState) : HostStateIdentityKey :=
  stateIdentityKey record.stateId record.support

/-- Whether an indexed ensemble annotation only references valid atoms. -/
def ensembleOK (raw : RawMolecule) (record : IndexedDetectedEnsembleState) : Bool :=
  atomIndicesOK raw record.support &&
    decide (record.support.length > 0) &&
      atomIndicesDistinct record.support

/-- Identity key for an indexed ensemble annotation, ignoring optional kind label. -/
def ensembleKey (record : IndexedDetectedEnsembleState) : HostStateIdentityKey :=
  stateIdentityKey record.stateId record.support

/-- Canonical support key for virtual proof-facing nodes, including the anchor insertion. -/
def canonicalVirtualNodeSupport (anchor : ℕ) (support : List ℕ) : Finset ℕ :=
  insert anchor (atomSupportKey support)

/-- Canonical identity for virtual hierarchical-digraph nodes. -/
def virtualNodeKey (anchor : ℕ) (support : List ℕ) (rootDistance? : Option ℕ) :
    ℕ × Finset ℕ × Option ℕ :=
  (anchor, canonicalVirtualNodeSupport anchor support, rootDistance?)

/-- Whether an indexed auxiliary Rule-5 node annotation only references valid atoms. -/
def auxiliaryRule5NodeOK (raw : RawMolecule)
    (record : IndexedDetectedAuxiliaryRule5Node) : Bool :=
  atomIndicesOK raw (record.anchor :: record.support) &&
    decide (record.support.length > 0) &&
      atomIndicesDistinct record.support

/-- Geometry key for an indexed auxiliary Rule-5 node annotation, ignoring descriptor label. -/
def auxiliaryRule5NodeKey (record : IndexedDetectedAuxiliaryRule5Node) :
    ℕ × Finset ℕ × Option ℕ :=
  virtualNodeKey record.anchor record.support record.rootDistance?

/-- Whether an indexed phantom-node annotation only references valid atoms. -/
def phantomNodeOK (raw : RawMolecule) (record : IndexedDetectedPhantomNode) : Bool :=
  atomIndicesOK raw (record.anchor :: record.support) &&
    decide (record.support.length > 0) &&
      atomIndicesDistinct record.support

/-- Geometry key for an indexed phantom-node annotation. -/
def phantomNodeKey (record : IndexedDetectedPhantomNode) : ℕ × Finset ℕ × Option ℕ :=
  virtualNodeKey record.anchor record.support record.rootDistance?

/-- Whether an indexed lone-pair node annotation only references valid atoms. -/
def lonePairNodeOK (raw : RawMolecule) (record : IndexedDetectedLonePairNode) : Bool :=
  atomIndicesOK raw (record.anchor :: record.support) &&
    decide (record.support.length > 0) &&
      atomIndicesDistinct record.support

/-- Geometry key for an indexed lone-pair-node annotation. -/
def lonePairNodeKey (record : IndexedDetectedLonePairNode) : ℕ × Finset ℕ × Option ℕ :=
  virtualNodeKey record.anchor record.support record.rootDistance?

/-- Unique parser-visible double-bond endpoint pairs in a raw molecule. -/
def rawDoubleBondPairs (raw : RawMolecule) : List (ℕ × ℕ) :=
  deduplicateByEquality <|
    raw.bonds.filterMap fun bond =>
      if bond.kind == ParsedBondKind.double then
        some (unorderedPairKey bond.source bond.target)
      else
        none

/-- Count unique parser-visible double bonds in a raw molecule. -/
def rawDoubleBondCount (raw : RawMolecule) : ℕ :=
  (rawDoubleBondPairs raw).length

/-- Whether a perceived double-bond stereo value is an assigned `E/Z` descriptor. -/
def doubleBondStereoAssigned : Option DoubleBondStereo → Bool
  | some DoubleBondStereo.E => true
  | some DoubleBondStereo.Z => true
  | _ => false

/-- Unique double-bond endpoint pairs whose stereochemistry is perceived as assigned `E/Z`. -/
def assignedDoubleBondPairs (packet : ExternalRawMoleculePacket) : List (ℕ × ℕ) :=
  let result := (importExternalRawMoleculePacket packet).normalized.normalized
  deduplicateByEquality <|
    result.stereobonds.doubleBondAssignments.filterMap fun assignment =>
      match assignment with
      | (left, right, _) =>
          if doubleBondStereoAssigned (result.perceivedDoubleBondStereo? left right) then
            some (unorderedPairKey left right)
          else
            none

/-- Count unique double bonds whose stereochemistry is perceived as assigned `E/Z`. -/
def assignedDoubleBondCount (packet : ExternalRawMoleculePacket) : ℕ :=
  (assignedDoubleBondPairs packet).length

/-- All oriented parsed double-bond endpoints. -/
def doubleBondOrientations (raw : RawMolecule) : List (ℕ × ℕ) :=
  (rawDoubleBondPairs raw).flatMap fun pair =>
    [(pair.1, pair.2), (pair.2, pair.1)]

/-- Parser-visible length-three cumulene path candidates. -/
def cumulenePathCandidates (raw : RawMolecule) : List (ℕ × ℕ × ℕ) :=
  deduplicateByEquality <|
    (doubleBondOrientations raw).flatMap fun first =>
      (doubleBondOrientations raw).filterMap fun second =>
        if first.2 == second.1 && decide (first.1 ≠ second.2) &&
            decide (first.1 < second.2) then
          some (first.1, first.2, second.2)
        else
          none

/-- Coverage summary computed from raw parser-visible units and valid indexed annotations. -/
def ofPacketAndAnnotations (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : HostDetectorCoverage :=
  let raw := packet.raw
  let rawDoubleBonds := rawDoubleBondCount raw
  let assignedDoubleBonds := assignedDoubleBondCount packet
  let cumulenes := (cumulenePathCandidates raw).length
  let axes := countUniqueKeysWhere (axialOK raw) axialKey annotations.axes
  let planes := countUniqueKeysWhere (planarOK raw) planarKey annotations.planes
  let helices := countUniqueKeysWhere (helicalOK raw) helicalKey annotations.helices
  let conformations := countUniqueKeysWhere (conformationOK raw) conformationKey annotations.conformations
  let ensembles := countUniqueKeysWhere (ensembleOK raw) ensembleKey annotations.ensembles
  let auxiliaryRule5Nodes :=
    countUniqueKeysWhere
      (auxiliaryRule5NodeOK raw) auxiliaryRule5NodeKey annotations.auxiliaryRule5Nodes
  let phantomNodes :=
    countUniqueKeysWhere (phantomNodeOK raw) phantomNodeKey annotations.phantomNodes
  let lonePairNodes :=
    countUniqueKeysWhere (lonePairNodeOK raw) lonePairNodeKey annotations.lonePairNodes
  { rawDoubleBonds := rawDoubleBonds
    assignedDoubleBonds := assignedDoubleBonds
    cumulenes := cumulenes
    axes := axes
    planes := planes
    helices := helices
    conformations := conformations
    ensembles := ensembles
    auxiliaryRule5Nodes := auxiliaryRule5Nodes
    phantomNodes := phantomNodes
    lonePairNodes := lonePairNodes
    total :=
      rawDoubleBonds + assignedDoubleBonds + cumulenes + axes + planes + helices +
        conformations + ensembles + auxiliaryRule5Nodes + phantomNodes + lonePairNodes }

end HostDetectorCoverage

namespace HostMoleculeDescriptorResult

/-- Count one exact source key when matching records carry exactly one descriptor/result value. -/
def countExactSourceKeyWithValue {α γ : Type*} [DecidableEq γ]
    (predicate : α → Bool) (matchesSource : α → Bool) (value : α → γ) (target : γ)
    (values : List α) : ℕ :=
  let matchingValues := values.filter fun record => predicate record && matchesSource record
  let descriptorValues := deduplicateByEquality (matchingValues.map value)
  if descriptorValues = [target] then 1 else 0

/-- Count one exact state source key when all records for its identity share one support and kind. -/
def countExactStateSourceKeyWithKind {α β : Type*} [DecidableEq β]
    (predicate : α → Bool) (identity : α → β) (support : α → Finset ℕ)
    (kind? : α → Option OfficialStereogenicUnitKind) (sourceIdentity : β)
    (sourceSupport : Finset ℕ) (target : OfficialStereogenicUnitKind)
    (values : List α) : ℕ :=
  let matchingValues :=
    values.filter fun record =>
      predicate record && decide (identity record = sourceIdentity)
  let supportValues := deduplicateByEquality (matchingValues.map support)
  let kindValues :=
    deduplicateByEquality (matchingValues.filterMap kind?)
  if supportValues = [sourceSupport] && kindValues = [target] then 1 else 0

/-- Exact source key for an indexed axial annotation. -/
def axialSourceKey (record : IndexedDetectedAxialUnit) : HostMoleculeDescriptorSourceKey :=
  HostMoleculeDescriptorSourceKey.axial record.axisStart record.axisEnd record.startHigh
    record.startLow record.endHigh record.endLow

/-- Exact source key for an indexed planar annotation. -/
def planarSourceKey (record : IndexedDetectedPlanarUnit) : HostMoleculeDescriptorSourceKey :=
  HostMoleculeDescriptorSourceKey.planar record.planeAtoms record.pilotAtom
    record.highReference record.lowReference

/-- Exact source key for an indexed helical annotation. -/
def helicalSourceKey (record : IndexedDetectedHelicalUnit) : HostMoleculeDescriptorSourceKey :=
  HostMoleculeDescriptorSourceKey.helical record.helixPath record.frontReference
    record.backReference

/-- Canonical exact source key for a parser-visible double-bond pair. -/
def alkeneSourceKey (left right : ℕ) : HostMoleculeDescriptorSourceKey :=
  let pair := HostDetectorCoverage.unorderedPairKey left right
  HostMoleculeDescriptorSourceKey.alkene pair.1 pair.2

/-- Whether an auxiliary Rule-5 annotation matches a canonical virtual-node source key. -/
def auxiliaryRule5SourceKeyMatches (record : IndexedDetectedAuxiliaryRule5Node)
    (sourceKey : HostMoleculeDescriptorSourceKey) : Bool :=
  match sourceKey with
  | HostMoleculeDescriptorSourceKey.auxiliaryRule5 anchor support rootDistance? =>
      decide (record.anchor = anchor) &&
        decide
          (HostDetectorCoverage.canonicalVirtualNodeSupport record.anchor record.support =
            HostDetectorCoverage.canonicalVirtualNodeSupport anchor support) &&
          decide (record.rootDistance? = rootDistance?)
  | _ => false

/-- Count valid axial annotations carrying an exact `Rₐ/Sₐ` descriptor. -/
def axialDescriptorCount (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (descriptor : AxialDescriptor) : ℕ :=
  let raw := packet.raw
  HostDetectorCoverage.countUniqueKeysWithExactValue
    (HostDetectorCoverage.axialOK raw) HostDetectorCoverage.axialKey
    (fun record => record.descriptor) descriptor annotations.axes

/-- Count valid planar annotations carrying an exact `Rₚ/Sₚ` descriptor. -/
def planarDescriptorCount (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (descriptor : PlanarDescriptor) : ℕ :=
  let raw := packet.raw
  HostDetectorCoverage.countUniqueKeysWithExactValue
    (HostDetectorCoverage.planarOK raw) HostDetectorCoverage.planarKey
    (fun record => record.descriptor) descriptor annotations.planes

/-- Count valid helical annotations carrying an exact `P/M` descriptor. -/
def helicalDescriptorCount (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (descriptor : HelicalDescriptor) : ℕ :=
  let raw := packet.raw
  HostDetectorCoverage.countUniqueKeysWithExactValue
    (HostDetectorCoverage.helicalOK raw) HostDetectorCoverage.helicalKey
    (fun record => record.descriptor) descriptor annotations.helices

/-- Count a valid axial annotation carrying an exact descriptor at one exact source key. -/
def axialDescriptorCountForKey (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (sourceKey : HostMoleculeDescriptorSourceKey)
    (descriptor : AxialDescriptor) : ℕ :=
  let raw := packet.raw
  countExactSourceKeyWithValue
    (HostDetectorCoverage.axialOK raw)
    (fun record => decide (axialSourceKey record = sourceKey))
    (fun record => record.descriptor) descriptor annotations.axes

/-- Count a valid planar annotation carrying an exact descriptor at one exact source key. -/
def planarDescriptorCountForKey (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (sourceKey : HostMoleculeDescriptorSourceKey)
    (descriptor : PlanarDescriptor) : ℕ :=
  let raw := packet.raw
  countExactSourceKeyWithValue
    (HostDetectorCoverage.planarOK raw)
    (fun record => decide (planarSourceKey record = sourceKey))
    (fun record => record.descriptor) descriptor annotations.planes

/-- Count a valid helical annotation carrying an exact descriptor at one exact source key. -/
def helicalDescriptorCountForKey (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (sourceKey : HostMoleculeDescriptorSourceKey)
    (descriptor : HelicalDescriptor) : ℕ :=
  let raw := packet.raw
  countExactSourceKeyWithValue
    (HostDetectorCoverage.helicalOK raw)
    (fun record => decide (helicalSourceKey record = sourceKey))
    (fun record => record.descriptor) descriptor annotations.helices

/-- Unique non-`unspecified` stored stereo values for an undirected double-bond pair. -/
def storedDoubleBondStereoValues (packet : ExternalRawMoleculePacket)
    (left right : ℕ) : List DoubleBondStereo :=
  let result := (importExternalRawMoleculePacket packet).normalized.normalized
  deduplicateByEquality <|
    result.stereobonds.doubleBondAssignments.filterMap fun assignment =>
      if StereobondSemantics.doubleBondAssignmentConnects assignment left right then
        match StereobondSemantics.doubleBondAssignmentStereo assignment with
        | DoubleBondStereo.unspecified => none
        | stereo => some stereo
      else
        none

/-- Exact double-bond stereo when a stored value is unambiguous, otherwise the senior-substituent
CIP reading of the directional markers.

This defers to `ChemistryNormalizationResult.cipDoubleBondStereo?` rather than comparing whole-side
marker lists, so a host certificate reports the relationship of the CIP-senior groups instead of
whichever atoms happened to carry slashes. -/
def exactDoubleBondStereo? (packet : ExternalRawMoleculePacket)
    (left right : ℕ) : Option DoubleBondStereo :=
  match storedDoubleBondStereoValues packet left right with
  | [stereo] => some stereo
  | [] =>
      ((importExternalRawMoleculePacket packet).normalized.normalized).cipDoubleBondStereo?
        left right
  | _ => none

/-- Unique double-bond endpoint pairs whose perceived stereochemistry is an exact `E/Z` value. -/
def doubleBondStereoPairs (packet : ExternalRawMoleculePacket)
    (descriptor : DoubleBondStereo) : List (ℕ × ℕ) :=
  let result := (importExternalRawMoleculePacket packet).normalized.normalized
  deduplicateByEquality <|
    result.stereobonds.doubleBondAssignments.filterMap fun assignment =>
      match assignment with
      | (left, right, _) =>
          if exactDoubleBondStereo? packet left right = some descriptor then
            some (HostDetectorCoverage.unorderedPairKey left right)
          else
            none

/-- Count unique double bonds whose perceived stereochemistry is an exact `E/Z` value. -/
def doubleBondStereoCount (packet : ExternalRawMoleculePacket)
    (descriptor : DoubleBondStereo) : ℕ :=
  (doubleBondStereoPairs packet descriptor).length

/-- Count one double bond whose perceived stereochemistry is an exact `E/Z` value. -/
def doubleBondStereoCountForKey (packet : ExternalRawMoleculePacket)
    (sourceKey : HostMoleculeDescriptorSourceKey) (descriptor : DoubleBondStereo) : ℕ :=
  let result := (importExternalRawMoleculePacket packet).normalized.normalized
  match sourceKey with
  | HostMoleculeDescriptorSourceKey.alkene sourceLeft sourceRight =>
      countExactSourceKeyWithValue
        (fun _ => true)
        (fun assignment =>
          match assignment with
          | (left, right, _) => decide (alkeneSourceKey left right =
              HostMoleculeDescriptorSourceKey.alkene sourceLeft sourceRight))
        (fun assignment =>
          match assignment with
          | (left, right, _) =>
              (exactDoubleBondStereo? packet left right).getD DoubleBondStereo.unspecified)
        descriptor result.stereobonds.doubleBondAssignments
  | _ => 0

/-- Count valid auxiliary Rule-5 annotations carrying an exact descriptor. -/
def auxiliaryRule5DescriptorCount (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations)
    (descriptor : OfficialRule5Descriptor) : ℕ :=
  let raw := packet.raw
  HostDetectorCoverage.countUniqueKeysWithExactValue
    (HostDetectorCoverage.auxiliaryRule5NodeOK raw)
    HostDetectorCoverage.auxiliaryRule5NodeKey
    (fun record => record.descriptor.asAuxiliary) descriptor annotations.auxiliaryRule5Nodes

/-- Count one valid auxiliary Rule-5 annotation carrying an exact descriptor at one source key. -/
def auxiliaryRule5DescriptorCountForKey (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (sourceKey : HostMoleculeDescriptorSourceKey)
    (descriptor : OfficialRule5Descriptor) : ℕ :=
  let raw := packet.raw
  countExactSourceKeyWithValue
    (HostDetectorCoverage.auxiliaryRule5NodeOK raw)
    (fun record => auxiliaryRule5SourceKeyMatches record sourceKey)
    (fun record => record.descriptor.asAuxiliary) descriptor annotations.auxiliaryRule5Nodes

/-- Count valid conformational-state annotations carrying an exact Rule-4a unit kind. -/
def conformerKindCount (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations)
    (kind : OfficialStereogenicUnitKind) : ℕ :=
  let raw := packet.raw
  HostDetectorCoverage.countUniqueStateKeysWithExactKind
    (HostDetectorCoverage.conformationOK raw)
    HostDetectorCoverage.conformationKey
    (fun record => HostDetectorCoverage.atomSupportKey record.support)
    (fun record => record.kind?)
    kind annotations.conformations

/-- Count one conformational-state source key carrying an exact Rule-4a kind. -/
def conformerKindCountForKey (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (sourceKey : HostMoleculeDescriptorSourceKey)
    (kind : OfficialStereogenicUnitKind) : ℕ :=
  let raw := packet.raw
  match sourceKey with
  | HostMoleculeDescriptorSourceKey.conformer stateId support =>
      countExactStateSourceKeyWithKind
        (HostDetectorCoverage.conformationOK raw)
        HostDetectorCoverage.conformationKey
        (fun record => HostDetectorCoverage.atomSupportKey record.support)
        (fun record => record.kind?)
        (HostDetectorCoverage.stateIdentityKey stateId support)
        (HostDetectorCoverage.atomSupportKey support)
        kind annotations.conformations
  | _ => 0

/-- Count valid ensemble-state annotations carrying an exact Rule-4a unit kind. -/
def ensembleKindCount (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations)
    (kind : OfficialStereogenicUnitKind) : ℕ :=
  let raw := packet.raw
  HostDetectorCoverage.countUniqueStateKeysWithExactKind
    (HostDetectorCoverage.ensembleOK raw)
    HostDetectorCoverage.ensembleKey
    (fun record => HostDetectorCoverage.atomSupportKey record.support)
    (fun record => record.kind?)
    kind annotations.ensembles

/-- Count one ensemble-state source key carrying an exact Rule-4a kind. -/
def ensembleKindCountForKey (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) (sourceKey : HostMoleculeDescriptorSourceKey)
    (kind : OfficialStereogenicUnitKind) : ℕ :=
  let raw := packet.raw
  match sourceKey with
  | HostMoleculeDescriptorSourceKey.ensemble stateId support =>
      countExactStateSourceKeyWithKind
        (HostDetectorCoverage.ensembleOK raw)
        HostDetectorCoverage.ensembleKey
        (fun record => HostDetectorCoverage.atomSupportKey record.support)
        (fun record => record.kind?)
        (HostDetectorCoverage.stateIdentityKey stateId support)
        (HostDetectorCoverage.atomSupportKey support)
        kind annotations.ensembles
  | _ => 0

/-- Source-count semantics for exact descriptor-result certificate evidence. -/
def sourceCount (result : HostMoleculeDescriptorResult)
    (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : ℕ :=
  match result with
  | axial descriptor => axialDescriptorCount packet annotations descriptor
  | planar descriptor => planarDescriptorCount packet annotations descriptor
  | helical descriptor => helicalDescriptorCount packet annotations descriptor
  | alkene descriptor => doubleBondStereoCount packet descriptor
  | auxiliaryRule5 descriptor => auxiliaryRule5DescriptorCount packet annotations descriptor
  | conformerKind kind => conformerKindCount packet annotations kind
  | ensembleKind kind => ensembleKindCount packet annotations kind

/-- Source-count semantics for exact descriptor-result certificate evidence at one source key. -/
def sourceCountForKey (result : HostMoleculeDescriptorResult)
    (sourceKey : HostMoleculeDescriptorSourceKey)
    (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : ℕ :=
  if result.compatibleSourceKey sourceKey then
    match result with
    | axial descriptor => axialDescriptorCountForKey packet annotations sourceKey descriptor
    | planar descriptor => planarDescriptorCountForKey packet annotations sourceKey descriptor
    | helical descriptor => helicalDescriptorCountForKey packet annotations sourceKey descriptor
    | alkene descriptor => doubleBondStereoCountForKey packet sourceKey descriptor
    | auxiliaryRule5 descriptor => auxiliaryRule5DescriptorCountForKey packet annotations sourceKey descriptor
    | conformerKind kind => conformerKindCountForKey packet annotations sourceKey kind
    | ensembleKind kind => ensembleKindCountForKey packet annotations sourceKey kind
  else
    0

end HostMoleculeDescriptorResult


inductive HostNoncenterDescriptorFamily where
  | axial
  | planar
  | helical
  | alkene
  | cumulene
  | auxiliaryRule5
  | phantom
  | lonePair
  deriving DecidableEq, Repr

namespace HostNoncenterDescriptorFamily

/-- Host-facing label for a non-center stereochemical unit family. -/
def label : HostNoncenterDescriptorFamily → String
  | axial => "axial descriptor"
  | planar => "planar descriptor"
  | helical => "helical descriptor"
  | alkene => "assigned alkene E/Z descriptor"
  | cumulene => "cumulene path candidate"
  | auxiliaryRule5 => "auxiliary Rule-5 node"
  | phantom => "phantom node"
  | lonePair => "lone-pair node"

/-- Coverage count for this unit family in a normalized detector bundle. -/
def coverageCount (family : HostNoncenterDescriptorFamily)
    (coverage : HostDetectorCoverage) : ℕ :=
  match family with
  | axial => coverage.axes
  | planar => coverage.planes
  | helical => coverage.helices
  | alkene => coverage.assignedDoubleBonds
  | cumulene => coverage.cumulenes
  | auxiliaryRule5 => coverage.auxiliaryRule5Nodes
  | phantom => coverage.phantomNodes
  | lonePair => coverage.lonePairNodes

/-- Target-witness coverage field corresponding to this non-center family. -/
def coverageField : HostNoncenterDescriptorFamily → HostMoleculeTargetCoverageField
  | axial => HostMoleculeTargetCoverageField.axial
  | planar => HostMoleculeTargetCoverageField.planar
  | helical => HostMoleculeTargetCoverageField.helical
  | alkene => HostMoleculeTargetCoverageField.alkene
  | cumulene => HostMoleculeTargetCoverageField.cumulene
  | auxiliaryRule5 => HostMoleculeTargetCoverageField.auxiliaryRule5
  | phantom => HostMoleculeTargetCoverageField.phantom
  | lonePair => HostMoleculeTargetCoverageField.lonePair

/-- Broad theorem-family dependencies required by this unit-family target. -/
def requiredClaimTargets : HostNoncenterDescriptorFamily → List HostStereoClaimTarget
  | axial => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | planar => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | helical => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | alkene => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | cumulene => [HostStereoClaimTarget.stereoElementProfileMirrorInvolutive]
  | auxiliaryRule5 => [HostStereoClaimTarget.officialCIPAssignmentSuccessResolved]
  | phantom => [HostStereoClaimTarget.officialCIPAssignmentSuccessResolved]
  | lonePair => [HostStereoClaimTarget.officialCIPAssignmentSuccessResolved]

end HostNoncenterDescriptorFamily


inductive HostGraphRelationTargetKind where
  | multiCenterCipRSExactlyOne
  | descriptorClassifierSound
  | descriptorClassifierRefusal
  deriving DecidableEq, Repr

namespace HostGraphRelationTargetKind

/-- Host-facing label for a graph-level relation target. -/
def label : HostGraphRelationTargetKind → String
  | multiCenterCipRSExactlyOne => "multi-center CIP R/S exactly-one classification"
  | descriptorClassifierSound => "graph descriptor classifier soundness"
  | descriptorClassifierRefusal => "graph descriptor classifier unresolved-priority refusal"

/-- Broad theorem-family dependency for this graph-level relation target. -/
def requiredClaimTargets : HostGraphRelationTargetKind → List HostStereoClaimTarget
  | multiCenterCipRSExactlyOne =>
      [HostStereoClaimTarget.multiCenterCipRSClassificationExactlyOne]
  | descriptorClassifierSound =>
      [HostStereoClaimTarget.graphDescriptorClassifierSound]
  | descriptorClassifierRefusal =>
      [HostStereoClaimTarget.graphDescriptorClassifierRefusesUnresolved]

/-- Target-witness coverage field corresponding to this graph-level relation family. -/
def coverageField : HostGraphRelationTargetKind → HostMoleculeTargetCoverageField
  | multiCenterCipRSExactlyOne => HostMoleculeTargetCoverageField.multiCenterGraphRelation
  | descriptorClassifierSound => HostMoleculeTargetCoverageField.graphClassifierSound
  | descriptorClassifierRefusal => HostMoleculeTargetCoverageField.graphClassifierRefusal

end HostGraphRelationTargetKind


inductive HostConformerClaimTargetKind where
  | profileChiralRefutesAchiral
  deriving DecidableEq, Repr

namespace HostConformerClaimTargetKind

/-- Host-facing label for a conformer-level claim target. -/
def label : HostConformerClaimTargetKind → String
  | profileChiralRefutesAchiral => "profile chirality refutes conformer achirality"

/-- Broad theorem-family dependency for this conformer-level target. -/
def requiredClaimTargets : HostConformerClaimTargetKind → List HostStereoClaimTarget
  | profileChiralRefutesAchiral =>
      [HostStereoClaimTarget.conformationalProfileChiralRefutesAchiral]

end HostConformerClaimTargetKind


inductive HostEnsembleClaimTargetKind where
  | descriptorChiralRefutesAchiral
  deriving DecidableEq, Repr

namespace HostEnsembleClaimTargetKind

/-- Host-facing label for an ensemble-level claim target. -/
def label : HostEnsembleClaimTargetKind → String
  | descriptorChiralRefutesAchiral => "descriptor-chiral ensemble refutes descriptor achirality"

/-- Broad theorem-family dependency for this ensemble-level target. -/
def requiredClaimTargets : HostEnsembleClaimTargetKind → List HostStereoClaimTarget
  | descriptorChiralRefutesAchiral =>
      [HostStereoClaimTarget.descriptorChiralEnsembleRefutesAchiral]

end HostEnsembleClaimTargetKind

/-- Target requesting a non-center stereochemical unit family from a molecule analysis. -/
structure HostNoncenterDescriptorTarget where
  keySuffix : String
  description : String
  family : HostNoncenterDescriptorFamily
  minimumCount : ℕ := 1
  expectedResult? : Option HostMoleculeDescriptorResult := none
  expectedSourceKey? : Option HostMoleculeDescriptorSourceKey := none
  minimumResultCount : ℕ := 1
  deriving Repr

namespace HostNoncenterDescriptorTarget

/-- Validate host-facing names and non-empty coverage demand for a non-center target. -/
def validateGeneratedShape (target : HostNoncenterDescriptorTarget) : Except String Unit := do
  requireHostRequestShape (target.keySuffix ≠ "")
    "non-center target keySuffix must not be empty"
  requireHostRequestShape (hostPackageKeySegment? target.keySuffix)
    "non-center target keySuffix must be one package-key segment"
  requireHostRequestShape (target.description ≠ "")
    "non-center target description must not be empty"
  requireHostRequestShape (target.minimumCount > 0)
    "non-center target minimumCount must be positive"
  match target.expectedResult? with
  | none =>
      requireHostRequestShape target.expectedSourceKey?.isNone
        "non-center target expectedSourceKey requires expectedResult"
  | some result => do
      requireHostRequestShape (result.coverageField = target.family.coverageField)
        "non-center target expectedResult does not match its requested family"
      requireHostRequestShape result.assigned
        "non-center target expectedResult is not an assigned descriptor"
      let sourceKey ←
        match target.expectedSourceKey? with
        | some sourceKey => pure sourceKey
        | none => throw "non-center target expectedSourceKey must be present when expectedResult is present"
      requireHostRequestShape sourceKey.isCanonical
        "non-center target expectedSourceKey must be canonical"
      requireHostRequestShape (result.compatibleSourceKey sourceKey)
        "non-center target expectedSourceKey does not match its expectedResult family"
      requireHostRequestShape (target.minimumResultCount > 0)
        "non-center target minimumResultCount must be positive when expectedResult is present"

/-- Whether the detector coverage satisfies this target's required family count. -/
def coverageReady (target : HostNoncenterDescriptorTarget)
    (coverage : HostDetectorCoverage) : Bool :=
  decide (target.family.coverageCount coverage ≥ target.minimumCount)

/-- Refuse this target if detector coverage does not expose enough matching units. -/
def validateCoverage (target : HostNoncenterDescriptorTarget)
    (coverage : HostDetectorCoverage) : Except String Unit := do
  requireHostRequestShape (target.coverageReady coverage)
    ("requested " ++ target.family.label ++ " target " ++ reprStr target.keySuffix ++
      " requires at least " ++ toString target.minimumCount ++
      " detected unit(s), but coverage has " ++
      toString (target.family.coverageCount coverage))

/-- Exact descriptor-result evidence for this non-center target, if requested. -/
def descriptorResultEvidence? (target : HostNoncenterDescriptorTarget)
    (packet : ExternalRawMoleculePacket) (annotations : IndexedNoncenterStereoAnnotations) :
    Option HostMoleculeDescriptorResultEvidence :=
  match target.expectedResult?, target.expectedSourceKey? with
  | some result, some sourceKey =>
      some
        { result := result
          sourceKey := sourceKey
          matchedCount := result.sourceCountForKey sourceKey packet annotations
          requiredCount := target.minimumResultCount
          resultChecked := true }
  | _, _ => none

/-- Whether exact descriptor-result evidence satisfies this target's requested value. -/
def descriptorResultReady (target : HostNoncenterDescriptorTarget)
    (coverage : HostDetectorCoverage) (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : Bool :=
  match target.descriptorResultEvidence? packet annotations with
  | none => true
  | some evidence => evidence.readyFor target.family.coverageField (target.family.coverageCount coverage)

/-- Refuse this target if the requested exact descriptor value is absent from source evidence. -/
def validateDescriptorResult (target : HostNoncenterDescriptorTarget)
    (coverage : HostDetectorCoverage) (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : Except String Unit := do
  match target.expectedResult? with
  | none => pure ()
  | some result =>
      let sourceKey ←
        match target.expectedSourceKey? with
        | some sourceKey => pure sourceKey
        | none => throw "non-center exact descriptor target is missing an expected source key"
      requireHostRequestShape (target.descriptorResultReady coverage packet annotations)
        ("requested exact descriptor result " ++ result.label ++ " for target " ++
          reprStr target.keySuffix ++ " requires at least " ++
          toString target.minimumResultCount ++ " matching source unit(s), but source has " ++
          toString (result.sourceCountForKey sourceKey packet annotations))

/-- Broad theorem-family dependencies required by this target. -/
def requiredClaimTargets (target : HostNoncenterDescriptorTarget) :
    List HostStereoClaimTarget :=
  target.family.requiredClaimTargets

/-- Molecule-specific witness for this non-center target and normalized detector coverage. -/
def witness (requestKey : String) (coverage : HostDetectorCoverage)
    (packet : ExternalRawMoleculePacket) (annotations : IndexedNoncenterStereoAnnotations)
    (target : HostNoncenterDescriptorTarget) : HostMoleculeTargetWitness where
  requestKey := requestKey
  targetKeySuffix := target.keySuffix
  targetDescription := target.description
  targetLabel := target.family.label
  kind := HostMoleculeTargetWitnessKind.noncenterDescriptor
  coverageField := target.family.coverageField
  observedCount := target.family.coverageCount coverage
  requiredCount := target.minimumCount
  coverageChecked := true
  descriptorResult? := target.descriptorResultEvidence? packet annotations
  theoremFamilyKeys := target.requiredClaimTargets.map (hostAnalysisClaimPackageKey requestKey)

end HostNoncenterDescriptorTarget

/-- Target requesting a graph-level stereochemical relation family. -/
structure HostGraphRelationTarget where
  keySuffix : String
  description : String
  kind : HostGraphRelationTargetKind
  minimumDetectedCenters : ℕ := 1
  configurationPolicy : HostMoleculeGraphConfigurationPolicy :=
    HostMoleculeGraphConfigurationPolicy.identityMirror
  expectedOutcome? : Option CipRSClassRelation := none
  outcomePrecondition : HostMoleculeGraphOutcomePrecondition :=
    HostMoleculeGraphOutcomePrecondition.none
  deriving Repr

namespace HostGraphRelationTarget

/-- Validate host-facing metadata for a graph-level target. -/
def validateGeneratedShape (target : HostGraphRelationTarget) : Except String Unit := do
  requireHostRequestShape (target.keySuffix ≠ "")
    "graph-relation target keySuffix must not be empty"
  requireHostRequestShape (hostPackageKeySegment? target.keySuffix)
    "graph-relation target keySuffix must be one package-key segment"
  requireHostRequestShape (target.description ≠ "")
    "graph-relation target description must not be empty"
  requireHostRequestShape (target.minimumDetectedCenters > 0)
    "graph-relation target minimumDetectedCenters must be positive"
  match target.expectedOutcome? with
  | none =>
      requireHostRequestShape
        (target.outcomePrecondition = HostMoleculeGraphOutcomePrecondition.none)
        "graph-relation outcome precondition requires a concrete expected outcome"
  | some outcome =>
      requireHostRequestShape
        (HostMoleculeGraphResultEvidence.autoOutcomeSupported
          (match target.kind with
          | HostGraphRelationTargetKind.multiCenterCipRSExactlyOne =>
              HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne
          | HostGraphRelationTargetKind.descriptorClassifierSound =>
              HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound
          | HostGraphRelationTargetKind.descriptorClassifierRefusal =>
              HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal)
          target.configurationPolicy target.outcomePrecondition outcome)
        "graph-relation concrete outcome is not supported by the selected target kind and configuration policy"

/-- Broad theorem-family dependencies required by this target. -/
def requiredClaimTargets (target : HostGraphRelationTarget) :
    List HostStereoClaimTarget :=
  target.kind.requiredClaimTargets

/-- Whether graph source evidence exposes enough tetrahedral centers for this graph target. -/
def coverageReady (target : HostGraphRelationTarget) (packet : ExternalRawMoleculePacket) : Bool :=
  decide
    (HostMoleculeGraphResult.detectedTetrahedralCenterCount packet ≥
      target.minimumDetectedCenters)

/-- Refuse this graph target when the host molecule source lacks graph-center evidence. -/
def validateCoverage (target : HostGraphRelationTarget)
    (packet : ExternalRawMoleculePacket) : Except String Unit := do
  let observed := HostMoleculeGraphResult.detectedTetrahedralCenterCount packet
  requireHostRequestShape (target.coverageReady packet)
    ("requested graph-relation target " ++ reprStr target.keySuffix ++
      " requires at least " ++ toString target.minimumDetectedCenters ++
      " detected tetrahedral center(s), but source has " ++ toString observed)

/-- Typed graph-result evidence for this graph-level target. -/
def graphResultEvidence (target : HostGraphRelationTarget)
    (packet : ExternalRawMoleculePacket) : HostMoleculeGraphResultEvidence where
  kind :=
    match target.kind with
    | HostGraphRelationTargetKind.multiCenterCipRSExactlyOne =>
        HostMoleculeGraphResultEvidenceKind.multiCenterExactlyOne
    | HostGraphRelationTargetKind.descriptorClassifierSound =>
        HostMoleculeGraphResultEvidenceKind.descriptorClassifierSound
    | HostGraphRelationTargetKind.descriptorClassifierRefusal =>
        HostMoleculeGraphResultEvidenceKind.descriptorClassifierRefusal
  sourceCenterCount := HostMoleculeGraphResult.detectedTetrahedralCenterCount packet
  requiredCenterCount := target.minimumDetectedCenters
  configurationPolicy := target.configurationPolicy
  expectedOutcome? := target.expectedOutcome?
  outcomePrecondition := target.outcomePrecondition
  outcomeChecked := target.expectedOutcome?.isSome
  resultChecked := true

/-- Molecule-specific witness for this graph target and graph-source evidence. -/
def witness (requestKey : String) (packet : ExternalRawMoleculePacket)
    (target : HostGraphRelationTarget) : HostMoleculeTargetWitness where
  requestKey := requestKey
  targetKeySuffix := target.keySuffix
  targetDescription := target.description
  targetLabel := target.kind.label
  kind := HostMoleculeTargetWitnessKind.graphRelation
  coverageField := target.kind.coverageField
  observedCount := HostMoleculeGraphResult.detectedTetrahedralCenterCount packet
  requiredCount := target.minimumDetectedCenters
  coverageChecked := true
  graphResult? := some (target.graphResultEvidence packet)
  theoremFamilyKeys := target.requiredClaimTargets.map (hostAnalysisClaimPackageKey requestKey)

end HostGraphRelationTarget

/-- Target requesting a conformer-level stereochemical claim. -/
structure HostConformerClaimTarget where
  keySuffix : String
  description : String
  kind : HostConformerClaimTargetKind
  minimumConformerStates : ℕ := 1
  expectedKind? : Option OfficialStereogenicUnitKind := none
  expectedSourceKey? : Option HostMoleculeDescriptorSourceKey := none
  minimumKindCount : ℕ := 1
  deriving Repr

namespace HostConformerClaimTarget

/-- Validate host-facing metadata for a conformer-level target. -/
def validateGeneratedShape (target : HostConformerClaimTarget) : Except String Unit := do
  requireHostRequestShape (target.keySuffix ≠ "")
    "conformer target keySuffix must not be empty"
  requireHostRequestShape (hostPackageKeySegment? target.keySuffix)
    "conformer target keySuffix must be one package-key segment"
  requireHostRequestShape (target.description ≠ "")
    "conformer target description must not be empty"
  requireHostRequestShape (target.minimumConformerStates > 0)
    "conformer target minimumConformerStates must be positive"
  match target.expectedKind? with
  | none =>
      requireHostRequestShape target.expectedSourceKey?.isNone
        "conformer target expectedSourceKey requires expectedKind"
  | some kind =>
      requireHostRequestShape (kind = OfficialStereogenicUnitKind.chiral)
        "conformer profile-chirality target expectedKind must be chiral"
      let sourceKey ←
        match target.expectedSourceKey? with
        | some sourceKey => pure sourceKey
        | none => throw "conformer target expectedSourceKey must be present when expectedKind is present"
      requireHostRequestShape sourceKey.isCanonical
        "conformer target expectedSourceKey must be canonical"
      requireHostRequestShape (sourceKey.coverageField = HostMoleculeTargetCoverageField.conformer)
        "conformer target expectedSourceKey must be a conformer source key"
      requireHostRequestShape (target.minimumKindCount > 0)
        "conformer target minimumKindCount must be positive when expectedKind is present"

/-- Whether detector coverage exposes enough conformational states for this target. -/
def coverageReady (target : HostConformerClaimTarget)
    (coverage : HostDetectorCoverage) : Bool :=
  decide (coverage.conformations ≥ target.minimumConformerStates)

/-- Refuse this target if no conformational state/candidate is present. -/
def validateCoverage (target : HostConformerClaimTarget)
    (coverage : HostDetectorCoverage) : Except String Unit := do
  requireHostRequestShape (target.coverageReady coverage)
    ("requested conformer target " ++ reprStr target.keySuffix ++
      " requires at least " ++ toString target.minimumConformerStates ++
      " detected conformational state(s), but coverage has " ++
      toString coverage.conformations)

/-- Exact Rule-4a-kind result evidence for this conformer target, if requested. -/
def descriptorResultEvidence? (target : HostConformerClaimTarget)
    (packet : ExternalRawMoleculePacket) (annotations : IndexedNoncenterStereoAnnotations) :
    Option HostMoleculeDescriptorResultEvidence :=
  match target.expectedKind?, target.expectedSourceKey? with
  | some kind, some sourceKey =>
      let result := HostMoleculeDescriptorResult.conformerKind kind
      some
        { result := result
          sourceKey := sourceKey
          matchedCount := result.sourceCountForKey sourceKey packet annotations
          requiredCount := target.minimumKindCount
          resultChecked := true }
  | _, _ => none

/-- Whether exact conformer-kind evidence satisfies this target. -/
def descriptorResultReady (target : HostConformerClaimTarget)
    (coverage : HostDetectorCoverage) (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : Bool :=
  match target.descriptorResultEvidence? packet annotations with
  | none => true
  | some evidence => evidence.readyFor HostMoleculeTargetCoverageField.conformer coverage.conformations

/-- Refuse this conformer target if the requested exact kind is absent from source evidence. -/
def validateDescriptorResult (target : HostConformerClaimTarget)
    (coverage : HostDetectorCoverage) (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : Except String Unit := do
  match target.expectedKind? with
  | none =>
      requireHostRequestShape target.expectedSourceKey?.isNone
        "conformer target expectedSourceKey requires expectedKind"
  | some kind =>
      let result := HostMoleculeDescriptorResult.conformerKind kind
      let sourceKey ←
        match target.expectedSourceKey? with
        | some sourceKey => pure sourceKey
        | none => throw "conformer exact kind target is missing an expected source key"
      requireHostRequestShape (target.descriptorResultReady coverage packet annotations)
        ("requested exact conformer kind " ++ result.label ++ " for target " ++
          reprStr target.keySuffix ++ " requires at least " ++ toString target.minimumKindCount ++
          " matching source state(s), but source has " ++
          toString (result.sourceCountForKey sourceKey packet annotations))

/-- Broad theorem-family dependencies required by this target. -/
def requiredClaimTargets (target : HostConformerClaimTarget) :
    List HostStereoClaimTarget :=
  target.kind.requiredClaimTargets

/-- Molecule-specific witness for this conformer target and normalized detector coverage. -/
def witness (requestKey : String) (coverage : HostDetectorCoverage)
    (packet : ExternalRawMoleculePacket) (annotations : IndexedNoncenterStereoAnnotations)
    (target : HostConformerClaimTarget) : HostMoleculeTargetWitness where
  requestKey := requestKey
  targetKeySuffix := target.keySuffix
  targetDescription := target.description
  targetLabel := target.kind.label
  kind := HostMoleculeTargetWitnessKind.conformerClaim
  coverageField := HostMoleculeTargetCoverageField.conformer
  observedCount := coverage.conformations
  requiredCount := target.minimumConformerStates
  coverageChecked := true
  descriptorResult? := target.descriptorResultEvidence? packet annotations
  theoremFamilyKeys := target.requiredClaimTargets.map (hostAnalysisClaimPackageKey requestKey)

end HostConformerClaimTarget

/-- Target requesting an ensemble-level stereochemical claim. -/
structure HostEnsembleClaimTarget where
  keySuffix : String
  description : String
  kind : HostEnsembleClaimTargetKind
  minimumEnsembleStates : ℕ := 1
  expectedKind? : Option OfficialStereogenicUnitKind := none
  expectedSourceKey? : Option HostMoleculeDescriptorSourceKey := none
  minimumKindCount : ℕ := 1
  deriving Repr

namespace HostEnsembleClaimTarget

/-- Validate host-facing metadata for an ensemble-level target. -/
def validateGeneratedShape (target : HostEnsembleClaimTarget) : Except String Unit := do
  requireHostRequestShape (target.keySuffix ≠ "")
    "ensemble target keySuffix must not be empty"
  requireHostRequestShape (hostPackageKeySegment? target.keySuffix)
    "ensemble target keySuffix must be one package-key segment"
  requireHostRequestShape (target.description ≠ "")
    "ensemble target description must not be empty"
  requireHostRequestShape (target.minimumEnsembleStates > 0)
    "ensemble target minimumEnsembleStates must be positive"
  match target.expectedKind? with
  | none =>
      requireHostRequestShape target.expectedSourceKey?.isNone
        "ensemble target expectedSourceKey requires expectedKind"
  | some kind =>
      requireHostRequestShape (kind = OfficialStereogenicUnitKind.chiral)
        "ensemble descriptor-chirality target expectedKind must be chiral"
      let sourceKey ←
        match target.expectedSourceKey? with
        | some sourceKey => pure sourceKey
        | none => throw "ensemble target expectedSourceKey must be present when expectedKind is present"
      requireHostRequestShape sourceKey.isCanonical
        "ensemble target expectedSourceKey must be canonical"
      requireHostRequestShape (sourceKey.coverageField = HostMoleculeTargetCoverageField.ensemble)
        "ensemble target expectedSourceKey must be an ensemble source key"
      requireHostRequestShape (target.minimumKindCount > 0)
        "ensemble target minimumKindCount must be positive when expectedKind is present"

/-- Whether detector coverage exposes enough ensemble states for this target. -/
def coverageReady (target : HostEnsembleClaimTarget)
    (coverage : HostDetectorCoverage) : Bool :=
  decide (coverage.ensembles ≥ target.minimumEnsembleStates)

/-- Refuse this target if no ensemble state is present. -/
def validateCoverage (target : HostEnsembleClaimTarget)
    (coverage : HostDetectorCoverage) : Except String Unit := do
  requireHostRequestShape (target.coverageReady coverage)
    ("requested ensemble target " ++ reprStr target.keySuffix ++
      " requires at least " ++ toString target.minimumEnsembleStates ++
      " detected ensemble state(s), but coverage has " ++ toString coverage.ensembles)

/-- Exact Rule-4a-kind result evidence for this ensemble target, if requested. -/
def descriptorResultEvidence? (target : HostEnsembleClaimTarget)
    (packet : ExternalRawMoleculePacket) (annotations : IndexedNoncenterStereoAnnotations) :
    Option HostMoleculeDescriptorResultEvidence :=
  match target.expectedKind?, target.expectedSourceKey? with
  | some kind, some sourceKey =>
      let result := HostMoleculeDescriptorResult.ensembleKind kind
      some
        { result := result
          sourceKey := sourceKey
          matchedCount := result.sourceCountForKey sourceKey packet annotations
          requiredCount := target.minimumKindCount
          resultChecked := true }
  | _, _ => none

/-- Whether exact ensemble-kind evidence satisfies this target. -/
def descriptorResultReady (target : HostEnsembleClaimTarget)
    (coverage : HostDetectorCoverage) (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : Bool :=
  match target.descriptorResultEvidence? packet annotations with
  | none => true
  | some evidence => evidence.readyFor HostMoleculeTargetCoverageField.ensemble coverage.ensembles

/-- Refuse this ensemble target if the requested exact kind is absent from source evidence. -/
def validateDescriptorResult (target : HostEnsembleClaimTarget)
    (coverage : HostDetectorCoverage) (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : Except String Unit := do
  match target.expectedKind? with
  | none => pure ()
  | some kind =>
      let result := HostMoleculeDescriptorResult.ensembleKind kind
      let sourceKey ←
        match target.expectedSourceKey? with
        | some sourceKey => pure sourceKey
        | none => throw "ensemble exact kind target is missing an expected source key"
      requireHostRequestShape (target.descriptorResultReady coverage packet annotations)
        ("requested exact ensemble kind " ++ result.label ++ " for target " ++
          reprStr target.keySuffix ++ " requires at least " ++ toString target.minimumKindCount ++
          " matching source state(s), but source has " ++
          toString (result.sourceCountForKey sourceKey packet annotations))

/-- Broad theorem-family dependencies required by this target. -/
def requiredClaimTargets (target : HostEnsembleClaimTarget) :
    List HostStereoClaimTarget :=
  target.kind.requiredClaimTargets

/-- Molecule-specific witness for this ensemble target and normalized detector coverage. -/
def witness (requestKey : String) (coverage : HostDetectorCoverage)
    (packet : ExternalRawMoleculePacket) (annotations : IndexedNoncenterStereoAnnotations)
    (target : HostEnsembleClaimTarget) : HostMoleculeTargetWitness where
  requestKey := requestKey
  targetKeySuffix := target.keySuffix
  targetDescription := target.description
  targetLabel := target.kind.label
  kind := HostMoleculeTargetWitnessKind.ensembleClaim
  coverageField := HostMoleculeTargetCoverageField.ensemble
  observedCount := coverage.ensembles
  requiredCount := target.minimumEnsembleStates
  coverageChecked := true
  descriptorResult? := target.descriptorResultEvidence? packet annotations
  theoremFamilyKeys := target.requiredClaimTargets.map (hostAnalysisClaimPackageKey requestKey)

end HostEnsembleClaimTarget

/-- Typed package-selection targets that a host can request for one molecule.

Official-center targets generate molecule-specific official-stereo certificates.  Non-center,
graph, conformer, and ensemble targets emit source-bound molecule-specific target-witness/target
certificate packages and select broad theorem-family packages. -/
inductive HostStereochemicalOutputTarget where
  | officialCenterComparison (target : HostOfficialStereoAnalysisTarget)
  | noncenterDescriptor (target : HostNoncenterDescriptorTarget)
  | graphRelation (target : HostGraphRelationTarget)
  | conformerClaim (target : HostConformerClaimTarget)
  | ensembleClaim (target : HostEnsembleClaimTarget)
  deriving Repr

namespace HostStereochemicalOutputTarget

/-- Host-facing key suffix for this output target. -/
def keySuffix : HostStereochemicalOutputTarget → String
  | officialCenterComparison target => target.keySuffix
  | noncenterDescriptor target => target.keySuffix
  | graphRelation target => target.keySuffix
  | conformerClaim target => target.keySuffix
  | ensembleClaim target => target.keySuffix

/-- Official-stereo branch analysis generated by this target, if any. -/
def officialStereoTarget? :
    HostStereochemicalOutputTarget → Option HostOfficialStereoAnalysisTarget
  | officialCenterComparison target => some target
  | _ => none

/-- Broad theorem-family dependencies required by this output target. -/
def requiredClaimTargets : HostStereochemicalOutputTarget → List HostStereoClaimTarget
  | officialCenterComparison _ =>
      [HostStereoClaimTarget.officialCIPAssignmentSuccessResolved]
  | noncenterDescriptor target => target.requiredClaimTargets
  | graphRelation target => target.requiredClaimTargets
  | conformerClaim target => target.requiredClaimTargets
  | ensembleClaim target => target.requiredClaimTargets

/-- Validate generated names for this output target. -/
def validateGeneratedShape : HostStereochemicalOutputTarget → Except String Unit
  | officialCenterComparison target => target.validateGeneratedShape
  | noncenterDescriptor target => target.validateGeneratedShape
  | graphRelation target => target.validateGeneratedShape
  | conformerClaim target => target.validateGeneratedShape
  | ensembleClaim target => target.validateGeneratedShape

/-- Validate target coverage against a normalized detector coverage summary. -/
def validateCoverage (coverage : HostDetectorCoverage) :
    HostStereochemicalOutputTarget → Except String Unit
  | officialCenterComparison _ => Except.ok ()
  | noncenterDescriptor target => target.validateCoverage coverage
  | graphRelation _ => Except.ok ()
  | conformerClaim target => target.validateCoverage coverage
  | ensembleClaim target => target.validateCoverage coverage

/-- Validate graph-source evidence for graph-level targets. -/
def validateGraphCoverage (packet : ExternalRawMoleculePacket) :
    HostStereochemicalOutputTarget → Except String Unit
  | graphRelation target => target.validateCoverage packet
  | _ => Except.ok ()

/-- Validate exact descriptor-result evidence requested by this output target, if any. -/
def validateDescriptorResult (coverage : HostDetectorCoverage)
    (packet : ExternalRawMoleculePacket) (annotations : IndexedNoncenterStereoAnnotations) :
    HostStereochemicalOutputTarget → Except String Unit
  | officialCenterComparison _ => Except.ok ()
  | noncenterDescriptor target => target.validateDescriptorResult coverage packet annotations
  | graphRelation _ => Except.ok ()
  | conformerClaim target => target.validateDescriptorResult coverage packet annotations
  | ensembleClaim target => target.validateDescriptorResult coverage packet annotations

/-- Molecule-specific coverage-bearing target witness generated by this output target, if any. -/
def witness? (requestKey : String) (coverage : HostDetectorCoverage)
    (packet : ExternalRawMoleculePacket) (annotations : IndexedNoncenterStereoAnnotations) :
    HostStereochemicalOutputTarget → Option HostMoleculeTargetWitness
  | officialCenterComparison _ => none
  | noncenterDescriptor target => some (target.witness requestKey coverage packet annotations)
  | graphRelation target => some (target.witness requestKey packet)
  | conformerClaim target => some (target.witness requestKey coverage packet annotations)
  | ensembleClaim target => some (target.witness requestKey coverage packet annotations)

/-- Whether this output target should emit a coverage-bearing target witness. -/
def emitsCoverageWitness : HostStereochemicalOutputTarget → Bool
  | noncenterDescriptor _ => true
  | graphRelation _ => true
  | conformerClaim _ => true
  | ensembleClaim _ => true
  | officialCenterComparison _ => false

end HostStereochemicalOutputTarget


structure HostStereochemicalAnalysisPlan where
  outputs : List HostStereochemicalOutputTarget := []
  deriving Repr

namespace HostStereochemicalAnalysisPlan


def officialStereoTargets (plan : HostStereochemicalAnalysisPlan) :
    List HostOfficialStereoAnalysisTarget :=
  plan.outputs.filterMap HostStereochemicalOutputTarget.officialStereoTarget?


def requiredClaimTargets (plan : HostStereochemicalAnalysisPlan) :
    List HostStereoClaimTarget :=
  deduplicateHostStereoClaimTargets
    (plan.outputs.flatMap HostStereochemicalOutputTarget.requiredClaimTargets)


def outputKeySuffixes (plan : HostStereochemicalAnalysisPlan) : List String :=
  plan.outputs.map HostStereochemicalOutputTarget.keySuffix


def hasCoverageWitnessTargets (plan : HostStereochemicalAnalysisPlan) : Bool :=
  plan.outputs.any HostStereochemicalOutputTarget.emitsCoverageWitness


def validateGeneratedShape (plan : HostStereochemicalAnalysisPlan) : Except String Unit := do
  for target in plan.outputs do
    target.validateGeneratedShape
  requireHostRequestShape (!hasDuplicateStrings plan.outputKeySuffixes)
    "stereochemical analysis plan contains duplicate output key suffixes"


def validateCoverage (plan : HostStereochemicalAnalysisPlan)
    (coverage : HostDetectorCoverage) : Except String Unit := do
  for target in plan.outputs do
    target.validateCoverage coverage


def validateGraphCoverage (plan : HostStereochemicalAnalysisPlan)
    (packet : ExternalRawMoleculePacket) : Except String Unit := do
  for target in plan.outputs do
    target.validateGraphCoverage packet


def validateDescriptorResults (plan : HostStereochemicalAnalysisPlan)
    (coverage : HostDetectorCoverage) (packet : ExternalRawMoleculePacket)
    (annotations : IndexedNoncenterStereoAnnotations) : Except String Unit := do
  for target in plan.outputs do
    target.validateDescriptorResult coverage packet annotations

end HostStereochemicalAnalysisPlan

/-- A host-facing molecule analysis request that derives generated package and suite requests. -/
structure HostMoleculeAnalysisRequest where
  key : String
  description : String
  packet : ExternalRawMoleculePacket
  annotations : IndexedNoncenterStereoAnnotations := {}
  analysisPlan : HostStereochemicalAnalysisPlan := {}
  officialStereoTargets : List HostOfficialStereoAnalysisTarget := []
  broadClaimPolicy : HostBroadClaimPolicy := HostBroadClaimPolicy.all
  moduleNamespaceBase : List String := ["TetraStereoGenerated", "HostAnalyses", "Modules"]
  certificateNamespaceBase : List String := ["TetraStereoGenerated", "HostAnalyses", "Certificates"]
  claimNamespacePath : List String := ["TetraStereoGenerated", "HostAnalyses", "Claims"]
  witnessNamespacePath : List String := ["TetraStereoGenerated", "HostAnalyses", "Witnesses"]
  suiteNamespacePath : List String := ["TetraStereoGenerated", "HostAnalyses", "Suites"]
  suiteFileName : String := "HostMoleculeAnalysisSuite.lean"
  suiteTheoremName : String := "host_molecule_analysis_suite_checked"

namespace HostMoleculeAnalysisRequest

/-- Normalized detector coverage for this request's shared molecule packet and annotations. -/
def detectorCoverage (request : HostMoleculeAnalysisRequest) : HostDetectorCoverage :=
  HostDetectorCoverage.ofPacketAndAnnotations request.packet request.annotations

/-- Whether a requested host atom index is detected as a tetrahedral center in the raw graph. -/
def centerAtomDetected (request : HostMoleculeAnalysisRequest) (idx : ℕ) : Bool :=
  HostMoleculeGraphResult.rawTetrahedralCenterDetected request.packet.raw idx

/-- Validate atom/branch bounds that generated `Fin` terms require before writing source. -/
def validateOfficialTargetBounds
    (request : HostMoleculeAnalysisRequest)
    (target : HostOfficialStereoAnalysisTarget) : Except String Unit := do
  requireHostRequestShape (target.centerAtom < request.packet.raw.atomCount)
    ("official-stereo target " ++ reprStr target.keySuffix ++
      " has centerAtom outside raw atom range")
  requireHostRequestShape (target.left < 4)
    ("official-stereo target " ++ reprStr target.keySuffix ++
      " has left branch outside Fin 4")
  requireHostRequestShape (target.right < 4)
    ("official-stereo target " ++ reprStr target.keySuffix ++
      " has right branch outside Fin 4")
  requireHostRequestShape (request.centerAtomDetected target.centerAtom)
    ("official-stereo target " ++ reprStr target.keySuffix ++
      " does not select an automatically detected tetrahedral center")

/-- Convert one requested branch analysis into a generated official-stereo host package request. -/
def officialStereoRequest
    (request : HostMoleculeAnalysisRequest)
    (target : HostOfficialStereoAnalysisTarget) : HostOfficialStereoRequest where
  key := hostScopedPackageKey request.key target.keySuffix
  description := request.description ++ ": " ++ target.description
  ownerRequestKey := request.key
  packageKeySuffix := target.keySuffix
  moduleFileName := target.moduleFileName
  namespacePath := request.moduleNamespaceBase ++ target.moduleNamespaceSuffix
  definitionPrefix := target.definitionPrefix
  packet := request.packet
  annotations := request.annotations
  centerAtom := target.centerAtom
  left := target.left
  right := target.right
  profile := target.profile
  graphFuel := target.graphFuel
  scheduleFuel := target.scheduleFuel
  branchFuel := target.branchFuel
  target := target.target
  certificateFileName := target.certificateFileName
  certificateTheoremName := target.certificateTheoremName
  certificateNamespacePath := request.certificateNamespaceBase

/-- All molecule-derived official-stereo generated package requests for this analysis. -/
def officialStereoRequests (request : HostMoleculeAnalysisRequest) :
    List HostOfficialStereoRequest :=
  (request.officialStereoTargets ++ request.analysisPlan.officialStereoTargets).map
    request.officialStereoRequest

/-- Registry keys emitted by all derived official-stereo generated packages. -/
def officialStereoRequestKeys (request : HostMoleculeAnalysisRequest) : List String :=
  request.officialStereoRequests.map fun officialRequest => officialRequest.key

/-- Convert one broad theorem-family target into a generated broad claim package request. -/
def claimRequest
    (request : HostMoleculeAnalysisRequest) (target : HostStereoClaimTarget) :
    HostStereoClaimRequest where
  target := target
  key := hostAnalysisClaimPackageKey request.key target
  description := request.description ++ ": " ++ target.defaultDescription
  namespacePath := request.claimNamespacePath ++ [leanIdentifierSlug request.key]

/-- All broad claim package requests included by this molecule analysis. -/
def claimRequests (request : HostMoleculeAnalysisRequest) : List HostStereoClaimRequest :=
  (deduplicateHostStereoClaimTargets
    (request.analysisPlan.requiredClaimTargets ++ request.broadClaimPolicy.targets)).map
      request.claimRequest

/-- Registry keys emitted by all derived broad theorem-family generated packages. -/
def claimRequestKeys (request : HostMoleculeAnalysisRequest) : List String :=
  request.claimRequests.map fun claimRequest => claimRequest.key

/-- Find an included broad claim package by key. -/
def claimRequestByKey? (request : HostMoleculeAnalysisRequest) (key : String) :
    Option HostStereoClaimRequest :=
  request.claimRequests.find? fun claimRequest => claimRequest.key == key

/-- Generated claim modules required by witness theorem-family keys. -/
def claimModulesForKeys (request : HostMoleculeAnalysisRequest) (keys : List String) :
    List String :=
  keys.filterMap fun key =>
    (request.claimRequestByKey? key).map fun claimRequest =>
      HostAnalysisSuiteRequest.claimModuleName claimRequest

/-- Generated claim theorems required by witness theorem-family keys. -/
def claimTheoremsForKeys (request : HostMoleculeAnalysisRequest) (keys : List String) :
    List String :=
  keys.filterMap fun key =>
    (request.claimRequestByKey? key).map fun claimRequest =>
      HostAnalysisSuiteRequest.claimTheoremName claimRequest

/-- Generated host module used as the source for coverage recomputation, if available. -/
def coverageSourceRequest? (request : HostMoleculeAnalysisRequest) :
    Option HostOfficialStereoRequest :=
  request.officialStereoRequests.head?

/-- Exact imports for a molecule-derived target-witness package. -/
def witnessImportsForKeys
    (request : HostMoleculeAnalysisRequest) (coverageSourceModule : String) (keys : List String) :
    List String :=
  ["TetraStereo.Engine.HostAnalysisRequestBuilder", coverageSourceModule] ++
    request.claimModulesForKeys keys

/-- Convert one non-official package-selection output into a molecule-specific target certificate package. -/
def witnessRequest?
    (request : HostMoleculeAnalysisRequest)
    (target : HostStereochemicalOutputTarget) : Option HostMoleculeTargetWitnessRequest := do
  let witness ← target.witness? request.key request.detectorCoverage request.packet request.annotations
  let coverageSource ← request.coverageSourceRequest?
  let dependencyKeys := witness.theoremFamilyKeys
  let coverageSourceModule := coverageSource.moduleName
  some
    { key := witness.expectedPackageKey
      description :=
        request.description ++ ": molecule-specific target certificate for " ++
          witness.targetKeySuffix
      witness := witness
      fileName := witness.expectedFileName
      namespacePath := request.witnessNamespacePath
      definitionName := witness.expectedDefinitionName
      theoremName := witness.expectedTheoremName
      coverageSourceModule := coverageSourceModule
      coverageSourcePacketName :=
        HostAnalysisSuiteRequest.officialCoveragePacketName coverageSource
      coverageSourceAnnotationsName :=
        HostAnalysisSuiteRequest.officialCoverageAnnotationsName coverageSource
      coverageSourceBlueprintName :=
        HostAnalysisSuiteRequest.officialCoverageBlueprintName coverageSource
      coverageSourceOwnerName :=
        HostAnalysisSuiteRequest.officialCoverageOwnerRequestKeyName coverageSource
      coverageTheoremName := witness.expectedCoverageTheoremName
      dependencyTheoremNames := request.claimTheoremsForKeys dependencyKeys
      imports := request.witnessImportsForKeys coverageSourceModule dependencyKeys }


def witnessRequestsFromOutputs
    (request : HostMoleculeAnalysisRequest) :
    List HostStereochemicalOutputTarget → List HostMoleculeTargetWitnessRequest
  | [] => []
  | target :: rest =>
      let tail := request.witnessRequestsFromOutputs rest
      match request.witnessRequest? target with
      | some witnessRequest => witnessRequest :: tail
      | none => tail


def witnessRequests (request : HostMoleculeAnalysisRequest) :
    List HostMoleculeTargetWitnessRequest :=
  request.witnessRequestsFromOutputs request.analysisPlan.outputs

/-- Registry keys emitted by all derived target-certificate packages. -/
def witnessRequestKeys (request : HostMoleculeAnalysisRequest) : List String :=
  request.witnessRequests.map fun witnessRequest => witnessRequest.key

/-- Registry keys emitted by all derived public target certificates. -/
def witnessCertificateKeys (request : HostMoleculeAnalysisRequest) : List String :=
  request.witnessRequests.map fun witnessRequest => witnessRequest.certificate.key

/-- Registry keys emitted by all generated packages in this molecule-analysis request. -/
def packageRequestKeys (request : HostMoleculeAnalysisRequest) : List String :=
  request.officialStereoRequestKeys ++ request.claimRequestKeys ++ request.witnessRequestKeys ++
    request.witnessCertificateKeys

/-- The generated suite request induced by this molecule-analysis request. -/
def suiteRequest (request : HostMoleculeAnalysisRequest) : HostAnalysisSuiteRequest where
  key := request.key
  description := request.description
  officialStereoRequests := request.officialStereoRequests
  claimRequests := request.claimRequests
  witnessRequests := request.witnessRequests
  namespacePath := request.suiteNamespacePath
  fileName := request.suiteFileName
  theoremName := request.suiteTheoremName

/-- Validate molecule-analysis fields and derived package keys before suite validation. -/
def validateGeneratedPrefixShape (request : HostMoleculeAnalysisRequest) : Except String Unit := do
  requireHostRequestShape (hostPackageKeySegment? request.key)
    "host molecule analysis key must be one package-key segment"
  requireHostRequestShape (request.description ≠ "")
    "host molecule analysis description must not be empty"
  validateNamespacePath "moduleNamespaceBase" request.moduleNamespaceBase
  validateNamespacePath "certificateNamespaceBase" request.certificateNamespaceBase
  validateNamespacePath "claimNamespacePath" request.claimNamespacePath
  validateNamespacePath "witnessNamespacePath" request.witnessNamespacePath
  validateNamespacePath "suiteNamespacePath" request.suiteNamespacePath
  validateImportableLeanFileName "suiteFileName" request.suiteFileName
  validateLeanNames "suite theorem names" [request.suiteTheoremName]
  requireHostRequestShape request.packet.raw.admissible?
    "host molecule analysis raw molecule is not admissible"
  for target in request.officialStereoTargets do
    target.validateGeneratedShape
    request.validateOfficialTargetBounds target
  request.analysisPlan.validateGeneratedShape
  for target in request.analysisPlan.officialStereoTargets do
    request.validateOfficialTargetBounds target
  request.analysisPlan.validateCoverage request.detectorCoverage
  request.analysisPlan.validateGraphCoverage request.packet
  request.analysisPlan.validateDescriptorResults request.detectorCoverage request.packet request.annotations
  requireHostRequestShape
    (!request.analysisPlan.hasCoverageWitnessTargets || !request.officialStereoRequests.isEmpty)
    "coverage-bearing target witnesses require at least one generated host molecule module"
  requireHostRequestShape (!hasDuplicateStrings request.officialStereoRequestKeys)
    "host molecule analysis emits duplicate official-stereo package keys"
  requireHostRequestShape (!hasDuplicateStrings request.claimRequestKeys)
    "host molecule analysis emits duplicate broad-claim package keys"
  requireHostRequestShape (!hasDuplicateStrings request.packageRequestKeys)
    "host molecule analysis emits duplicate generated package keys"

/-- Validate the generated package shape induced by this molecule-analysis request. -/
def validateGeneratedShape (request : HostMoleculeAnalysisRequest) : Except String Unit := do
  request.validateGeneratedPrefixShape
  request.suiteRequest.validateGeneratedShape

/-- Write all generated package files for the suite induced by this molecule-analysis request. -/
def writeSuitePackageSources
    (request : HostMoleculeAnalysisRequest) (packageRoot : String) :
    IO HostAnalysisSuiteRequest.PackagePaths := do
  match request.validateGeneratedShape with
  | Except.ok () => pure ()
  | Except.error message => throw (IO.userError message)
  request.suiteRequest.writePackageSources packageRoot

/-- Write, compile, and verify the generated suite induced by this molecule-analysis request. -/
def writeAndVerifySuitePackageSources
    (request : HostMoleculeAnalysisRequest) (packageRoot : String) :
    IO HostAnalysisSuiteRequest.VerificationResult := do
  match request.validateGeneratedShape with
  | Except.ok () => pure ()
  | Except.error message => throw (IO.userError message)
  request.suiteRequest.writeAndVerifyPackageSources packageRoot

end HostMoleculeAnalysisRequest

end
end Engine
end TetraStereo
