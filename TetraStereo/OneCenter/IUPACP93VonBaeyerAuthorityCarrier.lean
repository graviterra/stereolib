import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

/-!
# Authority carrier for the four von Baeyer P-93 rows

A von Baeyer system is carried as two bridgeheads and three internally disjoint constitutional
paths.  The source dimensions are therefore derived from graph-bearing lists instead of accepted
as three unrelated natural numbers.  Descriptor citations, qualitative bridge orientation,
bridgehead-relative notation, and the bicyclo[3.3.3] double-bond threshold remain audited
source relations.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Cyclic

structure P93AuthorityVonBaeyerSystem where
  firstBridgehead : Nat
  secondBridgehead : Nat
  xBridgeInternal : List Nat
  yBridgeInternal : List Nat
  zBridgeInternal : List Nat
  deriving DecidableEq, Repr

namespace P93AuthorityVonBaeyerSystem

def atoms (system : P93AuthorityVonBaeyerSystem) : List Nat :=
  [system.firstBridgehead, system.secondBridgehead] ++
    system.xBridgeInternal ++ system.yBridgeInternal ++ system.zBridgeInternal

def bridgePath (system : P93AuthorityVonBaeyerSystem)
    (internal : List Nat) : List Nat :=
  system.firstBridgehead :: internal ++ [system.secondBridgehead]

def dimensions (system : P93AuthorityVonBaeyerSystem) : VonBaeyerBridgeSystem where
  x := system.xBridgeInternal.length
  y := system.yBridgeInternal.length
  z := system.zBridgeInternal.length

def MechanicallyValidFor
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityVonBaeyerSystem) : Prop :=
  system.firstBridgehead < system.secondBridgehead ∧
    system.atoms.Nodup ∧
    P93AuthorityAtomsBounded source system.atoms ∧
    0 < system.yBridgeInternal.length ∧
    system.yBridgeInternal.length ≤ system.xBridgeInternal.length ∧
    system.zBridgeInternal.length ≤ system.yBridgeInternal.length ∧
    P93AuthorityConnectedPath source
      (system.bridgePath system.xBridgeInternal) ∧
    P93AuthorityConnectedPath source
      (system.bridgePath system.yBridgeInternal) ∧
    P93AuthorityConnectedPath source
      (system.bridgePath system.zBridgeInternal)

end P93AuthorityVonBaeyerSystem

structure P93VonBaeyerAuthorityPolicy where
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  SystemObserved :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem → Prop
  UnitInSystemObserved :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem →
      P93AuthorityPhysicalUnit → Prop
  CitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCitationToken →
      P93AuthorityPhysicalUnit → Prop
  CenterKindObserved :
    AuthoritativeChemicalInput → Nat → BlueBookP93.Acyclic.UnitKind → Prop
  CenterDescriptorAuthorized :
    AuthoritativeChemicalInput → Nat → BlueBookP93.Acyclic.Descriptor → Prop
  CenterConfigurationKnowledgeObserved :
    AuthoritativeChemicalInput → Nat → ConfigurationKnowledge → Prop
  CenterNotationObserved :
    AuthoritativeChemicalInput → Nat → ConfigurationKnowledge →
      MonocycleNotation → Prop
  BridgeAttachmentObserved :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem →
      Nat → Nat → BridgeAttachment → Prop
  BridgeheadLigandSideObserved :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem →
      Nat → Nat → RingSide → Prop
  BridgeheadRelativeNotationObserved :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem →
      Bool → BridgeheadRelativeNotation → Prop
  LargerThanBicyclo333Observed :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem → Bool → Prop
  SeniorLigandGeometryObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      MonocyclicSeniorLigandGeometry → Prop
  OrdinaryDoubleBondNamingAuthorized :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem →
      P93AuthorityPhysicalUnit → Bool → Bool →
        Option BlueBookP93.Acyclic.Descriptor → Prop
  IncludedCumuleneNumberingObserved :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem →
      List Nat → P93AuthorityCitationToken → Prop
  IncludedCumuleneNamingContextObserved :
    AuthoritativeChemicalInput → P93AuthorityVonBaeyerSystem →
      P93AuthorityPhysicalUnit → BlueBookP93.Acyclic.NomenclatureContext → Prop

def P93AuthorityVonBaeyerSystem.ValidFor
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityVonBaeyerSystem) : Prop :=
  system.MechanicallyValidFor source ∧
    policy.SystemObserved source system

def P93VonBaeyerUnitSupported
    (system : P93AuthorityVonBaeyerSystem) : P93AuthorityPhysicalUnit → Prop
  | .atomCenter center => center ∈ system.atoms
  | .bond first second => first ∈ system.atoms ∧ second ∈ system.atoms
  | .axis path => path ≠ [] ∧ ∀ atom ∈ path, atom ∈ system.atoms
  | .plane _ | .helix _ | .polyhedron _ _ => False

structure P93VonBaeyerCenterAuthorityObservation
    (policy : P93VonBaeyerAuthorityPolicy) where
  system : P93AuthorityVonBaeyerSystem
  unit : P93AuthorityPhysicalUnit
  citation : P93AuthorityCitationToken
  kind : BlueBookP93.Acyclic.UnitKind
  descriptor : BlueBookP93.Acyclic.Descriptor
  knowledge : ConfigurationKnowledge
  «notation» : MonocycleNotation

def P93VonBaeyerCenterAuthorityObservation.ValidFor
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerCenterAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    observation.unit.ValidFor policy.physicalObservation source ∧
    P93VonBaeyerUnitSupported observation.system observation.unit ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    (∃ center, observation.unit = .atomCenter center ∧
      policy.CenterKindObserved source center observation.kind ∧
      policy.CenterDescriptorAuthorized source center observation.descriptor ∧
      policy.CenterConfigurationKnowledgeObserved source center observation.knowledge ∧
      policy.CenterNotationObserved source center observation.knowledge
        observation.notation) ∧
    (observation.kind = .chiralCenter ∨
      observation.kind = .pseudoasymmetricCenter) ∧
    BlueBookP93.Acyclic.DescriptorApplies observation.kind observation.descriptor ∧
    observation.notation = PreferredMonocycleNotation observation.knowledge ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit

structure P93VonBaeyerBridgeOrientationAuthorityObservation
    (policy : P93VonBaeyerAuthorityPolicy) where
  system : P93AuthorityVonBaeyerSystem
  attachmentAtom : Nat
  substituent : Nat
  citation : P93AuthorityCitationToken
  attachment : BridgeAttachment
  descriptor : BridgeDescriptor

def P93VonBaeyerBridgeOrientationAuthorityObservation.ValidFor
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    EndoExoSynAntiApplicable observation.system.dimensions ∧
    observation.attachmentAtom ∈ observation.system.atoms ∧
    observation.substituent ∉ observation.system.atoms ∧
    P93AuthorityBinaryBond source observation.attachmentAtom observation.substituent ∧
    (P93AuthorityPhysicalUnit.atomCenter observation.attachmentAtom).ValidFor
      policy.physicalObservation source ∧
    policy.UnitInSystemObserved source observation.system
      (P93AuthorityPhysicalUnit.atomCenter observation.attachmentAtom) ∧
    policy.BridgeAttachmentObserved source observation.system
      observation.attachmentAtom observation.substituent observation.attachment ∧
    observation.descriptor = bridgeDescriptor observation.attachment ∧
    ¬BridgeDescriptorDeterminesAbsolute observation.descriptor ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation
      (P93AuthorityPhysicalUnit.atomCenter observation.attachmentAtom)

def P93VonBaeyerOptionalBridgeheadCitationValid
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput) (bridgehead : Nat) :
    Option P93AuthorityCitationToken → Prop
  | none => True
  | some citation =>
      citation.Valid ∧
        policy.CitationAuthorized source citation
          (P93AuthorityPhysicalUnit.atomCenter bridgehead)

structure P93VonBaeyerBridgeheadRelativeAuthorityObservation
    (policy : P93VonBaeyerAuthorityPolicy) where
  system : P93AuthorityVonBaeyerSystem
  firstLigand : Nat
  secondLigand : Nat
  firstCitation? : Option P93AuthorityCitationToken
  secondCitation? : Option P93AuthorityCitationToken
  firstSide : RingSide
  secondSide : RingSide
  descriptor : CisTrans
  contextIsPIN : Bool
  «notation» : BridgeheadRelativeNotation

def P93VonBaeyerBridgeheadRelativeAuthorityObservation.ValidFor
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    observation.firstLigand ≠ observation.secondLigand ∧
    observation.firstLigand ∉ observation.system.atoms ∧
    observation.secondLigand ∉ observation.system.atoms ∧
    P93AuthorityBinaryBond source observation.system.firstBridgehead
      observation.firstLigand ∧
    P93AuthorityBinaryBond source observation.system.secondBridgehead
      observation.secondLigand ∧
    policy.BridgeheadLigandSideObserved source observation.system
      observation.system.firstBridgehead observation.firstLigand
      observation.firstSide ∧
    policy.BridgeheadLigandSideObserved source observation.system
      observation.system.secondBridgehead observation.secondLigand
      observation.secondSide ∧
    RelativeRingSide observation.firstSide observation.secondSide
      observation.descriptor ∧
    policy.BridgeheadRelativeNotationObserved source observation.system
      observation.contextIsPIN observation.notation ∧
    (observation.contextIsPIN = true →
      PreferredBridgeheadRelativeNotation observation.notation) ∧
    P93VonBaeyerOptionalBridgeheadCitationValid policy source
      observation.system.firstBridgehead observation.firstCitation? ∧
    P93VonBaeyerOptionalBridgeheadCitationValid policy source
      observation.system.secondBridgehead observation.secondCitation? ∧
    (observation.contextIsPIN = true →
      ∃ firstCitation secondCitation,
        observation.firstCitation? = some firstCitation ∧
          observation.secondCitation? = some secondCitation)

def P93VonBaeyerOrdinaryDoubleBondExpected
    (largerThanBicyclo333 : Bool)
    (geometry : MonocyclicSeniorLigandGeometry) :
    Option BlueBookP93.Acyclic.Descriptor :=
  if VonBaeyerDoubleBondDescriptorRequired largerThanBicyclo333 = true then
    match geometry with
    | .together => some .Z
    | .opposite => some .E
  else
    none

def P93VonBaeyerOrdinaryDescriptorAllowed :
    Option BlueBookP93.Acyclic.Descriptor → Prop
  | none | some .E | some .Z => True
  | _ => False

inductive P93VonBaeyerUnsaturationSpecification where
  | ordinaryDoubleBond
      (contextIsPIN : Bool)
      (largerThanBicyclo333 : Bool)
      (geometry : MonocyclicSeniorLigandGeometry)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor)
  | includedOpenCumulene
      (context : BlueBookP93.Acyclic.NomenclatureContext)
      (parity : OpenCumuleneParity)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  deriving DecidableEq, Repr

structure P93VonBaeyerUnsaturationAuthorityObservation
    (policy : P93VonBaeyerAuthorityPolicy) where
  system : P93AuthorityVonBaeyerSystem
  unit : P93AuthorityPhysicalUnit
  citation : P93AuthorityCitationToken
  specification : P93VonBaeyerUnsaturationSpecification

def P93VonBaeyerUnsaturationAuthorityObservation.ValidFor
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerUnsaturationAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    observation.unit.ValidFor policy.physicalObservation source ∧
    P93VonBaeyerUnitSupported observation.system observation.unit ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit ∧
    match observation.specification with
    | .ordinaryDoubleBond contextIsPIN largerThanBicyclo333 geometry descriptor? =>
        (∃ first second, observation.unit = .bond first second) ∧
          policy.LargerThanBicyclo333Observed source observation.system
            largerThanBicyclo333 ∧
          policy.SeniorLigandGeometryObserved source observation.unit geometry ∧
          policy.OrdinaryDoubleBondNamingAuthorized source observation.system
            observation.unit contextIsPIN largerThanBicyclo333 descriptor? ∧
          P93VonBaeyerOrdinaryDescriptorAllowed descriptor? ∧
          (contextIsPIN = true →
            descriptor? = P93VonBaeyerOrdinaryDoubleBondExpected
              largerThanBicyclo333 geometry)
    | .includedOpenCumulene context parity descriptor =>
        (∃ path, observation.unit = .axis path ∧
          policy.IncludedCumuleneNumberingObserved source observation.system
            path observation.citation) ∧
          policy.IncludedCumuleneNamingContextObserved source observation.system
            observation.unit context ∧
          OpenTerminalCumuleneDescriptorApplies
            .includedOpenCumuleneSegment parity descriptor ∧
          match parity with
          | .even =>
              BlueBookP93.Acyclic.DescriptorRecommended context
                .evenDoubleBondCumulene descriptor
          | .odd =>
              BlueBookP93.Acyclic.DescriptorRecommended context
                .oddDoubleBondCumulene descriptor

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93AuthorityVonBaeyerSystem.MechanicallyValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93VonBaeyerCenterAuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93VonBaeyerBridgeOrientationAuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93VonBaeyerBridgeheadRelativeAuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93VonBaeyerUnsaturationAuthorityObservation.ValidFor
