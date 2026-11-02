import TetraStereo.OneCenter.IUPACRemaining71P93VonBaeyerReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for all four von Baeyer P-93 provisions

The family producer exposes the graph-derived bridge system, physical-unit source evidence,
relative-side rules, and ordinary/cumulene descriptor calculations directly.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93
open BlueBookP93.Cyclic

def P93VonBaeyerSystemSourceCore
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityVonBaeyerSystem) : Prop :=
  system.MechanicallyValidFor source ∧ policy.SystemObserved source system

def P93VonBaeyerPhysicalUnitSourceCore
    (policy : P93AuthorityPhysicalObservationPolicy)
    (source : AuthoritativeChemicalInput) : P93AuthorityPhysicalUnit → Prop
  | .atomCenter center =>
      center < source.molecule.atomCount ∧
        ∃ neighbors : List Nat,
          3 ≤ neighbors.length ∧ neighbors.Nodup ∧
            P93AuthorityAtomsBounded source neighbors ∧
            ∀ neighbor ∈ neighbors,
              P93AuthorityBinaryBond source center neighbor ∨
                P93AuthorityMulticenterIncidence source center neighbor
  | .bond first second =>
      first < source.molecule.atomCount ∧ second < source.molecule.atomCount ∧
        first < second ∧ P93AuthorityBinaryBond source first second
  | .axis path => P93AuthorityCanonicalCumuleneAxisPerceived source path
  | .plane members =>
      ∃ frame : P93AuthorityPlaneFrame,
        frame.ValidFor source members ∧
          policy.PlanarRestrictionAndAsymmetryObserved source members frame
  | .helix path =>
      ∃ frame : P93AuthorityHelixFrame,
        frame.ValidFor source path ∧ policy.HelixIdentified source path frame
  | .polyhedron center positions =>
      ∃ geometry frame,
        P93AuthorityPolyhedralFrame.ValidFor source center positions geometry frame ∧
          policy.PolyhedralQualitativeFrameObserved source center positions geometry frame

def P93VonBaeyerCenterSourceCore
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerCenterAuthorityObservation policy) : Prop :=
  P93VonBaeyerSystemSourceCore policy source observation.system ∧
    P93VonBaeyerPhysicalUnitSourceCore policy.physicalObservation source observation.unit ∧
    P93VonBaeyerUnitSupported observation.system observation.unit ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    (∃ center, observation.unit = .atomCenter center ∧
      policy.CenterKindObserved source center observation.kind ∧
      policy.CenterDescriptorAuthorized source center observation.descriptor ∧
      policy.CenterConfigurationKnowledgeObserved source center observation.knowledge ∧
      policy.CenterNotationObserved source center observation.knowledge observation.notation) ∧
    (observation.kind = .chiralCenter ∨ observation.kind = .pseudoasymmetricCenter) ∧
    BlueBookP93.Acyclic.DescriptorApplies observation.kind observation.descriptor ∧
    observation.notation = PreferredMonocycleNotation observation.knowledge ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit

def P93VonBaeyerBridgeOrientationSourceCore
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy) : Prop :=
  P93VonBaeyerSystemSourceCore policy source observation.system ∧
    EndoExoSynAntiApplicable observation.system.dimensions ∧
    observation.attachmentAtom ∈ observation.system.atoms ∧
    observation.substituent ∉ observation.system.atoms ∧
    P93AuthorityBinaryBond source observation.attachmentAtom observation.substituent ∧
    P93VonBaeyerPhysicalUnitSourceCore policy.physicalObservation source
      (.atomCenter observation.attachmentAtom) ∧
    policy.UnitInSystemObserved source observation.system
      (.atomCenter observation.attachmentAtom) ∧
    policy.BridgeAttachmentObserved source observation.system observation.attachmentAtom
      observation.substituent observation.attachment ∧
    observation.descriptor = bridgeDescriptor observation.attachment ∧
    ¬BridgeDescriptorDeterminesAbsolute observation.descriptor ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation
      (.atomCenter observation.attachmentAtom)

def P93VonBaeyerBridgeheadRelativeSourceCore
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy) : Prop :=
  P93VonBaeyerSystemSourceCore policy source observation.system ∧
    observation.firstLigand ≠ observation.secondLigand ∧
    observation.firstLigand ∉ observation.system.atoms ∧
    observation.secondLigand ∉ observation.system.atoms ∧
    P93AuthorityBinaryBond source observation.system.firstBridgehead observation.firstLigand ∧
    P93AuthorityBinaryBond source observation.system.secondBridgehead observation.secondLigand ∧
    policy.BridgeheadLigandSideObserved source observation.system
      observation.system.firstBridgehead observation.firstLigand observation.firstSide ∧
    policy.BridgeheadLigandSideObserved source observation.system
      observation.system.secondBridgehead observation.secondLigand observation.secondSide ∧
    RelativeRingSide observation.firstSide observation.secondSide observation.descriptor ∧
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

def P93VonBaeyerUnsaturationSourceCore
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerUnsaturationAuthorityObservation policy) : Prop :=
  P93VonBaeyerSystemSourceCore policy source observation.system ∧
    P93VonBaeyerPhysicalUnitSourceCore policy.physicalObservation source observation.unit ∧
    P93VonBaeyerUnitSupported observation.system observation.unit ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit ∧
    match observation.specification with
    | .ordinaryDoubleBond contextIsPIN largerThanBicyclo333 geometry descriptor? =>
        (∃ first second, observation.unit = .bond first second) ∧
          policy.LargerThanBicyclo333Observed source observation.system largerThanBicyclo333 ∧
          policy.SeniorLigandGeometryObserved source observation.unit geometry ∧
          policy.OrdinaryDoubleBondNamingAuthorized source observation.system observation.unit
            contextIsPIN largerThanBicyclo333 descriptor? ∧
          P93VonBaeyerOrdinaryDescriptorAllowed descriptor? ∧
          (contextIsPIN = true → descriptor? =
            P93VonBaeyerOrdinaryDoubleBondExpected largerThanBicyclo333 geometry)
    | .includedOpenCumulene context parity descriptor =>
        (∃ path, observation.unit = .axis path ∧
          policy.IncludedCumuleneNumberingObserved source observation.system
            path observation.citation) ∧
          policy.IncludedCumuleneNamingContextObserved source observation.system
            observation.unit context ∧
          OpenTerminalCumuleneDescriptorApplies .includedOpenCumuleneSegment parity descriptor ∧
          match parity with
          | .even => BlueBookP93.Acyclic.DescriptorRecommended context
              .evenDoubleBondCumulene descriptor
          | .odd => BlueBookP93.Acyclic.DescriptorRecommended context
              .oddDoubleBondCumulene descriptor

namespace Remaining71P93VonBaeyerAuthorityRow

def ProductionJudges
    (policy : P93VonBaeyerAuthorityPolicy) :
    (row : Remaining71P93VonBaeyerAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .vonBaeyerCIPCenters, source, observation =>
      P93VonBaeyerCenterSourceCore policy source observation ∧
        observation.knowledge = .absolute
  | .vonBaeyerEndoExoSynAnti, source, observation =>
      P93VonBaeyerBridgeOrientationSourceCore policy source observation
  | .vonBaeyerCisTrans, source, observation =>
      P93VonBaeyerBridgeheadRelativeSourceCore policy source observation
  | .vonBaeyerDoubleBonds, source, observation =>
      P93VonBaeyerUnsaturationSourceCore policy source observation

theorem production_eq_reference
    (policy : P93VonBaeyerAuthorityPolicy)
    (row : Remaining71P93VonBaeyerAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row <;> rfl

theorem reference_applicable_of_judged
    (policy : P93VonBaeyerAuthorityPolicy)
    (row : Remaining71P93VonBaeyerAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row <;> exact ⟨observation, judged⟩

end Remaining71P93VonBaeyerAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93VonBaeyerAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93VonBaeyerAuthorityRow.reference_applicable_of_judged
