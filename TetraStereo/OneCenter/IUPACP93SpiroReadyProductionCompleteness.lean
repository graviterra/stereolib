import TetraStereo.OneCenter.IUPACRemaining71P93SpiroReviewedSemantics

set_option autoImplicit false

/-!
# Source/core production completeness for four spiro P-93 rows

This module factors the reviewed `Xabcd`, `Xabab`, double-bond, and axial spiro judgments into
explicit source evidence and finite descriptor cores.  Production never invokes an observation
`ValidFor` definition or a reference `Judges` field.  Mechanical spiro-system evidence, atom or
bond evidence, policy observations, authorizations, and citation nonemptiness are all visible in
the producer relations.

This is deliberately a **source/core factorization**, not a transport theorem from the deeper
`SpiroConfiguration` analyzer.  The authority carrier's descriptor and evidence types differ from
the analyzer's types; identifying them requires a separate, scientifically meaningful refinement
map.  The policy and raw source evidence below therefore remain caller-supplied audited boundaries.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic

/-- The four spiro rows whose reviewed judgments admit a direct source/core factorization. -/
inductive Remaining71P93SpiroReadyAuthorityRow where
  | spiroXabcd
  | spiroXabab
  | spiroDoubleBonds
  | spiroAxialChirality
  deriving DecidableEq, Repr

namespace Remaining71P93SpiroReadyAuthorityRow

def all : List Remaining71P93SpiroReadyAuthorityRow :=
  [ .spiroXabcd
  , .spiroXabab
  , .spiroDoubleBonds
  , .spiroAxialChirality
  ]

def toAuthorityRow : Remaining71P93SpiroReadyAuthorityRow →
    Remaining71P93SpiroAuthorityRow
  | .spiroXabcd => .spiroXabcd
  | .spiroXabab => .spiroXabab
  | .spiroDoubleBonds => .spiroDoubleBonds
  | .spiroAxialChirality => .spiroAxialChirality

def provision (row : Remaining71P93SpiroReadyAuthorityRow) :
    IUPACNormativeProvision :=
  row.toAuthorityRow.provision

def reference
    (policy : P93SpiroAuthorityPolicy)
    (row : Remaining71P93SpiroReadyAuthorityRow) : ProvisionReference :=
  row.toAuthorityRow.reference policy

def provisions : List IUPACNormativeProvision :=
  all.map provision

@[simp] theorem all_length : all.length = 4 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem provisions_length : provisions.length = 4 := by
  rfl

@[simp] theorem provisions_exact :
    provisions =
      [ .p93SpiroXabcd
      , .p93SpiroXabab
      , .p93SpiroDoubleBonds
      , .p93SpiroAxialChirality
      ] := by
  rfl

end Remaining71P93SpiroReadyAuthorityRow

/-! ## Explicit source envelopes -/

/-- Mechanical and audited source evidence for the shared spiro system. -/
def P93SpiroSystemSourceEnvelope
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) : Prop :=
  system.MechanicallyValidFor source ∧
    policy.SystemObserved source system

/-- Fully expanded physical evidence for the spiro atom center. -/
def P93SpiroAtomCenterSourceEnvelope
    (source : AuthoritativeChemicalInput)
    (center : Nat) : Prop :=
  center < source.molecule.atomCount ∧
    ∃ neighbors : List Nat,
      3 ≤ neighbors.length ∧ neighbors.Nodup ∧
        P93AuthorityAtomsBounded source neighbors ∧
        ∀ neighbor ∈ neighbors,
          P93AuthorityBinaryBond source center neighbor ∨
            P93AuthorityMulticenterIncidence source center neighbor

/-- Fully expanded physical evidence that a carrier unit is an ordered binary bond. -/
def P93SpiroDoubleBondUnitSourceEnvelope
    (source : AuthoritativeChemicalInput)
    (unit : P93AuthorityPhysicalUnit) : Prop :=
  ∃ first second,
    unit = .bond first second ∧
      first < source.molecule.atomCount ∧
      second < source.molecule.atomCount ∧
      first < second ∧
      P93AuthorityBinaryBond source first second

theorem p93SpiroSystem_validFor_iff_sourceEnvelope
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) :
    system.ValidFor policy source ↔
      P93SpiroSystemSourceEnvelope policy source system := by
  rfl

theorem p93SpiroAtomCenter_validFor_iff_sourceEnvelope
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (center : Nat) :
    (P93AuthorityPhysicalUnit.atomCenter center).ValidFor
        policy.physicalObservation source ↔
      P93SpiroAtomCenterSourceEnvelope source center := by
  rfl

theorem p93SpiroDoubleBondUnit_validFor_iff_sourceEnvelope
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (unit : P93AuthorityPhysicalUnit) :
    P93SpiroDoubleBondUnitSourceEnvelope source unit ↔
      unit.ValidFor policy.physicalObservation source ∧
        ∃ first second, unit = .bond first second := by
  constructor
  · rintro ⟨first, second, rfl, firstBound, secondBound, ordered, bonded⟩
    exact ⟨⟨firstBound, secondBound, ordered, bonded⟩, ⟨first, second, rfl⟩⟩
  · rintro ⟨valid, first, second, unitEq⟩
    subst unit
    exact ⟨first, second, rfl, valid⟩

/-! ## Finite descriptor facts omitted from the producer cores -/

theorem spiroXabcd_centerRS_supported :
    SpiroFamilySupported .Xabcd .centerRS := by
  trivial

theorem spiroXabab_family_supported_of_center_family
    (family : SpiroDescriptorFamily)
    (centerFamily : family = .centerRS ∨ family = .centerRrSs) :
    SpiroFamilySupported .Xabab family := by
  rcases centerFamily with rfl | rfl <;> trivial

theorem spiroXaabb_centerRS_supported :
    SpiroFamilySupported .Xaabb .centerRS := by
  trivial

theorem spiroXaabb_axialMP_supported :
    SpiroFamilySupported .Xaabb .axialMP := by
  trivial

theorem spiro_centerRS_descriptor_recommended
    (descriptor : Descriptor)
    (descriptorMatches : P93SpiroCenterDescriptorMatchesFamily .centerRS descriptor) :
    DescriptorRecommended .preferredIUPACName .chiralCenter descriptor := by
  cases descriptor <;>
    simp_all [P93SpiroCenterDescriptorMatchesFamily, DescriptorRecommended]

/-! ## Row-specific source/core relations -/

def P93SpiroXabcdSourceCore
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroXabcdAuthorityObservation policy) : Prop :=
  P93SpiroSystemSourceEnvelope policy source observation.system ∧
    P93SpiroAtomCenterSourceEnvelope source observation.system.center ∧
    policy.UnitInSystemObserved source observation.system
      (.atomCenter observation.system.center) ∧
    policy.SpiroPatternObserved source observation.system .Xabcd ∧
    P93SpiroCenterDescriptorMatchesFamily .centerRS observation.descriptor ∧
    policy.CenterDescriptorAuthorized source observation.system
      .Xabcd .centerRS observation.descriptor ∧
    observation.citation.components ≠ [] ∧
    policy.CitationAuthorized source observation.citation
      (.atomCenter observation.system.center)

def P93SpiroXababSourceCore
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroXababAuthorityObservation policy) : Prop :=
  P93SpiroSystemSourceEnvelope policy source observation.system ∧
    P93SpiroAtomCenterSourceEnvelope source observation.system.center ∧
    policy.UnitInSystemObserved source observation.system
      (.atomCenter observation.system.center) ∧
    policy.SpiroPatternObserved source observation.system .Xabab ∧
    (observation.family = .centerRS ∨ observation.family = .centerRrSs) ∧
    ValidXababOccurrenceOrder observation.occurrenceOrder ∧
    policy.XababOccurrenceOrderObserved source observation.system
      observation.occurrenceOrder ∧
    P93SpiroCenterDescriptorMatchesFamily observation.family observation.descriptor ∧
    policy.CenterDescriptorAuthorized source observation.system
      .Xabab observation.family observation.descriptor ∧
    observation.citation.components ≠ [] ∧
    policy.CitationAuthorized source observation.citation
      (.atomCenter observation.system.center)

def P93SpiroDoubleBondSourceCore
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroDoubleBondAuthorityObservation policy) : Prop :=
  P93SpiroSystemSourceEnvelope policy source observation.system ∧
    P93SpiroDoubleBondUnitSourceEnvelope source observation.unit ∧
    P93SpiroUnitSupported observation.system observation.unit ∧
    (∃ first second, observation.unit = .bond first second ∧
      first ∈ observation.ring ∧ second ∈ observation.ring) ∧
    P93SpiroRingBelongsToSystem observation.system observation.ring ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    policy.DoubleBondRingObserved source observation.system observation.unit
      observation.ring ∧
    policy.DoubleBondGeometryObserved source observation.unit observation.geometry ∧
    policy.DoubleBondNamingAuthorized source observation.system observation.unit
      observation.context observation.descriptor? ∧
    P93SpiroGeneralDoubleBondDescriptorAllowed observation.descriptor? ∧
    (observation.context = .preferredIUPACName →
      observation.descriptor? =
        P93SpiroDoubleBondExpected observation.ring.length observation.geometry) ∧
    observation.citation.components ≠ [] ∧
    policy.CitationAuthorized source observation.citation observation.unit

def P93SpiroAxialSourceCore
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroAxialAuthorityObservation policy) : Prop :=
  P93SpiroSystemSourceEnvelope policy source observation.system ∧
    P93SpiroAtomCenterSourceEnvelope source observation.system.center ∧
    policy.UnitInSystemObserved source observation.system
      (.atomCenter observation.system.center) ∧
    policy.SpiroPatternObserved source observation.system .Xaabb ∧
    P93SpiroCenterDescriptorMatchesFamily .centerRS observation.centerDescriptor ∧
    P93SpiroCenterDescriptorMatchesFamily .axialMP observation.axialDescriptor ∧
    P93SpiroCenterAxialCorrespondence observation.centerDescriptor
      observation.axialDescriptor ∧
    policy.AxialCenterDescriptorAuthorized source observation.system
      observation.centerDescriptor ∧
    policy.AxialDescriptorAuthorized source observation.system
      observation.axialDescriptor ∧
    observation.citation.components ≠ [] ∧
    policy.CitationAuthorized source observation.citation
      (.atomCenter observation.system.center)

/-! ## Exact source/core factorization -/

theorem p93SpiroXabcd_sourceCore_iff_validFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroXabcdAuthorityObservation policy) :
    P93SpiroXabcdSourceCore policy source observation ↔
      observation.ValidFor policy source := by
  rw [P93SpiroXabcdAuthorityObservation.ValidFor]
  constructor
  · rintro ⟨system, center, inSystem, pattern, descriptorMatches, authorized,
      citation, citationAuthorized⟩
    exact ⟨
      (p93SpiroSystem_validFor_iff_sourceEnvelope policy source observation.system).2 system,
      (p93SpiroAtomCenter_validFor_iff_sourceEnvelope policy source
        observation.system.center).2 center,
      inSystem, pattern, spiroXabcd_centerRS_supported, descriptorMatches, authorized,
      citation, citationAuthorized⟩
  · rintro ⟨system, center, inSystem, pattern, _supported, descriptorMatches, authorized,
      citation, citationAuthorized⟩
    exact ⟨
      (p93SpiroSystem_validFor_iff_sourceEnvelope policy source observation.system).1 system,
      (p93SpiroAtomCenter_validFor_iff_sourceEnvelope policy source
        observation.system.center).1 center,
      inSystem, pattern, descriptorMatches, authorized, citation, citationAuthorized⟩

theorem p93SpiroXabab_sourceCore_iff_validFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroXababAuthorityObservation policy) :
    P93SpiroXababSourceCore policy source observation ↔
      observation.ValidFor policy source := by
  rw [P93SpiroXababAuthorityObservation.ValidFor]
  constructor
  · rintro ⟨system, center, inSystem, pattern, centerFamily, order,
      orderObserved, descriptorMatches, authorized, citation, citationAuthorized⟩
    exact ⟨
      (p93SpiroSystem_validFor_iff_sourceEnvelope policy source observation.system).2 system,
      (p93SpiroAtomCenter_validFor_iff_sourceEnvelope policy source
        observation.system.center).2 center,
      inSystem, pattern,
      spiroXabab_family_supported_of_center_family observation.family centerFamily,
      centerFamily, order, orderObserved, descriptorMatches, authorized, citation,
      citationAuthorized⟩
  · rintro ⟨system, center, inSystem, pattern, _supported, centerFamily, order,
      orderObserved, descriptorMatches, authorized, citation, citationAuthorized⟩
    exact ⟨
      (p93SpiroSystem_validFor_iff_sourceEnvelope policy source observation.system).1 system,
      (p93SpiroAtomCenter_validFor_iff_sourceEnvelope policy source
        observation.system.center).1 center,
      inSystem, pattern, centerFamily, order, orderObserved, descriptorMatches, authorized,
      citation, citationAuthorized⟩

theorem p93SpiroDoubleBond_sourceCore_iff_validFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroDoubleBondAuthorityObservation policy) :
    P93SpiroDoubleBondSourceCore policy source observation ↔
      observation.ValidFor policy source := by
  rw [P93SpiroDoubleBondAuthorityObservation.ValidFor]
  constructor
  · rintro ⟨system, unit, supported, inRing, belongs, inSystem, ringObserved,
      geometryObserved, namingAuthorized, descriptorAllowed, preferred,
      citation, citationAuthorized⟩
    have unitValidAndBond :=
      (p93SpiroDoubleBondUnit_validFor_iff_sourceEnvelope
        policy source observation.unit).1 unit
    exact ⟨
      (p93SpiroSystem_validFor_iff_sourceEnvelope policy source observation.system).2 system,
      unitValidAndBond.1, supported, inRing, belongs, inSystem, ringObserved,
      geometryObserved, namingAuthorized, descriptorAllowed, preferred,
      citation, citationAuthorized⟩
  · rintro ⟨system, unitValid, supported, inRing, belongs, inSystem, ringObserved,
      geometryObserved, namingAuthorized, descriptorAllowed, preferred,
      citation, citationAuthorized⟩
    rcases inRing with ⟨first, second, unitEq, firstIn, secondIn⟩
    have unitEnvelope : P93SpiroDoubleBondUnitSourceEnvelope source observation.unit :=
      (p93SpiroDoubleBondUnit_validFor_iff_sourceEnvelope
        policy source observation.unit).2
          ⟨unitValid, ⟨first, second, unitEq⟩⟩
    exact ⟨
      (p93SpiroSystem_validFor_iff_sourceEnvelope policy source observation.system).1 system,
      unitEnvelope, supported, ⟨first, second, unitEq, firstIn, secondIn⟩,
      belongs, inSystem, ringObserved, geometryObserved, namingAuthorized,
      descriptorAllowed, preferred, citation, citationAuthorized⟩

theorem p93SpiroAxial_sourceCore_iff_validFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroAxialAuthorityObservation policy) :
    P93SpiroAxialSourceCore policy source observation ↔
      observation.ValidFor policy source := by
  rw [P93SpiroAxialAuthorityObservation.ValidFor]
  constructor
  · rintro ⟨system, center, inSystem, pattern, centerMatches, axialMatches,
      correspondence, centerAuthorized, axialAuthorized, citation, citationAuthorized⟩
    exact ⟨
      (p93SpiroSystem_validFor_iff_sourceEnvelope policy source observation.system).2 system,
      (p93SpiroAtomCenter_validFor_iff_sourceEnvelope policy source
        observation.system.center).2 center,
      inSystem, pattern, spiroXaabb_centerRS_supported, spiroXaabb_axialMP_supported,
      centerMatches, axialMatches, correspondence, centerAuthorized, axialAuthorized,
      spiro_centerRS_descriptor_recommended observation.centerDescriptor centerMatches,
      citation, citationAuthorized⟩
  · rintro ⟨system, center, inSystem, pattern, _centerSupported, _axialSupported,
      centerMatches, axialMatches, correspondence, centerAuthorized, axialAuthorized,
      _recommended, citation, citationAuthorized⟩
    exact ⟨
      (p93SpiroSystem_validFor_iff_sourceEnvelope policy source observation.system).1 system,
      (p93SpiroAtomCenter_validFor_iff_sourceEnvelope policy source
        observation.system.center).1 center,
      inSystem, pattern, centerMatches, axialMatches, correspondence, centerAuthorized,
      axialAuthorized, citation, citationAuthorized⟩

namespace Remaining71P93SpiroReadyAuthorityRow

/-- Source/core producer family; no branch invokes a reviewed carrier predicate. -/
def ProductionJudges
    (policy : P93SpiroAuthorityPolicy) :
    (row : Remaining71P93SpiroReadyAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .spiroXabcd, source, observation =>
      P93SpiroXabcdSourceCore policy source observation
  | .spiroXabab, source, observation =>
      P93SpiroXababSourceCore policy source observation
  | .spiroDoubleBonds, source, observation =>
      P93SpiroDoubleBondSourceCore policy source observation
  | .spiroAxialChirality, source, observation =>
      P93SpiroAxialSourceCore policy source observation

/-- Every row's explicit producer is extensionally the independent reviewed judgment. -/
theorem production_eq_reference
    (policy : P93SpiroAuthorityPolicy)
    (row : Remaining71P93SpiroReadyAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row with
  | spiroXabcd =>
      exact p93SpiroXabcd_sourceCore_iff_validFor policy source observation
  | spiroXabab =>
      exact p93SpiroXabab_sourceCore_iff_validFor policy source observation
  | spiroDoubleBonds =>
      exact p93SpiroDoubleBond_sourceCore_iff_validFor policy source observation
  | spiroAxialChirality =>
      exact p93SpiroAxial_sourceCore_iff_validFor policy source observation

theorem reference_applicable_of_judged
    (policy : P93SpiroAuthorityPolicy)
    (row : Remaining71P93SpiroReadyAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row <;> exact ⟨observation, judged⟩

end Remaining71P93SpiroReadyAuthorityRow

/-! ## Residual nontetrahedral spiro row -/

def P93SpiroPhysicalUnitSourceEnvelope
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
          policy.PolyhedralQualitativeFrameObserved
            source center positions geometry frame

theorem p93SpiroPhysicalUnit_sourceEnvelope_iff_validFor
    (policy : P93AuthorityPhysicalObservationPolicy)
    (source : AuthoritativeChemicalInput)
    (unit : P93AuthorityPhysicalUnit) :
    P93SpiroPhysicalUnitSourceEnvelope policy source unit ↔
      unit.ValidFor policy source := by
  cases unit <;> rfl

def P93SpiroNontetrahedralSourceCore
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroPolyhedralAuthorityObservation policy) : Prop :=
  P93SpiroSystemSourceEnvelope policy source observation.system ∧
    P93SpiroPhysicalUnitSourceEnvelope policy.physicalObservation source observation.unit ∧
    P93SpiroUnitSupported observation.system observation.unit ∧
    (∃ positions,
      observation.unit = .polyhedron observation.system.center positions ∧
        policy.CoordinationObserved source observation.system positions
          observation.coordination ∧
        policy.PolyhedralDescriptorAuthorized source observation.system positions
          observation.knowledge observation.descriptor) ∧
    BlueBookP93.Cyclic.PolyhedralACApplicable observation.coordination ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit

theorem p93SpiroNontetrahedral_sourceCore_iff_validFor
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93SpiroPolyhedralAuthorityObservation policy) :
    P93SpiroNontetrahedralSourceCore policy source observation ↔
      observation.ValidFor policy source := by
  rw [P93SpiroPolyhedralAuthorityObservation.ValidFor,
    p93SpiroSystem_validFor_iff_sourceEnvelope,
    ← p93SpiroPhysicalUnit_sourceEnvelope_iff_validFor]
  rfl

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93SpiroReadyAuthorityRow.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93SpiroDoubleBondUnit_validFor_iff_sourceEnvelope
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.spiro_centerRS_descriptor_recommended
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93SpiroReadyAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93SpiroReadyAuthorityRow.reference_applicable_of_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93SpiroNontetrahedral_sourceCore_iff_validFor
