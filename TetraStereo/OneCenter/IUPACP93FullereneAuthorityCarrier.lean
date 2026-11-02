import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93MolecularFullereneThreeLocantGeometry

set_option autoImplicit false

/-!
# Authority carrier for the six P-93.5.6 fullerene rows

The carrier deliberately keeps the audited source boundary separate from the executable
fullerene reference program.  Cage identity is proved on a raw molecular graph; the three
chirality tests are derived from its oriented face-map symmetries; and `f,xC`/`f,xA` is derived
from a source-selected numbering and exact exterior-view geometry.

Type 4 and the P-93.5.6.6 superimposition rule do not trust the legacy
`everyChiralSubstituentHasCIP` Boolean by itself.  They require a duplicate-free, all-and-only
corpus of source-authorized physical stereogenic units and their actual CIP descriptors.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

/-- The printed P-93.5.6 methodology is the complete four-way decision rule itself, not a
molecule-specific coordinate observation. -/
def P93FullereneFourWaySubstitutionDecisionRule : Prop :=
  ∀ test chiralityType,
    fullereneChiralityType? test = some chiralityType ↔
      FullereneTypeMatches test chiralityType

theorem p93FullereneFourWaySubstitutionDecisionRule :
    P93FullereneFourWaySubstitutionDecisionRule :=
  fullereneChiralityType?_eq_some_iff

/-- Descriptor vocabularies that can occur on a chiral fullerene substituent. -/
inductive P93FullereneSubstituentCIPDescriptor where
  | center (descriptor : BlueBookP92.CenterDescriptor)
  | axis (descriptor : BlueBookP92.AxialDescriptor)
  | plane (descriptor : BlueBookP92.PlanarDescriptor)
  | helix (descriptor : BlueBookP92.Helicity)
  | doubleBond (descriptor : BlueBookP92.EnantiomorphicDoubleBondDescriptor)
  | polyhedron (descriptor : PolyhedralDescriptor)
  deriving DecidableEq, Repr

/-- Typed stereogenic units that may occur inside a fullerene substituent.  `bondAxis` keeps
atropisomeric and other bond axes distinct from perceived cumulene axes; both remain genuine
source bonds, but only the latter uses the molecule-wide cumulene perception judgment. -/
inductive P93FullereneSubstituentStereogenicUnit where
  | center (atom : Nat)
  | doubleBond (first second : Nat)
  | cumuleneAxis (path : List Nat)
  | bondAxis (first second : Nat)
  | plane (members : Finset Nat)
  | helix (path : List Nat)
  | polyhedron (center : Nat) (positions : Finset Nat)
  deriving DecidableEq

def P93FullereneSubstituentStereogenicUnit.toPhysicalUnit :
    P93FullereneSubstituentStereogenicUnit → P93AuthorityPhysicalUnit
  | P93FullereneSubstituentStereogenicUnit.center atom => .atomCenter atom
  | P93FullereneSubstituentStereogenicUnit.doubleBond first second =>
      .bond first second
  | P93FullereneSubstituentStereogenicUnit.cumuleneAxis path => .axis path
  | P93FullereneSubstituentStereogenicUnit.bondAxis first second =>
      .bond first second
  | P93FullereneSubstituentStereogenicUnit.plane members => .plane members
  | P93FullereneSubstituentStereogenicUnit.helix path => .helix path
  | P93FullereneSubstituentStereogenicUnit.polyhedron centerAtom positions =>
      .polyhedron centerAtom positions

/-- Descriptor vocabulary and physical stereogenic-unit family agree by construction. -/
def P93FullereneSubstituentDescriptorMatchesUnit :
    P93FullereneSubstituentCIPDescriptor →
      P93FullereneSubstituentStereogenicUnit → Prop
  | P93FullereneSubstituentCIPDescriptor.center _,
      P93FullereneSubstituentStereogenicUnit.center _
  | .axis _, .cumuleneAxis _
  | .axis _, .bondAxis _ _
  | .plane _, .plane _
  | .helix _, .helix _
  | .doubleBond _, .doubleBond _ _
  | .polyhedron _, .polyhedron _ _ => True
  | _, _ => False

/-- One site-indexed substituent stereogenic unit, its nomenclature citation, and its CIP result. -/
structure P93FullereneSubstituentCIPAssignment where
  substitutedSite : Nat
  unit : P93FullereneSubstituentStereogenicUnit
  citation : P93AuthorityCitationToken
  descriptor : P93FullereneSubstituentCIPDescriptor
  deriving DecidableEq

/-- Audited relations that connect an authoritative chemical input to the independent molecular
fullerene program.  These relations carry observations that constitution and exact coordinates
alone cannot derive: the raw-graph transcription, original-derivative chirality, preferred
numbering, and molecule-specific substituent/citation authorization. -/
structure P93FullereneAuthorityPolicy where
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  MethodologyRuleObserved : AuthoritativeChemicalInput → Prop
  RawMoleculeObserved :
    AuthoritativeChemicalInput → RawMolecule → Prop
  InputFamilyObserved :
    AuthoritativeChemicalInput → RawMolecule →
      List SpatiallyDerivedMolecularFullereneConfigurationInput → Prop
  SubstitutionEvidenceObserved :
    AuthoritativeChemicalInput → RawMolecule →
      MolecularFullereneConfigurationInput →
      MolecularFullereneSubstitutionEvidence → Prop
  PreferredNumberingSelected :
    AuthoritativeChemicalInput → MolecularFullereneConfigurationInput →
      MolecularFullereneNumberingEvidence → Prop
  OriginalDerivativeChiralityObserved :
    AuthoritativeChemicalInput → MolecularFullereneConfigurationInput → Bool → Prop
  /-- A printed `f,xC/A` assignment is closed provenance.  The executable observation must still
  derive the same handedness from its exact numbering and turn geometry. -/
  PrintedCageHandednessObserved :
    AuthoritativeChemicalInput → RawMolecule → MolecularFullereneConfigurationInput →
      FullereneNumberingKind → FullereneHandedness → Prop
  SubstituentUnitAtSiteEligible :
    AuthoritativeChemicalInput → RawMolecule →
      MolecularFullereneConfigurationInput →
      MolecularFullereneSubstitutionEvidence → Nat →
      P93FullereneSubstituentStereogenicUnit → Prop
  SubstituentCitationAuthorized :
    AuthoritativeChemicalInput → MolecularFullereneConfigurationInput → Nat →
      P93AuthorityCitationToken → P93FullereneSubstituentStereogenicUnit → Prop
  SubstituentDescriptorAuthorized :
    AuthoritativeChemicalInput → MolecularFullereneConfigurationInput → Nat →
      P93FullereneSubstituentStereogenicUnit →
        P93FullereneSubstituentCIPDescriptor → Prop

/-- Every strict input record is bound to the source observation and to the preferred systematic
or trivial numbering selected by the applicable nomenclature authority. -/
def P93FullereneStrictInputSourceBound
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule)
    (input : SpatiallyDerivedMolecularFullereneConfigurationInput) : Prop :=
  policy.SubstitutionEvidenceObserved source molecule input.symmetryInput.cage
      input.symmetryInput.substitutionEvidence ∧
    policy.PreferredNumberingSelected source input.symmetryInput.cage
      input.numberingEvidence ∧
    policy.OriginalDerivativeChiralityObserved source input.symmetryInput.cage
      input.symmetryInput.substitutionEvidence.originalDerivativeChiral

/-- One substituent CIP assignment is physically valid and authorized for this exact fullerene
unit. -/
def P93FullereneSubstituentCIPAssignment.ValidFor
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence)
    (assignment : P93FullereneSubstituentCIPAssignment) : Prop :=
  assignment.substitutedSite ∈ evidence.chiralSubstituentSites ∧
    assignment.unit.toPhysicalUnit.ValidFor policy.physicalObservation source ∧
    policy.SubstituentUnitAtSiteEligible source molecule input evidence
      assignment.substitutedSite assignment.unit ∧
    P93FullereneSubstituentDescriptorMatchesUnit
      assignment.descriptor assignment.unit ∧
    assignment.citation.Valid ∧
    policy.SubstituentCitationAuthorized source input assignment.substitutedSite
      assignment.citation assignment.unit ∧
    policy.SubstituentDescriptorAuthorized source input assignment.substitutedSite
      assignment.unit assignment.descriptor

/-- Exact corpus condition for chiral substituents: no duplicate physical unit or citation,
every carried assignment is valid, and every eligible unit appears. -/
def P93FullereneSubstituentCIPAssignmentsComplete
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence)
    (assignments : List P93FullereneSubstituentCIPAssignment) : Prop :=
  assignments ≠ [] ∧
    (assignments.map fun assignment =>
      (assignment.substitutedSite, assignment.unit)).Nodup ∧
    (assignments.map fun assignment => assignment.unit.toPhysicalUnit).Nodup ∧
    (assignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ assignments,
      assignment.ValidFor policy source molecule input evidence) ∧
    (∀ site ∈ evidence.chiralSubstituentSites,
      ∃ assignment ∈ assignments, assignment.substitutedSite = site) ∧
    ∀ site ∈ evidence.chiralSubstituentSites, ∀ unit,
      policy.SubstituentUnitAtSiteEligible source molecule input evidence site unit →
        ∃ assignment ∈ assignments,
          assignment.substitutedSite = site ∧ assignment.unit = unit

/-- Complete molecule-bound observation used by the general and four class-specific rows.

The strict assignment judgment provides cage validation, oriented-symmetry classification,
coordinate-derived cage handedness, and same-cage conflict agreement.  The final implication
upgrades Type 4's Boolean payload to an independently enumerated CIP corpus. -/
structure P93FullereneAuthorityObservation
    (policy : P93FullereneAuthorityPolicy) where
  molecule : RawMolecule
  spatial : SpatialConfiguration
  inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput
  selectedInput : SpatiallyDerivedMolecularFullereneConfigurationInput
  assignment : FullereneConfigurationAssignment
  substituentAssignments : List P93FullereneSubstituentCIPAssignment

def P93FullereneAuthorityObservation.ValidFor
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93FullereneAuthorityObservation policy) : Prop :=
  source.spatial? = some observation.spatial ∧
    policy.RawMoleculeObserved source observation.molecule ∧
    observation.inputs ≠ [] ∧
    policy.InputFamilyObserved source observation.molecule observation.inputs ∧
    observation.selectedInput ∈ observation.inputs ∧
    (∀ input ∈ observation.inputs,
      P93FullereneStrictInputSourceBound
        policy source observation.molecule input) ∧
    SpatiallyDerivedMolecularFullereneConfigurationInputJudgment
      observation.molecule observation.spatial observation.selectedInput ∧
    FullereneConfigurationAssignmentJudgment
      observation.selectedInput.symmetryInput.cage.toFullereneConfigurationInput
      observation.assignment ∧
    SpatiallyDerivedMolecularFullereneConfigurationAssignmentJudgment
      observation.molecule observation.spatial observation.inputs
      observation.assignment ∧
    (observation.assignment.chiralityType = .chiralSubstituentsOnly →
      P93FullereneSubstituentCIPAssignmentsComplete policy source
        observation.molecule observation.selectedInput.symmetryInput.cage
        observation.selectedInput.symmetryInput.substitutionEvidence
        observation.substituentAssignments)

/-- Types 1--3 retain a printed numbering/handedness claim in addition to the independently
derived spatial assignment.  Agreement is literal membership in the computed payload. -/
def P93FullereneAuthorityObservation.CageHandednessValidFor
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93FullereneAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    ∃ numberingKind handedness,
      FullereneDescriptorPayload.cageHandedness numberingKind handedness ∈
        observation.assignment.payloads ∧
      policy.PrintedCageHandednessObserved source observation.molecule
        observation.selectedInput.symmetryInput.cage numberingKind handedness

/-- The general-methodology row carries only the printed four-way decision rule. -/
inductive P93FullereneMethodologyAuthorityObservation where
  | fourWayDecisionRule

def P93FullereneMethodologyAuthorityObservation.ValidFor
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (_observation : P93FullereneMethodologyAuthorityObservation) : Prop :=
  policy.MethodologyRuleObserved source ∧ P93FullereneFourWaySubstitutionDecisionRule

/-- Type 4 has no cage-handedness payload.  It stops after the symmetry-derived four-way test
and requires the complete, all-and-only substituent CIP corpus. -/
structure P93FullereneType4AuthorityObservation
    (policy : P93FullereneAuthorityPolicy) where
  molecule : RawMolecule
  input : SymmetryDerivedMolecularFullereneConfigurationInput
  substituentAssignments : List P93FullereneSubstituentCIPAssignment

def P93FullereneType4AuthorityObservation.ValidFor
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93FullereneType4AuthorityObservation policy) : Prop :=
  policy.RawMoleculeObserved source observation.molecule ∧
    policy.SubstitutionEvidenceObserved source observation.molecule observation.input.cage
      observation.input.substitutionEvidence ∧
    policy.OriginalDerivativeChiralityObserved source observation.input.cage
      observation.input.substitutionEvidence.originalDerivativeChiral ∧
    SymmetryDerivedMolecularFullereneConfigurationInputJudgment
      observation.molecule observation.input ∧
    FullereneTypeMatches observation.input.cage.substitutionTest .chiralSubstituentsOnly ∧
    observation.input.cage.descriptorEvidence.cageNumberingKind = none ∧
    observation.input.cage.descriptorEvidence.cageTurn = none ∧
    observation.input.cage.descriptorEvidence.everyChiralSubstituentHasCIP = true ∧
    P93FullereneSubstituentCIPAssignmentsComplete policy source observation.molecule
      observation.input.cage observation.input.substitutionEvidence
      observation.substituentAssignments

/-- The P-93.5.6.6 case superimposes two independently complete layers: a Type 2 or Type 3
cage/substitution-pattern descriptor and every CIP descriptor on its chiral substituents. -/
structure P93FullereneSuperimposedAuthorityObservation
    (policy : P93FullereneAuthorityPolicy) where
  base : P93FullereneAuthorityObservation policy

def P93FullereneSuperimposedAuthorityObservation.ValidFor
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93FullereneSuperimposedAuthorityObservation policy) : Prop :=
  observation.base.ValidFor policy source ∧
    (observation.base.assignment.chiralityType =
        .inherentlyChiralSubstitutionPattern ∨
      observation.base.assignment.chiralityType =
        .noninherentlyChiralSubstitutionPattern) ∧
    (∃ numberingKind handedness,
      FullereneDescriptorPayload.cageHandedness numberingKind handedness ∈
        observation.base.assignment.payloads ∧
      policy.PrintedCageHandednessObserved source observation.base.molecule
        observation.base.selectedInput.symmetryInput.cage numberingKind handedness) ∧
    P93FullereneSubstituentCIPAssignmentsComplete policy source
      observation.base.molecule observation.base.selectedInput.symmetryInput.cage
      observation.base.selectedInput.symmetryInput.substitutionEvidence
      observation.base.substituentAssignments ∧
    SuperimposedFullereneConfigurationComplete true true

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93FullereneSubstituentCIPAssignmentsComplete
assert_kernel_only
  TetraStereo.OneCenter.p93FullereneFourWaySubstitutionDecisionRule
assert_kernel_only
  TetraStereo.OneCenter.P93FullereneAuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93FullereneAuthorityObservation.CageHandednessValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93FullereneMethodologyAuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93FullereneType4AuthorityObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93FullereneSuperimposedAuthorityObservation.ValidFor
