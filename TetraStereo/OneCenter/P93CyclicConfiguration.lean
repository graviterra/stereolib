import TetraStereo.OneCenter.P93AcyclicConfiguration
import TetraStereo.OneCenter.StereochemicalElements

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent P-93.5--P-93.6 cyclic configuration semantics

The definitions below transcribe the decision-shaped content shared by monocyclic, von Baeyer,
spiro, fused, cyclophane, fullerene, and ring-assembly provisions.  Exact molecular perception,
mean-plane construction, and name rendering remain separate refinement obligations.
-/

namespace BlueBookP93.Cyclic

/-! ## Monocyclic relative configuration -/

inductive RingSide where
  | positive
  | negative
  | onMeanPlane
  deriving DecidableEq, Repr

inductive CisTrans where
  | cis
  | trans
  deriving DecidableEq, Repr

def RelativeRingSide : RingSide → RingSide → CisTrans → Prop
  | .positive, .positive, .cis
  | .negative, .negative, .cis
  | .positive, .negative, .trans
  | .negative, .positive, .trans => True
  | _, _, _ => False

theorem cis_and_trans_disjoint (first second : RingSide) :
    ¬(RelativeRingSide first second .cis ∧ RelativeRingSide first second .trans) := by
  cases first <;> cases second <;> simp [RelativeRingSide]

structure RingPlaneObservation where
  usesMeanPlane : Prop
  firstSubstitutedPositionNotReentrant : Prop
  secondSubstitutedPositionNotReentrant : Prop

def CisTransPlaneApplicable (observation : RingPlaneObservation) : Prop :=
  observation.usesMeanPlane ∧
  observation.firstSubstitutedPositionNotReentrant ∧
  observation.secondSubstitutedPositionNotReentrant

inductive ConfigurationKnowledge where
  | absolute
  | relative
  | racemic
  deriving DecidableEq, Repr

inductive MonocycleNotation where
  | CIP
  | cisTrans
  | rct
  deriving DecidableEq, Repr

def PreferredMonocycleNotation : ConfigurationKnowledge → MonocycleNotation
  | .absolute | .relative | .racemic => .CIP

inductive RCTDescriptor where
  | reference
  | cisToReference
  | transToReference
  deriving DecidableEq, Repr

def rctDescriptor (referenceSide ligandSide : RingSide) : Option RCTDescriptor :=
  match referenceSide, ligandSide with
  | .positive, .positive | .negative, .negative => some .cisToReference
  | .positive, .negative | .negative, .positive => some .transToReference
  | _, _ => none

structure RCTReferenceCandidate where
  locant : ℕ
  namedAsSuffix : Bool
  sequencePriority : ℕ
  deriving DecidableEq, Repr

/-- P-93.5.1.3.2: a suffix-named ligand at the lowest eligible locant wins; otherwise the
sequence-rule-senior ligand at the lowest locant wins. -/
def IsRCTReference (candidates : List RCTReferenceCandidate)
    (selected : RCTReferenceCandidate) : Prop :=
  selected ∈ candidates ∧
  ((selected.namedAsSuffix = true ∧
      ∀ other ∈ candidates, other.namedAsSuffix = true → selected.locant ≤ other.locant) ∨
    ((∀ candidate ∈ candidates, candidate.namedAsSuffix = false) ∧
      ∀ other ∈ candidates,
        selected.locant < other.locant ∨
        (selected.locant = other.locant ∧ other.sequencePriority ≤ selected.sequencePriority)))

/-! ## Cyclic and exocyclic unsaturation -/

/-- Constitutionally distinct cyclic unsaturation cases that must not be routed by the same
descriptor algorithm.  In particular, P-31.1.3.3's fully cyclic cumulene has no terminal atoms,
whereas the cumulene systems illustrated by P-93.5.2.3 are open cumulative segments included in a
larger cyclic system. -/
inductive CyclicUnsaturationTopology where
  | ordinaryCyclicDoubleBondSystem
  | includedOpenCumuleneSegment
  | fullyCyclicCumulene
  deriving DecidableEq, Repr

/-- The ordinary terminal-pair cumulene assignment schema applies to an open cumulative segment
included in a ring, but not to a ring composed entirely of doubly linked atoms. -/
def OpenTerminalCumuleneSchemaApplies : CyclicUnsaturationTopology → Prop
  | .includedOpenCumuleneSegment => True
  | .ordinaryCyclicDoubleBondSystem | .fullyCyclicCumulene => False

/-- P-31.1.3.3's cyclic-cumulene parent-hydride topology applies only to the all-double closed
component.  This is a constitution/naming classification, not yet a configuration descriptor. -/
def P31FullyCyclicCumuleneParentApplies : CyclicUnsaturationTopology → Prop
  | .fullyCyclicCumulene => True
  | .ordinaryCyclicDoubleBondSystem | .includedOpenCumuleneSegment => False

theorem fully_cyclic_cumulene_has_no_open_terminal_schema :
    ¬OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene :=
  id

theorem fully_cyclic_cumulene_is_P31_parent_topology :
    P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene :=
  trivial

theorem cyclic_unsaturation_topologies_are_disjoint
    (topology : CyclicUnsaturationTopology) :
    ¬(OpenTerminalCumuleneSchemaApplies topology ∧
      P31FullyCyclicCumuleneParentApplies topology) := by
  cases topology <;>
    simp [OpenTerminalCumuleneSchemaApplies, P31FullyCyclicCumuleneParentApplies]

/-! ### Boundary of the P-93 terminal-cumulene descriptor provisions -/

/-- Parity branch selected by P-93.4.2.2 and P-93.4.2.3 for an *open* cumulative
double-bond system.  P-93.5.2.3 reuses these two branches when such a system is included in a
larger cyclic structure. -/
inductive OpenCumuleneParity where
  | even
  | odd
  deriving DecidableEq, Repr

/-- Independent applicability relation for descriptors assigned by the P-93 open-terminal
cumulene provisions.

The topology guard is essential: the descriptor vocabulary alone cannot distinguish an open
cumulene included in a ring from P-31.1.3.3's ring composed entirely of doubly linked atoms.
For an applicable open system, the parity branch selects precisely the P-93.4.2.2 axial
`M/P` (or general-nomenclature `Rₐ/Sₐ`) family or the P-93.4.2.3 planar `E/Z`
(or general-nomenclature `cis/trans`) family. -/
def OpenTerminalCumuleneDescriptorApplies
    (topology : CyclicUnsaturationTopology) (parity : OpenCumuleneParity)
    (descriptor : BlueBookP93.Acyclic.Descriptor) : Prop :=
  OpenTerminalCumuleneSchemaApplies topology ∧
    match parity with
    | .even => BlueBookP93.Acyclic.DescriptorApplies
        .evenDoubleBondCumulene descriptor
    | .odd => BlueBookP93.Acyclic.DescriptorApplies
        .oddDoubleBondCumulene descriptor

/-- P-93.5.2.3's included-open-cumulene case exposes exactly the parity-selected descriptor
family. -/
theorem included_open_cumulene_descriptor_applies_iff
    (parity : OpenCumuleneParity) (descriptor : BlueBookP93.Acyclic.Descriptor) :
    OpenTerminalCumuleneDescriptorApplies .includedOpenCumuleneSegment parity descriptor ↔
      match parity with
      | .even => BlueBookP93.Acyclic.DescriptorApplies
          .evenDoubleBondCumulene descriptor
      | .odd => BlueBookP93.Acyclic.DescriptorApplies
          .oddDoubleBondCumulene descriptor := by
  cases parity <;>
    simp [OpenTerminalCumuleneDescriptorApplies, OpenTerminalCumuleneSchemaApplies]

/-- No descriptor from P-93.4.2.2 or P-93.4.2.3, including their P-93.5.2.3 reuse inside
cyclic systems, applies to a P-31.1.3.3 fully cyclic cumulene.  This is deliberately narrower
than claiming that every conceivable stereodescriptor is permanently omitted. -/
theorem fully_cyclic_cumulene_has_no_open_terminal_descriptor
    (parity : OpenCumuleneParity) (descriptor : BlueBookP93.Acyclic.Descriptor) :
    ¬OpenTerminalCumuleneDescriptorApplies .fullyCyclicCumulene parity descriptor := by
  cases parity <;>
    simp [OpenTerminalCumuleneDescriptorApplies, OpenTerminalCumuleneSchemaApplies]

inductive DoubleBondDescriptorPolicy where
  | permanentlyOmit
  | requireEZ
  deriving DecidableEq, Repr

def MonocyclicDoubleBondPolicy
    (ringSize doubleBondCount : ℕ) : Option DoubleBondDescriptorPolicy :=
  if 3 ≤ ringSize ∧ ringSize ≤ 7 then some .permanentlyOmit
  else if ringSize = 8 ∧ doubleBondCount = 1 then some .requireEZ
  else if ringSize = 8 ∧ 2 ≤ doubleBondCount ∧ doubleBondCount ≤ 4 then
    some .permanentlyOmit
  else if 9 ≤ ringSize then some .requireEZ
  else none

/-- Exact applicability of the P-91/P-93 mandatory-`E/Z` monocycle policy. -/
theorem monocyclicDoubleBondPolicy_eq_requireEZ_iff
    (ringSize doubleBondCount : ℕ) :
    MonocyclicDoubleBondPolicy ringSize doubleBondCount = some .requireEZ ↔
      (ringSize = 8 ∧ doubleBondCount = 1) ∨ 9 ≤ ringSize := by
  unfold MonocyclicDoubleBondPolicy
  split_ifs <;> simp_all
  all_goals omega

/-- Exact applicability of permanent descriptor omission for small monocycles and the special
eight-membered polyene cases recorded by P-91.2.2. -/
theorem monocyclicDoubleBondPolicy_eq_permanentlyOmit_iff
    (ringSize doubleBondCount : ℕ) :
    MonocyclicDoubleBondPolicy ringSize doubleBondCount = some .permanentlyOmit ↔
      (3 ≤ ringSize ∧ ringSize ≤ 7) ∨
        (ringSize = 8 ∧ 2 ≤ doubleBondCount ∧ doubleBondCount ≤ 4) := by
  unfold MonocyclicDoubleBondPolicy
  split_ifs <;> simp_all

/-- The mandatory and omission policies never overlap for the same ring evidence. -/
theorem monocyclicDoubleBondPolicies_disjoint
    (ringSize doubleBondCount : ℕ) :
    ¬(MonocyclicDoubleBondPolicy ringSize doubleBondCount = some .requireEZ ∧
      MonocyclicDoubleBondPolicy ringSize doubleBondCount = some .permanentlyOmit) := by
  rintro ⟨required, omitted⟩
  rw [required] at omitted
  cases omitted

/-- Independent spatial relation between the two CIP-senior endpoint ligands. This type belongs
to the normative cyclic specification and deliberately does not reuse a production geometry
type. -/
inductive MonocyclicSeniorLigandGeometry where
  | together
  | opposite
  deriving DecidableEq, Repr

/-- Independent P-93 meaning of an emitted descriptor for an ordinary monocyclic double bond.
The ring policy must require a descriptor, and the two CIP-senior endpoint ligands must have the
corresponding geometry: together is `Z`, opposite is `E`. -/
def RequiredMonocyclicEZAssignment
    (ringSize doubleBondCount : ℕ) (geometry : MonocyclicSeniorLigandGeometry)
    (descriptor : BlueBookP93.Acyclic.Descriptor) : Prop :=
  MonocyclicDoubleBondPolicy ringSize doubleBondCount = some .requireEZ ∧
    match geometry, descriptor with
    | .together, .Z | .opposite, .E => True
    | _, _ => False

/-- Independent executable form of the required cyclic `E/Z` assignment. Permanent omission,
an untranscribed policy case, or a nonstereogenic endpoint result emits no descriptor. -/
def requiredMonocyclicEZDescriptor?
    (ringSize doubleBondCount : ℕ) (geometry : MonocyclicSeniorLigandGeometry) :
    Option BlueBookP93.Acyclic.Descriptor :=
  match MonocyclicDoubleBondPolicy ringSize doubleBondCount with
  | some .requireEZ =>
      match geometry with
      | .together => some .Z
      | .opposite => some .E
  | some .permanentlyOmit | none => none

/-- The independent cyclic assignment evaluator succeeds exactly for the required policy and
the authoritative senior-ligand geometry correspondence. -/
theorem requiredMonocyclicEZDescriptor?_eq_some_iff
    (ringSize doubleBondCount : ℕ) (geometry : MonocyclicSeniorLigandGeometry)
    (descriptor : BlueBookP93.Acyclic.Descriptor) :
    requiredMonocyclicEZDescriptor? ringSize doubleBondCount geometry = some descriptor ↔
      RequiredMonocyclicEZAssignment ringSize doubleBondCount geometry descriptor := by
  cases policyComputed : MonocyclicDoubleBondPolicy ringSize doubleBondCount with
  | none =>
      cases geometry <;> cases descriptor <;>
        simp [requiredMonocyclicEZDescriptor?, RequiredMonocyclicEZAssignment,
          policyComputed]
  | some policy =>
      cases policy <;> cases geometry <;> cases descriptor <;>
        simp [requiredMonocyclicEZDescriptor?, RequiredMonocyclicEZAssignment,
          policyComputed]

theorem requiredMonocyclicEZDescriptor?_eq_none_of_omitted
    (ringSize doubleBondCount : ℕ) (geometry : MonocyclicSeniorLigandGeometry)
    (omitted : MonocyclicDoubleBondPolicy ringSize doubleBondCount =
      some .permanentlyOmit) :
    requiredMonocyclicEZDescriptor? ringSize doubleBondCount geometry = none := by
  simp [requiredMonocyclicEZDescriptor?, omitted]

@[simp] theorem eight_membered_required_together_is_Z :
    requiredMonocyclicEZDescriptor? 8 1 .together =
      some BlueBookP93.Acyclic.Descriptor.Z := by
  decide

@[simp] theorem eight_membered_required_opposite_is_E :
    requiredMonocyclicEZDescriptor? 8 1 .opposite =
      some BlueBookP93.Acyclic.Descriptor.E := by
  decide

@[simp] theorem seven_membered_together_emits_no_EZ :
    requiredMonocyclicEZDescriptor? 7 1 .together = none := by
  decide

@[simp] theorem seven_membered_cyclic_double_bond_omits :
    MonocyclicDoubleBondPolicy 7 3 = some .permanentlyOmit := by
  decide

@[simp] theorem eight_membered_cyclic_double_bond_requires_EZ :
    MonocyclicDoubleBondPolicy 8 1 = some .requireEZ := by
  decide

@[simp] theorem eight_membered_tetraene_omits_redundant_descriptors :
    MonocyclicDoubleBondPolicy 8 4 = some .permanentlyOmit := by
  decide

@[simp] theorem eight_membered_diene_omits_redundant_descriptors :
    MonocyclicDoubleBondPolicy 8 2 = some .permanentlyOmit := by
  decide

@[simp] theorem eight_membered_triene_omits_redundant_descriptors :
    MonocyclicDoubleBondPolicy 8 3 = some .permanentlyOmit := by
  decide

@[simp] theorem nine_membered_cyclic_double_bond_requires_EZ :
    MonocyclicDoubleBondPolicy 9 1 = some .requireEZ := by
  decide

inductive ChiralCycloalkeneDescriptor where
  | M | P | Rp | Sp
  deriving DecidableEq, Repr

def PreferredChiralCycloalkeneDescriptor : ChiralCycloalkeneDescriptor → Prop
  | .M | .P => True
  | .Rp | .Sp => False

inductive ExocyclicNamingMethod where
  | integralParentDoubleBond
  | ylideneSubstituent
  | wholeOddCumulene
  deriving DecidableEq, Repr

def ExocyclicMethodAllowed (contextIsPIN : Bool) (doubleBondCount ringSize : ℕ)
    (oppositePositions : Bool) : ExocyclicNamingMethod → Prop
  | .integralParentDoubleBond => True
  | .ylideneSubstituent => contextIsPIN = false
  | .wholeOddCumulene =>
      contextIsPIN = false ∧ doubleBondCount = 2 ∧ Even ringSize ∧
        oppositePositions = true

theorem integral_parent_method_is_PIN_method
    (doubleBondCount ringSize : ℕ) (oppositePositions : Bool) :
    ExocyclicMethodAllowed true doubleBondCount ringSize oppositePositions
      .integralParentDoubleBond :=
  trivial

inductive ExocyclicSystemTreatment where
  | individualStereogenicUnits
  | wholeAlleneSystem
  deriving DecidableEq, Repr

def PreferredExocyclicSystemTreatment : ExocyclicSystemTreatment → Prop
  | .individualStereogenicUnits => True
  | .wholeAlleneSystem => False

/-! ## von Baeyer systems -/

structure VonBaeyerBridgeSystem where
  x : ℕ
  y : ℕ
  z : ℕ

def EndoExoSynAntiApplicable (system : VonBaeyerBridgeSystem) : Prop :=
  system.y ≤ system.x ∧ system.z < system.y ∧ 0 < system.z ∧
    system.x + system.y < 7

inductive BridgeAttachment where
  | nonHighestBridgeAtomTowardHighestBridge
  | nonHighestBridgeAtomAwayFromHighestBridge
  | highestBridgeAtomTowardLowestBridge
  | highestBridgeAtomAwayFromLowestBridge
  deriving DecidableEq, Repr

inductive BridgeDescriptor where
  | exo | endo | syn | anti
  deriving DecidableEq, Repr

def bridgeDescriptor : BridgeAttachment → BridgeDescriptor
  | .nonHighestBridgeAtomTowardHighestBridge => .exo
  | .nonHighestBridgeAtomAwayFromHighestBridge => .endo
  | .highestBridgeAtomTowardLowestBridge => .syn
  | .highestBridgeAtomAwayFromLowestBridge => .anti

/-- These four descriptors state relative orientation and cannot by themselves distinguish a
single enantiomer from the corresponding racemate. -/
def BridgeDescriptorDeterminesAbsolute (_ : BridgeDescriptor) : Prop := False

theorem bridge_descriptor_never_determines_absolute (descriptor : BridgeDescriptor) :
    ¬BridgeDescriptorDeterminesAbsolute descriptor := by
  simp [BridgeDescriptorDeterminesAbsolute]

inductive BridgeheadRelativeNotation where
  | relCIP
  | cisTrans
  deriving DecidableEq, Repr

def PreferredBridgeheadRelativeNotation : BridgeheadRelativeNotation → Prop
  | .relCIP => True
  | .cisTrans => False

/-- P-93.5.2.3's named small-system boundary. -/
def VonBaeyerDoubleBondDescriptorRequired (largerThanBicyclo333 : Bool) : Bool :=
  largerThanBicyclo333

/-! ## Spiro systems -/

inductive SpiroLigandPattern where
  | Xabcd
  | Xabab
  | Xaabb
  deriving DecidableEq, Repr

inductive SpiroDescriptorFamily where
  | centerRS
  | centerRrSs
  | axialMP
  | polyhedralAC
  deriving DecidableEq, Repr

def SpiroFamilySupported : SpiroLigandPattern → SpiroDescriptorFamily → Prop
  | .Xabcd, .centerRS
  | .Xabab, .centerRS
  | .Xabab, .centerRrSs
  | .Xaabb, .centerRS
  | .Xaabb, .axialMP => True
  | _, _ => False

/-- For Xabab, equivalent pairs are broken by starting at the first senior occurrence and then
following the branch containing it; this is an occurrence-sensitive, not element-only, ordering. -/
structure XababOccurrenceOrder where
  firstSeniorChosen : Prop
  secondSeniorDistinguishedByTraversal : Prop
  juniorOnFirstSeniorBranchChosenFirst : Prop

def ValidXababOccurrenceOrder (order : XababOccurrenceOrder) : Prop :=
  order.firstSeniorChosen ∧ order.secondSeniorDistinguishedByTraversal ∧
  order.juniorOnFirstSeniorBranchChosenFirst

def SpiroDoubleBondDescriptorRequired (ringSize : ℕ) : Bool :=
  8 ≤ ringSize

@[simp] theorem spiro_seven_ring_omits_double_bond_descriptor :
    SpiroDoubleBondDescriptorRequired 7 = false := by
  decide

@[simp] theorem spiro_eight_ring_requires_double_bond_descriptor :
    SpiroDoubleBondDescriptorRequired 8 = true := by
  decide

inductive SpiroCenterCoordination where
  | tetrahedral
  | lambda4
  | lambda5
  | lambda6
  deriving DecidableEq, Repr

def PolyhedralACApplicable : SpiroCenterCoordination → Prop
  | .lambda4 | .lambda5 | .lambda6 => True
  | .tetrahedral => False

/-! ## Fused systems and cyclophanes -/

inductive FusedUnitDescriptor where
  | R | S | r | s | M | P
  deriving DecidableEq, Repr

inductive FusionRelationDescriptor where
  | relCIP | cis | trans | cisoid | transoid
  deriving DecidableEq, Repr

def PreferredFusionDescription : FusionRelationDescriptor → Prop
  | .relCIP => True
  | .cis | .trans | .cisoid | .transoid => False

structure NearestFusionPairCandidate where
  graphDistance : ℕ
  lowerAtomLocant : ℕ
  deriving DecidableEq, Repr

def IsSelectedNearestFusionPair
    (candidates : List NearestFusionPairCandidate)
    (selected : NearestFusionPairCandidate) : Prop :=
  selected ∈ candidates ∧
  ∀ other ∈ candidates,
    selected.graphDistance < other.graphDistance ∨
    (selected.graphDistance = other.graphDistance ∧
      selected.lowerAtomLocant ≤ other.lowerAtomLocant)

inductive CyclophanePlaneDescriptor where
  | M | P | Rp | Sp
  deriving DecidableEq, Repr

/-- Spatial reflection exchanges both the preferred and general spellings of the two
cyclophane-plane configurations. -/
def CyclophanePlaneDescriptor.mirror :
    CyclophanePlaneDescriptor → CyclophanePlaneDescriptor
  | .P => .M
  | .M => .P
  | .Rp => .Sp
  | .Sp => .Rp

@[simp] theorem CyclophanePlaneDescriptor.mirror_mirror
    (descriptor : CyclophanePlaneDescriptor) :
    descriptor.mirror.mirror = descriptor := by
  cases descriptor <;> rfl

def PreferredCyclophanePlaneDescriptor : CyclophanePlaneDescriptor → Prop
  | .M | .P => True
  | .Rp | .Sp => False

/-- P-93.5.5.1 correspondence and preference: `P` replaces the general planar `Rₚ`, while
`M` replaces `Sₚ`, for the same cyclophane-plane configuration. -/
def CyclophanePlaneDescriptor.preferredEquivalent :
    CyclophanePlaneDescriptor → CyclophanePlaneDescriptor
  | .P | .Rp => .P
  | .M | .Sp => .M

/-- Two cyclophane-plane symbols denote the same configuration exactly when their preferred
P-93.5.5.1 representatives agree. -/
def SameCyclophanePlaneConfiguration
    (left right : CyclophanePlaneDescriptor) : Prop :=
  left.preferredEquivalent = right.preferredEquivalent

@[simp] theorem preferredEquivalent_P :
    CyclophanePlaneDescriptor.P.preferredEquivalent = .P := rfl

@[simp] theorem preferredEquivalent_M :
    CyclophanePlaneDescriptor.M.preferredEquivalent = .M := rfl

@[simp] theorem preferredEquivalent_Rp :
    CyclophanePlaneDescriptor.Rp.preferredEquivalent = .P := rfl

@[simp] theorem preferredEquivalent_Sp :
    CyclophanePlaneDescriptor.Sp.preferredEquivalent = .M := rfl

/-- Every accepted general or preferred cyclophane-plane symbol has a preferred representative. -/
theorem preferredEquivalent_is_preferred (descriptor : CyclophanePlaneDescriptor) :
    PreferredCyclophanePlaneDescriptor descriptor.preferredEquivalent := by
  cases descriptor <;> trivial

/-- Taking the preferred P-93.5.5.1 spelling commutes with spatial reflection. -/
@[simp] theorem preferredEquivalent_mirror (descriptor : CyclophanePlaneDescriptor) :
    descriptor.mirror.preferredEquivalent = descriptor.preferredEquivalent.mirror := by
  cases descriptor <;> rfl

/-- Embed the general P-92 planar family into the acceptable P-93.5.5.1 cyclophane vocabulary. -/
def CyclophanePlaneDescriptor.ofGeneralPlanar :
    PlanarDescriptor → CyclophanePlaneDescriptor
  | .Rp => .Rp
  | .Sp => .Sp

/-- Preferred P-93.5.5.1 symbol for a coordinate-derived general planar descriptor.  This is a
plane-naming result, not a helical stereogenic unit. -/
def CyclophanePlaneDescriptor.preferredOfGeneralPlanar
    (descriptor : PlanarDescriptor) : CyclophanePlaneDescriptor :=
  (ofGeneralPlanar descriptor).preferredEquivalent

@[simp] theorem preferredOfGeneralPlanar_Rp :
    CyclophanePlaneDescriptor.preferredOfGeneralPlanar .Rp = .P := rfl

@[simp] theorem preferredOfGeneralPlanar_Sp :
    CyclophanePlaneDescriptor.preferredOfGeneralPlanar .Sp = .M := rfl

/-- Coordinate reflection followed by preferred cyclophane naming gives the mirror of the
original preferred name. -/
@[simp] theorem preferredOfGeneralPlanar_mirror (descriptor : PlanarDescriptor) :
    CyclophanePlaneDescriptor.preferredOfGeneralPlanar descriptor.mirror =
      (CyclophanePlaneDescriptor.preferredOfGeneralPlanar descriptor).mirror := by
  cases descriptor <;> rfl

theorem preferredOfGeneralPlanar_is_preferred (descriptor : PlanarDescriptor) :
    PreferredCyclophanePlaneDescriptor
      (CyclophanePlaneDescriptor.preferredOfGeneralPlanar descriptor) := by
  cases descriptor <;> trivial

theorem preferredOfGeneralPlanar_same_configuration (descriptor : PlanarDescriptor) :
    SameCyclophanePlaneConfiguration
      (CyclophanePlaneDescriptor.ofGeneralPlanar descriptor)
      (CyclophanePlaneDescriptor.preferredOfGeneralPlanar descriptor) := by
  cases descriptor <;> rfl

/-- The P-93.5.5.1 preferred representative exists and is unique for every one of the four
accepted cyclophane-plane symbols. -/
theorem existsUnique_preferred_sameCyclophanePlaneConfiguration
    (descriptor : CyclophanePlaneDescriptor) :
  ∃! preferred,
      PreferredCyclophanePlaneDescriptor preferred ∧
        SameCyclophanePlaneConfiguration descriptor preferred := by
  have sameRepresentative : SameCyclophanePlaneConfiguration
      descriptor descriptor.preferredEquivalent := by
    cases descriptor <;> rfl
  refine ⟨descriptor.preferredEquivalent,
    ⟨preferredEquivalent_is_preferred descriptor, sameRepresentative⟩, ?_⟩
  intro candidate candidateJudgment
  rcases candidateJudgment with ⟨candidatePreferred, sameConfiguration⟩
  cases descriptor <;> cases candidate <;>
    simp [PreferredCyclophanePlaneDescriptor, SameCyclophanePlaneConfiguration,
      CyclophanePlaneDescriptor.preferredEquivalent] at candidatePreferred sameConfiguration ⊢

structure CyclophanePlaneReference where
  chosenLigandIsCIPHighest : Prop
  locantIsCompositeRingLocantViewedFromPilotAtom : Prop

def ValidCyclophanePlaneReference (reference : CyclophanePlaneReference) : Prop :=
  reference.chosenLigandIsCIPHighest ∧
  reference.locantIsCompositeRingLocantViewedFromPilotAtom

def CyclophaneDoubleBondDescriptorRequired (totalNodes ringNodes : ℕ) : Bool :=
  7 < totalNodes && 7 < ringNodes

/-! ## Fullerenes -/

structure FullereneSubstitutionTest where
  parentChiral : Bool
  originalDerivativeChiral : Bool
  allSubstituentsReplacedByAchiralTChiral : Bool
  substitutionPatternWithActualIdentitiesChiral : Bool
  hasChiralSubstituent : Bool

inductive FullereneChiralityType where
  | inherentlyChiralParent
  | inherentlyChiralSubstitutionPattern
  | noninherentlyChiralSubstitutionPattern
  | chiralSubstituentsOnly
  deriving DecidableEq, Repr

def FullereneTypeMatches
    (test : FullereneSubstitutionTest) : FullereneChiralityType → Prop
  | .inherentlyChiralParent => test.parentChiral = true
  | .inherentlyChiralSubstitutionPattern =>
      test.parentChiral = false ∧ test.allSubstituentsReplacedByAchiralTChiral = true
  | .noninherentlyChiralSubstitutionPattern =>
      test.parentChiral = false ∧ test.originalDerivativeChiral = true ∧
      test.allSubstituentsReplacedByAchiralTChiral = false ∧
      test.substitutionPatternWithActualIdentitiesChiral = true
  | .chiralSubstituentsOnly =>
      test.parentChiral = false ∧
      test.originalDerivativeChiral = true ∧
      test.allSubstituentsReplacedByAchiralTChiral = false ∧
      test.substitutionPatternWithActualIdentitiesChiral = false ∧
      test.hasChiralSubstituent = true

theorem fullerene_type3_and_type4_disjoint (test : FullereneSubstitutionTest) :
    ¬(FullereneTypeMatches test .noninherentlyChiralSubstitutionPattern ∧
      FullereneTypeMatches test .chiralSubstituentsOnly) := by
  rintro ⟨⟨_, _, _, identityChiral⟩, ⟨_, _, _, identityAchiral, _⟩⟩
  rw [identityChiral] at identityAchiral
  cases identityAchiral

inductive FullereneNumberingKind where
  | systematic
  | trivial
  deriving DecidableEq, Repr

inductive FullereneHandedness where
  | A
  | C
  deriving DecidableEq, Repr

inductive ThreeLocantTurn where
  | clockwise
  | anticlockwise
  deriving DecidableEq, Repr

def fullereneHandedness : ThreeLocantTurn → FullereneHandedness
  | .clockwise => .C
  | .anticlockwise => .A

inductive FullereneDescriptorRequirement where
  | cageHandedness
  | substituentCIP
  deriving DecidableEq, Repr

def RequiredFullereneDescriptorKinds :
    FullereneChiralityType → List FullereneDescriptorRequirement
  | .inherentlyChiralParent => [.cageHandedness]
  | .inherentlyChiralSubstitutionPattern => [.cageHandedness]
  | .noninherentlyChiralSubstitutionPattern => [.cageHandedness]
  | .chiralSubstituentsOnly => [.substituentCIP]

def SuperimposedFullereneConfigurationComplete
    (hasCageDescriptor hasEverySubstituentDescriptor : Bool) : Prop :=
  hasCageDescriptor = true ∧ hasEverySubstituentDescriptor = true

/-! ## Ring assemblies and coupled ring/chain names -/

inductive RingAssemblyAxisDescriptor where
  | M | P | Ra | Sa
  deriving DecidableEq, Repr

def PreferredRingAssemblyAxisDescriptor : RingAssemblyAxisDescriptor → Prop
  | .M | .P => True
  | .Ra | .Sa => False

inductive RingAssemblyCenterDescriptor where
  | R | S | r | s | cis | trans
  deriving DecidableEq, Repr

def PreferredRingAssemblyCenterDescriptor : RingAssemblyCenterDescriptor → Prop
  | .R | .S | .r | .s => True
  | .cis | .trans => False

/-- P-93.5.7.3 imports P-91.2.2, with the special eight-membered-ring all-or-none statement. -/
def EightMemberedAssemblySpecificationComplete
    (oneUnitNeedsSpecification : Bool)
    (allStereogenicUnitsSpecified : Bool) : Prop :=
  oneUnitNeedsSpecification = true → allStereogenicUnitsSpecified = true

structure RingChainAnnotatedName (BaseName Descriptor : Type*) where
  baseName : BaseName
  descriptors : List Descriptor
  multiplicativeSymmetryRespected : Prop

def RingChainAnnotatedName.withDescriptors {BaseName Descriptor : Type*}
    (name : RingChainAnnotatedName BaseName Descriptor)
    (descriptors : List Descriptor) : RingChainAnnotatedName BaseName Descriptor :=
  { name with descriptors := descriptors }

@[simp] theorem ring_chain_descriptors_do_not_change_base_name
    {BaseName Descriptor : Type*}
    (name : RingChainAnnotatedName BaseName Descriptor)
    (descriptors : List Descriptor) :
    (name.withDescriptors descriptors).baseName = name.baseName :=
  rfl

end BlueBookP93.Cyclic

end TetraStereo.OneCenter
