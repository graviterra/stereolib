import TetraStereo.OneCenter.IUPACRemaining71P93ClosedProductionFamilies
import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthoritySourceAudit

set_option autoImplicit false



















namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic
open BlueBookP93.NoncarbonTetrahedra
open IUPACNormativeProvision

/-! ## Closed descriptor and name carriers -/

/-- One closed descriptor carrier spanning every descriptor language used by the fifty-six P-93
rows.  In particular, the general-configuration family no longer chooses an arbitrary `Type`. -/
inductive P93CanonicalDescriptor where
  | acyclic (descriptor : BlueBookP93.Acyclic.Descriptor)
  | fused (descriptor : FusedUnitDescriptor)
  | cyclophanePlane (descriptor : CyclophanePlaneDescriptor)
  | cyclophaneRelativeCenter (descriptor : RCTDescriptor)
  | polyhedral (descriptor : PolyhedralChiralitySymbol)
  | fullerene (descriptor : FullereneDescriptorPayload)
  | ringAssemblyAxis (descriptor : RingAssemblyAxisDescriptor)
  | ringAssemblyCenter (descriptor : RingAssemblyCenterDescriptor)
  deriving DecidableEq, Repr

namespace P93CanonicalDescriptor

/-- Spatial reflection on the closed P-93 descriptor carrier.  Relative descriptors and the
fullerene `substituentCIPComplete` marker are mirror invariant; handed descriptors are exchanged.
The lower-case `r/s` symbols are pseudoasymmetric and therefore remain unchanged under reflection,
as required by P-91.2.1.1. -/
def mirror : P93CanonicalDescriptor → P93CanonicalDescriptor
  | .acyclic .R => .acyclic .S
  | .acyclic .S => .acyclic .R
  | .acyclic .r => .acyclic .r
  | .acyclic .s => .acyclic .s
  | .acyclic .E => .acyclic .E
  | .acyclic .Z => .acyclic .Z
  | .acyclic .cis => .acyclic .cis
  | .acyclic .trans => .acyclic .trans
  | .acyclic .M => .acyclic .P
  | .acyclic .P => .acyclic .M
  | .acyclic .Ra => .acyclic .Sa
  | .acyclic .Sa => .acyclic .Ra
  | .fused .R => .fused .S
  | .fused .S => .fused .R
  | .fused .r => .fused .r
  | .fused .s => .fused .s
  | .fused .M => .fused .P
  | .fused .P => .fused .M
  | .cyclophanePlane descriptor => .cyclophanePlane descriptor.mirror
  | .cyclophaneRelativeCenter descriptor => .cyclophaneRelativeCenter descriptor
  | .polyhedral .A => .polyhedral .C
  | .polyhedral .C => .polyhedral .A
  | .fullerene (.cageHandedness numbering .A) =>
      .fullerene (.cageHandedness numbering .C)
  | .fullerene (.cageHandedness numbering .C) =>
      .fullerene (.cageHandedness numbering .A)
  | .fullerene .substituentCIPComplete => .fullerene .substituentCIPComplete
  | .ringAssemblyAxis .M => .ringAssemblyAxis .P
  | .ringAssemblyAxis .P => .ringAssemblyAxis .M
  | .ringAssemblyAxis .Ra => .ringAssemblyAxis .Sa
  | .ringAssemblyAxis .Sa => .ringAssemblyAxis .Ra
  | .ringAssemblyCenter .R => .ringAssemblyCenter .S
  | .ringAssemblyCenter .S => .ringAssemblyCenter .R
  | .ringAssemblyCenter .r => .ringAssemblyCenter .r
  | .ringAssemblyCenter .s => .ringAssemblyCenter .s
  | .ringAssemblyCenter .cis => .ringAssemblyCenter .cis
  | .ringAssemblyCenter .trans => .ringAssemblyCenter .trans

@[simp] theorem mirror_mirror (descriptor : P93CanonicalDescriptor) :
    mirror (mirror descriptor) = descriptor := by
  cases descriptor with
  | acyclic descriptor => cases descriptor <;> rfl
  | fused descriptor => cases descriptor <;> rfl
  | cyclophanePlane descriptor => cases descriptor <;> rfl
  | cyclophaneRelativeCenter descriptor => cases descriptor <;> rfl
  | polyhedral descriptor => cases descriptor <;> rfl
  | fullerene descriptor =>
      cases descriptor with
      | cageHandedness numbering handedness => cases handedness <;> rfl
      | substituentCIPComplete => rfl
  | ringAssemblyAxis descriptor => cases descriptor <;> rfl
  | ringAssemblyCenter descriptor => cases descriptor <;> rfl

def mirrorAction : P93AuthorityConfiguration.MirrorAction P93CanonicalDescriptor where
  mirror := mirror
  involutive := mirror_mirror

/-- Involutive **local** descriptor inversion for the one-unit epimerization of P-93.1.4
`ambo`.  This is the descriptor table obtained by exchanging the two ligands at one stated
stereogenic unit.  It agrees with global `mirror` except at pseudoasymmetric `r/s`, which global
reflection fixes but a local two-ligand exchange reverses (P-9).  The table describes the stated
configuration only: it does not assert that physically re-preparing one centre leaves remote CIP
descriptors unchanged, and it is not a universal physical theorem. -/
def localInvert : P93CanonicalDescriptor → P93CanonicalDescriptor
  | .acyclic .R => .acyclic .S
  | .acyclic .S => .acyclic .R
  | .acyclic .r => .acyclic .s
  | .acyclic .s => .acyclic .r
  | .acyclic .E => .acyclic .E
  | .acyclic .Z => .acyclic .Z
  | .acyclic .cis => .acyclic .cis
  | .acyclic .trans => .acyclic .trans
  | .acyclic .M => .acyclic .P
  | .acyclic .P => .acyclic .M
  | .acyclic .Ra => .acyclic .Sa
  | .acyclic .Sa => .acyclic .Ra
  | .fused .R => .fused .S
  | .fused .S => .fused .R
  | .fused .r => .fused .s
  | .fused .s => .fused .r
  | .fused .M => .fused .P
  | .fused .P => .fused .M
  | .cyclophanePlane descriptor => .cyclophanePlane descriptor.mirror
  | .cyclophaneRelativeCenter descriptor => .cyclophaneRelativeCenter descriptor
  | .polyhedral .A => .polyhedral .C
  | .polyhedral .C => .polyhedral .A
  | .fullerene (.cageHandedness numbering .A) =>
      .fullerene (.cageHandedness numbering .C)
  | .fullerene (.cageHandedness numbering .C) =>
      .fullerene (.cageHandedness numbering .A)
  | .fullerene .substituentCIPComplete => .fullerene .substituentCIPComplete
  | .ringAssemblyAxis .M => .ringAssemblyAxis .P
  | .ringAssemblyAxis .P => .ringAssemblyAxis .M
  | .ringAssemblyAxis .Ra => .ringAssemblyAxis .Sa
  | .ringAssemblyAxis .Sa => .ringAssemblyAxis .Ra
  | .ringAssemblyCenter .R => .ringAssemblyCenter .S
  | .ringAssemblyCenter .S => .ringAssemblyCenter .R
  | .ringAssemblyCenter .r => .ringAssemblyCenter .s
  | .ringAssemblyCenter .s => .ringAssemblyCenter .r
  | .ringAssemblyCenter .cis => .ringAssemblyCenter .cis
  | .ringAssemblyCenter .trans => .ringAssemblyCenter .trans

@[simp] theorem localInvert_acyclic_R :
    localInvert (.acyclic .R) = .acyclic .S := rfl

@[simp] theorem localInvert_acyclic_S :
    localInvert (.acyclic .S) = .acyclic .R := rfl

@[simp] theorem localInvert_acyclic_r :
    localInvert (.acyclic .r) = .acyclic .s := rfl

@[simp] theorem localInvert_acyclic_s :
    localInvert (.acyclic .s) = .acyclic .r := rfl

@[simp] theorem localInvert_fused_R :
    localInvert (.fused .R) = .fused .S := rfl

@[simp] theorem localInvert_fused_S :
    localInvert (.fused .S) = .fused .R := rfl

@[simp] theorem localInvert_fused_r :
    localInvert (.fused .r) = .fused .s := rfl

@[simp] theorem localInvert_fused_s :
    localInvert (.fused .s) = .fused .r := rfl

@[simp] theorem localInvert_ringAssemblyCenter_R :
    localInvert (.ringAssemblyCenter .R) = .ringAssemblyCenter .S := rfl

@[simp] theorem localInvert_ringAssemblyCenter_S :
    localInvert (.ringAssemblyCenter .S) = .ringAssemblyCenter .R := rfl

@[simp] theorem localInvert_ringAssemblyCenter_r :
    localInvert (.ringAssemblyCenter .r) = .ringAssemblyCenter .s := rfl

@[simp] theorem localInvert_ringAssemblyCenter_s :
    localInvert (.ringAssemblyCenter .s) = .ringAssemblyCenter .r := rfl

@[simp] theorem localInvert_involutive (descriptor : P93CanonicalDescriptor) :
    localInvert (localInvert descriptor) = descriptor := by
  cases descriptor with
  | acyclic descriptor => cases descriptor <;> rfl
  | fused descriptor => cases descriptor <;> rfl
  | cyclophanePlane descriptor => cases descriptor <;> rfl
  | cyclophaneRelativeCenter descriptor => cases descriptor <;> rfl
  | polyhedral descriptor => cases descriptor <;> rfl
  | fullerene descriptor =>
      cases descriptor with
      | cageHandedness numbering handedness => cases handedness <;> rfl
      | substituentCIPComplete => rfl
  | ringAssemblyAxis descriptor => cases descriptor <;> rfl
  | ringAssemblyCenter descriptor => cases descriptor <;> rfl

/-- Certified involutive **local** action.  It is deliberately distinct from `mirrorAction`:
global reflection fixes pseudoasymmetric `r/s`, while a two-ligand exchange at one centre swaps
them. -/
def localAction : P93AuthorityConfiguration.MirrorAction P93CanonicalDescriptor where
  mirror := localInvert
  involutive := localInvert_involutive

/-- Descriptors for which P-93.1 supplies a source-supported choice of displayed representative.
Mirror-invariant pseudoasymmetric and relative descriptors cannot select an enantiomeric
representative.  Polyhedral and fullerene `A/C` are excluded because their handedness is computed
from an exact geometry or numbering, not by a universal lowest-locant polarity. -/
def GeneralRepresentativeEligible : P93CanonicalDescriptor → Prop
  | .acyclic .R | .acyclic .S | .acyclic .M | .acyclic .P
  | .acyclic .Ra | .acyclic .Sa => True
  | .fused .R | .fused .S | .fused .M | .fused .P => True
  | .cyclophanePlane .M | .cyclophanePlane .P
  | .cyclophanePlane .Rp | .cyclophanePlane .Sp => True
  | .ringAssemblyAxis .M | .ringAssemblyAxis .P
  | .ringAssemblyAxis .Ra | .ringAssemblyAxis .Sa => True
  | .ringAssemblyCenter .R | .ringAssemblyCenter .S => True
  | _ => False

/-- Closed representative polarity for the source-supported descriptor pairs.  Values outside
`GeneralRepresentativeEligible` are false and have no authority meaning. -/
def PreferredAtLowest : P93CanonicalDescriptor → Prop
  | .acyclic .R | .acyclic .M | .acyclic .Ra => True
  | .fused .R | .fused .M => True
  | .cyclophanePlane .M | .cyclophanePlane .Rp => True
  | .ringAssemblyAxis .M | .ringAssemblyAxis .Ra => True
  | .ringAssemblyCenter .R => True
  | _ => False

@[simp] theorem mirror_generalRepresentativeEligible_iff
    (descriptor : P93CanonicalDescriptor) :
    descriptor.mirror.GeneralRepresentativeEligible ↔
      descriptor.GeneralRepresentativeEligible := by
  cases descriptor with
  | acyclic value => cases value <;> simp [mirror, GeneralRepresentativeEligible]
  | fused value => cases value <;> simp [mirror, GeneralRepresentativeEligible]
  | cyclophanePlane value =>
      cases value <;>
        simp [mirror, CyclophanePlaneDescriptor.mirror, GeneralRepresentativeEligible]
  | cyclophaneRelativeCenter value =>
      cases value <;> simp [mirror, GeneralRepresentativeEligible]
  | polyhedral value => cases value <;> simp [mirror, GeneralRepresentativeEligible]
  | fullerene value =>
      cases value with
      | cageHandedness numbering handedness =>
          cases handedness <;> simp [mirror, GeneralRepresentativeEligible]
      | substituentCIPComplete => simp [mirror, GeneralRepresentativeEligible]
  | ringAssemblyAxis value => cases value <;> simp [mirror, GeneralRepresentativeEligible]
  | ringAssemblyCenter value => cases value <;> simp [mirror, GeneralRepresentativeEligible]

theorem representativeEligible_mirror_iff
    (descriptor : P93CanonicalDescriptor) :
    descriptor.mirror.GeneralRepresentativeEligible ↔
      descriptor.GeneralRepresentativeEligible :=
  mirror_generalRepresentativeEligible_iff descriptor

/-- The local action preserves representative eligibility.  In particular it never turns a
pseudoasymmetric or relative descriptor into an enantiomeric representative. -/
@[simp] theorem localInvert_generalRepresentativeEligible_iff
    (descriptor : P93CanonicalDescriptor) :
    descriptor.localInvert.GeneralRepresentativeEligible ↔
      descriptor.GeneralRepresentativeEligible := by
  cases descriptor with
  | acyclic value => cases value <;> simp [localInvert, GeneralRepresentativeEligible]
  | fused value => cases value <;> simp [localInvert, GeneralRepresentativeEligible]
  | cyclophanePlane value =>
      cases value <;>
        simp [localInvert, CyclophanePlaneDescriptor.mirror, GeneralRepresentativeEligible]
  | cyclophaneRelativeCenter value =>
      cases value <;> simp [localInvert, GeneralRepresentativeEligible]
  | polyhedral value => cases value <;> simp [localInvert, GeneralRepresentativeEligible]
  | fullerene value =>
      cases value with
      | cageHandedness numbering handedness =>
          cases handedness <;> simp [localInvert, GeneralRepresentativeEligible]
      | substituentCIPComplete => simp [localInvert, GeneralRepresentativeEligible]
  | ringAssemblyAxis value => cases value <;> simp [localInvert, GeneralRepresentativeEligible]
  | ringAssemblyCenter value => cases value <;> simp [localInvert, GeneralRepresentativeEligible]

theorem mirror_ne_of_generalRepresentativeEligible
    (descriptor : P93CanonicalDescriptor)
    (eligible : descriptor.GeneralRepresentativeEligible) :
    descriptor.mirror ≠ descriptor := by
  cases descriptor with
  | acyclic value => cases value <;> simp_all [mirror, GeneralRepresentativeEligible]
  | fused value => cases value <;> simp_all [mirror, GeneralRepresentativeEligible]
  | cyclophanePlane value =>
      cases value <;>
        simp_all [mirror, CyclophanePlaneDescriptor.mirror, GeneralRepresentativeEligible]
  | cyclophaneRelativeCenter value =>
      cases value <;> simp_all [GeneralRepresentativeEligible]
  | polyhedral value => cases value <;> simp_all [GeneralRepresentativeEligible]
  | fullerene value =>
      cases value with
      | cageHandedness numbering handedness =>
          cases handedness <;> simp_all [GeneralRepresentativeEligible]
      | substituentCIPComplete => simp_all [GeneralRepresentativeEligible]
  | ringAssemblyAxis value => cases value <;> simp_all [mirror, GeneralRepresentativeEligible]
  | ringAssemblyCenter value => cases value <;> simp_all [mirror, GeneralRepresentativeEligible]

theorem mirror_preferredAtLowest_iff
    (descriptor : P93CanonicalDescriptor)
    (eligible : descriptor.GeneralRepresentativeEligible) :
    descriptor.mirror.PreferredAtLowest ↔ ¬descriptor.PreferredAtLowest := by
  cases descriptor with
  | acyclic value => cases value <;> simp_all [mirror, GeneralRepresentativeEligible, PreferredAtLowest]
  | fused value => cases value <;> simp_all [mirror, GeneralRepresentativeEligible, PreferredAtLowest]
  | cyclophanePlane value =>
      cases value <;>
        simp_all [mirror, CyclophanePlaneDescriptor.mirror,
          GeneralRepresentativeEligible, PreferredAtLowest]
  | cyclophaneRelativeCenter value =>
      cases value <;> simp_all [GeneralRepresentativeEligible]
  | polyhedral value =>
      cases value <;> simp_all [GeneralRepresentativeEligible]
  | fullerene value =>
      cases value with
      | cageHandedness numbering handedness =>
          cases handedness <;>
            simp_all [GeneralRepresentativeEligible]
      | substituentCIPComplete =>
          simp_all [GeneralRepresentativeEligible]
  | ringAssemblyAxis value =>
      cases value <;> simp_all [mirror, GeneralRepresentativeEligible, PreferredAtLowest]
  | ringAssemblyCenter value =>
      cases value <;> simp_all [mirror, GeneralRepresentativeEligible, PreferredAtLowest]

theorem mirrorPreferredAtLowest
    (descriptor : P93CanonicalDescriptor)
    (eligible : descriptor.GeneralRepresentativeEligible)
    (_nonfixed : descriptor.mirror ≠ descriptor) :
    descriptor.mirror.PreferredAtLowest ↔ ¬descriptor.PreferredAtLowest :=
  mirror_preferredAtLowest_iff descriptor eligible

end P93CanonicalDescriptor

/-- A nonempty path-like locator retained from the reviewed name structure.  This carrier does
not assert that a P-1--P-8 parser or constitutional-name generator produced the path. -/
inductive P93CanonicalNameComponentRole where
  | parent
  | prefix
  | functionalClassFirst
  | functionalClassSecond
  deriving DecidableEq, Repr

structure P93CanonicalNameComponent where
  role : P93CanonicalNameComponentRole
  path : List Nat
  deriving DecidableEq, Repr

def P93CanonicalNameComponent.Valid (component : P93CanonicalNameComponent) : Prop :=
  component.path ≠ []

/-- Policy-independent evidence used by P-93.6 after a base name has been frozen. -/
structure P93CanonicalLocatedDescriptor where
  unit : P93RingChainStereogenicUnit
  citation? : Option P93AuthorityCitationToken
  descriptor : P93CanonicalDescriptor
  deriving DecidableEq

/-! ## Exact family and provision partition -/

/-- The twelve source-claim families.  `physical` is shared support; the other eleven partition
the fifty-six descriptor-bearing P-93 provisions. -/
inductive P93ClaimFamily where
  | physical
  | general
  | noncarbon
  | acyclic
  | monocyclic
  | vonBaeyer
  | spiro
  | fused
  | cyclophane
  | fullerene
  | ringAssembly
  | coupled
  deriving DecidableEq, Repr

abbrev P93Clause := Remaining71P93ClosedProductionRow

namespace P93Clause

def all : List P93Clause := Remaining71P93ClosedProductionRow.all

def provision : P93Clause → IUPACNormativeProvision :=
  Remaining71P93ClosedProductionRow.provision

def family : P93Clause → P93ClaimFamily
  | .fullerene _ => .fullerene
  | .noncarbon _ => .noncarbon
  | .general _ => .general
  | .monocyclic _ => .monocyclic
  | .vonBaeyer _ => .vonBaeyer
  | .ringAssembly _ => .ringAssembly
  | .acyclic _ => .acyclic
  | .spiro _ | .spiroNontetrahedral => .spiro
  | .fusedCyclophane .fusedBridgedCIP
  | .fusedCyclophane .cisoidTransoid => .fused
  | .fusedCyclophane .cyclophanePlanes
  | .fusedCyclophane .cyclophaneCenters
  | .fusedCyclophane .cyclophaneDoubleBonds => .cyclophane
  | .coupledRingChain _ => .coupled

@[simp] theorem all_length : all.length = 56 := by
  exact Remaining71P93ClosedProductionRow.all_length

theorem all_nodup : all.Nodup := Remaining71P93ClosedProductionRow.all_nodup

theorem provisions_exact : all.map provision =
    Remaining71P93ClosedProductionRow.provisions := by
  rfl

end P93Clause

/-! ## Closed first-order claim families -/

/-- A fused CIP observation keeps the system, unit, citation, and descriptor in one payload;
these fields cannot be assembled from unrelated package entries. -/
structure P93CanonicalFusedCIPObservation where
  system : P93AuthorityFusedSystem
  unit : P93FusedAuthorityUnit
  citation : P93FusedLocant
  descriptor : FusedUnitDescriptor

/-- A graph path certifying the distance and lower-locant payload of one fusion-pair candidate. -/
structure P93CanonicalFusedNearestCandidate where
  candidate : P93FusedNearestPairCandidate
  shortestPath : List Nat

/-- The relation itself is irreducible source data (the Blue Book does not provide a molecular
coordinate algorithm for it), but its complete finite payload is closed and internally bound. -/
structure P93CanonicalFusedRelationSourceFact where
  firstJunction : CisTrans
  secondJunction : CisTrans
  nearestAtomsRelation : CisTrans
  legacyDescriptor : FusionRelationDescriptor
  preferredDescriptor : FusionRelationDescriptor
  citation : P93FusedLocant

/-- One coherent source record for P-93.5.4.2. -/
structure P93CanonicalFusedRelationObservation where
  system : P93AuthorityFusedSystem
  candidates : List P93CanonicalFusedNearestCandidate
  selected : P93CanonicalFusedNearestCandidate
  relation : P93CanonicalFusedRelationSourceFact

/-- Closed fullerene assignment corpus: every payload used by the production rows shares the
same molecule, spatial realization, selected strict input, and computed assignment. -/
structure P93CanonicalFullereneObservation where
  molecule : RawMolecule
  spatial : SpatialConfiguration
  inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput
  selectedInput : SpatiallyDerivedMolecularFullereneConfigurationInput
  assignment : FullereneConfigurationAssignment
  substituentAssignments : List P93FullereneSubstituentCIPAssignment

/-- Type 4 has no cage-numbering handedness.  Its source payload retains the independently
symmetry-derived substitution test and the complete substituent CIP corpus, but no spatial
numbering/turn witness. -/
structure P93CanonicalFullereneType4Observation where
  molecule : RawMolecule
  input : SymmetryDerivedMolecularFullereneConfigurationInput
  substituentAssignments : List P93FullereneSubstituentCIPAssignment

/-- One independently inventoried stereogenic unit constitutionally owned by a substituent site.
`ownedAtoms` is the complete non-cage connected component reached through `attachmentAtom`; the
CIP assignment list is deliberately absent. -/
structure P93CanonicalFullereneSubstituentInventoryEntry where
  substitutedSite : Nat
  attachmentAtom : Nat
  ownedAtoms : Finset Nat
  unit : P93FullereneSubstituentStereogenicUnit

/-- Only facts transcribed from the printed fullerene example.  In particular this record has no
coordinates, oriented faces, automorphism corpus, or spatial numbering-turn witness. -/
structure P93CanonicalFullerenePrintedObservation where
  molecule : RawMolecule
  cageCarrier : Finset Nat
  substitutionTest : FullereneSubstitutionTest
  chiralSubstituentSites : Finset Nat
  numberingKind? : Option FullereneNumberingKind
  handedness? : Option FullereneHandedness
  unitInventory : List P93CanonicalFullereneSubstituentInventoryEntry
  substituentAssignments : List P93FullereneSubstituentCIPAssignment

inductive P93PhysicalClaim where
  | helix (path : List Nat) (frame : P93AuthorityHelixFrame)
  | plane (members : Finset Nat) (frame : P93AuthorityPlaneFrame)
  | polyhedron (center : Nat) (positions : Finset Nat)
      (geometry : BlueBookP93.Geometry) (frame : P93AuthorityPolyhedralFrame)

inductive P93GeneralClaim where
  | preferredAtLowest (descriptor : P93CanonicalDescriptor)
  | citation (token : P93AuthorityCitationToken) (unit : P93AuthorityPhysicalUnit)
  | descriptor (unit : P93AuthorityPhysicalUnit) (descriptor : P93CanonicalDescriptor)

inductive P93NoncarbonClaim where
  | tetrahedral (center : Nat) (ligands : List Nat)
  | citation (token : P93AuthorityCitationToken) (unit : P93AuthorityPhysicalUnit)
  | descriptor (unit : P93AuthorityPhysicalUnit) (descriptor : P93CanonicalDescriptor)
  | oxideVariant (center oxygen : Nat)
      (family : BlueBookP93.NoncarbonTetrahedra.OxideCenter)
      (bonding : BlueBookP93.NoncarbonTetrahedra.WrittenBondingToOxygen)
  | phosphorusOxo (center oxygen : Nat)
      (family : BlueBookP93.NoncarbonTetrahedra.PhosphorusOxoFamily)
      (writtenAsDouble : Bool)
      (charges : BlueBookP93.NoncarbonTetrahedra.FormalChargeArrangement)
  | chalcogenOxo (center oxygen : Nat)
      (family : BlueBookP93.NoncarbonTetrahedra.ChalcogenOxoFamily)
      (writtenAsDouble : Bool)
      (charges : BlueBookP93.NoncarbonTetrahedra.FormalChargeArrangement)

inductive P93AcyclicClaim where
  | citation (token : P93AuthorityCitationToken) (unit : P93AuthorityPhysicalUnit)
  | component (component : P93CanonicalNameComponent) (unit : P93AuthorityPhysicalUnit)
  | unit (unit : P93AuthorityPhysicalUnit)
  | unitKind (unit : P93AuthorityPhysicalUnit) (kind : UnitKind)
  | descriptor (unit : P93AuthorityPhysicalUnit)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | carbonDoubleBondContext (unit : P93AuthorityPhysicalUnit)
      (context : CarbonDoubleBondContext)
  | singleCenterNaming (unit : P93AuthorityPhysicalUnit)
      (citation? : Option P93AuthorityCitationToken) (needsLocant isotopePresent : Bool)
      (affixes : List AffixKind)
  | oddCumuleneGeometry (path : List Nat) (geometry : OddCumuleneTerminalGeometry)
  | multipleCenterDescriptors
      (assignments : List
        (P93AuthorityPhysicalUnit × UnitKind × BlueBookP93.Acyclic.Descriptor))
  | multipleDoubleBondCollection (bonds : List P93AuthorityPhysicalUnit)
  | multipleDoubleBondDescriptors
      (assignments : List
        (P93AuthorityPhysicalUnit × UnitKind × BlueBookP93.Acyclic.Descriptor))
  | numberingCompetition
      (units : List (P93AuthorityPhysicalUnit × Option P93AuthorityCitationToken))
      (competition : P93AcyclicNumberingCompetition)

inductive P93MonocyclicClaim where
  | citation (token : P93AuthorityCitationToken) (unit : P93AuthorityPhysicalUnit)
  | ring (atoms : List Nat)
  | unitInRing (atoms : List Nat) (unit : P93AuthorityPhysicalUnit)
  | generalDescriptor (unit : P93AuthorityPhysicalUnit)
      (descriptor : P93CanonicalDescriptor)
  | generalNotation (unit : P93AuthorityPhysicalUnit)
      (knowledge : ConfigurationKnowledge) (notationValue : MonocycleNotation)
  | center (center : Nat) (kind : UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
      (knowledge : ConfigurationKnowledge) (notationValue : MonocycleNotation)
  | achiralCenter (center : Nat)
  | ringPlane (atoms : List Nat) (first second : Nat) (plane : RingPlaneObservation)
  | ringSide (atoms : List Nat) (ligand : Nat) (side : RingSide)
  | rctCandidate (atoms : List Nat) (ringPosition substituent : Nat)
      (citation : P93AuthorityCitationToken) (namedAsSuffix : Bool) (priority : Nat)
  | unsaturation (atoms : List Nat) (unit : P93AuthorityPhysicalUnit)
      (topology : CyclicUnsaturationTopology) (doubleBondCount : Nat)
  | seniorGeometry (unit : P93AuthorityPhysicalUnit)
      (geometry : MonocyclicSeniorLigandGeometry)
  | chiralCycloalkene (unit : P93AuthorityPhysicalUnit)
      (descriptor : ChiralCycloalkeneDescriptor) (contextIsPIN : Bool)
  | exocyclicSystem (atoms : List Nat) (unit : P93AuthorityPhysicalUnit)
      (doubleBondCount : Nat) (oppositePositions : Bool)
  | exocyclicNaming (unit : P93AuthorityPhysicalUnit) (contextIsPIN : Bool)
      (method : ExocyclicNamingMethod) (treatment : ExocyclicSystemTreatment)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor)

inductive P93VonBaeyerClaim where
  | system (system : P93AuthorityVonBaeyerSystem)
  | unit (system : P93AuthorityVonBaeyerSystem) (unit : P93AuthorityPhysicalUnit)
  | citation (token : P93AuthorityCitationToken) (unit : P93AuthorityPhysicalUnit)
  | center (center : Nat) (kind : UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
      (knowledge : ConfigurationKnowledge) (notationValue : MonocycleNotation)
  | bridgeAttachment (system : P93AuthorityVonBaeyerSystem)
      (attachment substituent : Nat) (kind : BridgeAttachment)
  | bridgeheadSide (system : P93AuthorityVonBaeyerSystem)
      (bridgehead ligand : Nat) (side : RingSide)
  | relativeNotation (system : P93AuthorityVonBaeyerSystem)
      (contextIsPIN : Bool) (notationValue : BridgeheadRelativeNotation)
  | largerThanBicyclo333 (system : P93AuthorityVonBaeyerSystem) (value : Bool)
  | seniorGeometry (unit : P93AuthorityPhysicalUnit)
      (geometry : MonocyclicSeniorLigandGeometry)
  | doubleBondNaming (system : P93AuthorityVonBaeyerSystem)
      (unit : P93AuthorityPhysicalUnit) (contextIsPIN larger : Bool)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor)
  | includedCumuleneNumbering (system : P93AuthorityVonBaeyerSystem)
      (path : List Nat) (citation : P93AuthorityCitationToken)
  | includedCumuleneContext (system : P93AuthorityVonBaeyerSystem)
      (unit : P93AuthorityPhysicalUnit) (context : NomenclatureContext)

inductive P93SpiroClaim where
  | system (system : P93AuthoritySpiroSystem)
  | unit (system : P93AuthoritySpiroSystem) (unit : P93AuthorityPhysicalUnit)
  | citation (token : P93AuthorityCitationToken) (unit : P93AuthorityPhysicalUnit)
  | pattern (system : P93AuthoritySpiroSystem) (pattern : SpiroLigandPattern)
  | centerDescriptor (system : P93AuthoritySpiroSystem) (pattern : SpiroLigandPattern)
      (family : SpiroDescriptorFamily) (descriptor : BlueBookP93.Acyclic.Descriptor)
  | xababOrder (system : P93AuthoritySpiroSystem) (order : XababOccurrenceOrder)
  | doubleBondRing (system : P93AuthoritySpiroSystem)
      (unit : P93AuthorityPhysicalUnit) (ring : List Nat)
  | doubleBondGeometry (unit : P93AuthorityPhysicalUnit)
      (geometry : MonocyclicSeniorLigandGeometry)
  | doubleBondNaming (system : P93AuthoritySpiroSystem)
      (unit : P93AuthorityPhysicalUnit) (context : NomenclatureContext)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor)
  | coordination (system : P93AuthoritySpiroSystem) (positions : Finset Nat)
      (coordination : SpiroCenterCoordination)
  | polyhedralDescriptor (system : P93AuthoritySpiroSystem) (positions : Finset Nat)
      (knowledge : ConfigurationKnowledge) (descriptor : PolyhedralChiralitySymbol)
  | axialCenterDescriptor (system : P93AuthoritySpiroSystem)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | axialDescriptor (system : P93AuthoritySpiroSystem)
      (descriptor : BlueBookP93.Acyclic.Descriptor)

inductive P93FusedClaim where
  | cipObservation (observation : P93CanonicalFusedCIPObservation)
  | relationObservation (observation : P93CanonicalFusedRelationObservation)
  | system (system : P93AuthorityFusedSystem)
  | unit (system : P93AuthorityFusedSystem) (unit : P93FusedAuthorityUnit)
  | citation (token : P93FusedLocant) (unit : P93FusedAuthorityUnit)
  | axis (system : P93AuthorityFusedSystem) (path : List Nat)
  | unitDescriptor (system : P93AuthorityFusedSystem) (unit : P93FusedAuthorityUnit)
      (descriptor : FusedUnitDescriptor)
  | fusionPair (system : P93AuthorityFusedSystem) (first second : Nat)
  | nearestCandidate (system : P93AuthorityFusedSystem) (first second : Nat)
      (distance : Nat) (lowerLocant : P93FusedLocant)
  | fusionCitation (system : P93AuthorityFusedSystem) (first second : Nat)
      (citation : P93FusedLocant)
  | fusionRelation (system : P93AuthorityFusedSystem) (first second : Nat)
      (firstJunction secondJunction : CisTrans) (relation : FusionRelationDescriptor)

inductive P93CyclophaneClaim where
  | system (system : P93AuthorityCyclophaneSystem)
  | unit (system : P93AuthorityCyclophaneSystem) (unit : P93AuthorityPhysicalUnit)
  | citation (token : P93AuthorityCitationToken) (unit : P93AuthorityPhysicalUnit)
  | planeReference (system : P93AuthorityCyclophaneSystem)
      (unit : P93AuthorityPhysicalUnit) (reference : CyclophanePlaneReference)
  | planeOrder (system : P93AuthorityCyclophaneSystem)
      (unit : P93AuthorityPhysicalUnit) (high low : Nat)
  | planeDescriptor (system : P93AuthorityCyclophaneSystem)
      (unit : P93AuthorityPhysicalUnit) (context : NomenclatureContext)
      (descriptor : CyclophanePlaneDescriptor)
  | center (system : P93AuthorityCyclophaneSystem) (center : Nat)
      (kind : UnitKind) (context : NomenclatureContext)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | rctEligible (system : P93AuthorityCyclophaneSystem) (center : Nat)
  | rctCandidate (system : P93AuthorityCyclophaneSystem) (center : Nat)
      (citation : P93AuthorityCitationToken) (namedAsSuffix : Bool) (priority : Nat)
  | rctSide (system : P93AuthorityCyclophaneSystem) (center : Nat) (side : RingSide)
  | doubleBondRing (system : P93AuthorityCyclophaneSystem)
      (unit : P93AuthorityPhysicalUnit) (ring phaneRing : List Nat)
  | doubleBondGeometry (unit : P93AuthorityPhysicalUnit)
      (geometry : MonocyclicSeniorLigandGeometry)
  | carbonDoubleBondContext (unit : P93AuthorityPhysicalUnit)
      (context : CarbonDoubleBondContext)
  | doubleBondNaming (system : P93AuthorityCyclophaneSystem)
      (unit : P93AuthorityPhysicalUnit) (context : NomenclatureContext)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor)

inductive P93FullereneClaim where
  | methodologyDecisionRule
  | printedObservation (observation : P93CanonicalFullerenePrintedObservation)
  | printedSuperimposedObservation (observation : P93CanonicalFullerenePrintedObservation)
  | rawMolecule (molecule : RawMolecule)
  | inputFamily (molecule : RawMolecule)
      (inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput)
  | substitutionEvidence (molecule : RawMolecule)
      (input : MolecularFullereneConfigurationInput)
      (evidence : MolecularFullereneSubstitutionEvidence)
  | preferredNumbering (molecule : RawMolecule)
      (input : MolecularFullereneConfigurationInput)
      (evidence : MolecularFullereneNumberingEvidence)
  | originalChirality (molecule : RawMolecule)
      (input : MolecularFullereneConfigurationInput)
      (evidence : MolecularFullereneSubstitutionEvidence) (value : Bool)
  | substituentUnit (molecule : RawMolecule)
      (input : MolecularFullereneConfigurationInput)
      (evidence : MolecularFullereneSubstitutionEvidence) (site : Nat)
      (unit : P93FullereneSubstituentStereogenicUnit)
  | substituentCitation (molecule : RawMolecule)
      (input : MolecularFullereneConfigurationInput) (site : Nat)
      (citation : P93AuthorityCitationToken)
      (unit : P93FullereneSubstituentStereogenicUnit)
  | substituentDescriptor (molecule : RawMolecule)
      (input : MolecularFullereneConfigurationInput) (site : Nat)
      (unit : P93FullereneSubstituentStereogenicUnit)
      (descriptor : P93FullereneSubstituentCIPDescriptor)

inductive P93RingAssemblyClaim where
  | assembly (assembly : P93AuthorityRingAssembly)
  | normalization (result : CertifiedChemistryNormalizationResult)
  | axisEligible (assembly : P93AuthorityRingAssembly) (junction : P93RingAssemblyJunction)
  | axisCitation (assembly : P93AuthorityRingAssembly) (junction : P93RingAssemblyJunction)
      (citation : P93AuthorityCitationToken)
  | axisDescriptors (assembly : P93AuthorityRingAssembly) (junction : P93RingAssemblyJunction)
      (preferred general : RingAssemblyAxisDescriptor)
  | centerEligible (assembly : P93AuthorityRingAssembly) (center : Nat)
  | centerCitation (assembly : P93AuthorityRingAssembly) (center : Nat)
      (citation : P93AuthorityCitationToken)
  | centerDescriptor (assembly : P93AuthorityRingAssembly) (center : Nat)
      (descriptor : RingAssemblyCenterDescriptor)
  | centerGeneralEquivalent (assembly : P93AuthorityRingAssembly) (center : Nat)
      (preferred general : RingAssemblyCenterDescriptor)
  | doubleBondStereogenic (assembly : P93AuthorityRingAssembly)
      (ringIndex first second : Nat)
  | doubleBondNeedsSpecification (assembly : P93AuthorityRingAssembly)
      (ringIndex first second : Nat)
  | doubleBondCitation (assembly : P93AuthorityRingAssembly)
      (ringIndex first second : Nat) (citation : P93AuthorityCitationToken)
  | doubleBondDescriptor (assembly : P93AuthorityRingAssembly)
      (ringIndex first second : Nat) (descriptor : BlueBookP93.Acyclic.Descriptor)

inductive P93CoupledClaim where
  | baseName (name : P93RingChainBaseName)
      (certificate : P93RingChainReviewedBaseNameCertificate)
  | eligibleUnit (name : P93RingChainBaseName) (unit : P93RingChainStereogenicUnit)
  | evidenceBelongs (name : P93RingChainBaseName)
      (evidence : P93CanonicalLocatedDescriptor)
  | citation (name : P93RingChainBaseName) (citation : P93AuthorityCitationToken)
      (unit : P93RingChainStereogenicUnit)
  | repeatedComponents (name : P93RingChainBaseName)
      (components : List P93RingChainRepeatedComponent)
  | multiplicativeDecision (name : P93RingChainBaseName) (selected : Bool)

inductive P93SourceClaim where
  | physical (claim : P93PhysicalClaim)
  | general (claim : P93GeneralClaim)
  | noncarbon (claim : P93NoncarbonClaim)
  | acyclic (claim : P93AcyclicClaim)
  | monocyclic (claim : P93MonocyclicClaim)
  | vonBaeyer (claim : P93VonBaeyerClaim)
  | spiro (claim : P93SpiroClaim)
  | fused (claim : P93FusedClaim)
  | cyclophane (claim : P93CyclophaneClaim)
  | fullerene (claim : P93FullereneClaim)
  | ringAssembly (claim : P93RingAssemblyClaim)
  | coupled (claim : P93CoupledClaim)

namespace P93SourceClaim

def family : P93SourceClaim → P93ClaimFamily
  | .physical _ => .physical
  | .general _ => .general
  | .noncarbon _ => .noncarbon
  | .acyclic _ => .acyclic
  | .monocyclic _ => .monocyclic
  | .vonBaeyer _ => .vonBaeyer
  | .spiro _ => .spiro
  | .fused _ => .fused
  | .cyclophane _ => .cyclophane
  | .fullerene _ => .fullerene
  | .ringAssembly _ => .ringAssembly
  | .coupled _ => .coupled

/-- Shared physical claims may support exactly the families whose legacy policies contain the
shared physical-observation boundary.  The constructors are explicit; there is no fallback case. -/
inductive PhysicalSupports : P93ClaimFamily → Prop where
  | general : PhysicalSupports .general
  | acyclic : PhysicalSupports .acyclic
  | monocyclic : PhysicalSupports .monocyclic
  | vonBaeyer : PhysicalSupports .vonBaeyer
  | spiro : PhysicalSupports .spiro
  | fused : PhysicalSupports .fused
  | cyclophane : PhysicalSupports .cyclophane
  | fullerene : PhysicalSupports .fullerene
  | ringAssembly : PhysicalSupports .ringAssembly
  | coupled : PhysicalSupports .coupled

end P93SourceClaim

/-! ## Qualitative physical-support projection -/

/-- Only these three unit forms require an audited qualitative observation in addition to their
mechanical source envelope. -/
def P93AuthorityPhysicalUnit.qualitativeOnly
    (unit : P93AuthorityPhysicalUnit) : List P93AuthorityPhysicalUnit :=
  match unit with
  | .plane _ | .helix _ | .polyhedron _ _ => [unit]
  | _ => []

def P93PhysicalClaim.unit : P93PhysicalClaim → P93AuthorityPhysicalUnit
  | .helix path _ => .helix path
  | .plane members _ => .plane members
  | .polyhedron center positions _ _ => .polyhedron center positions

def P93FusedAuthorityUnit.physicalUnits : P93FusedAuthorityUnit → List P93AuthorityPhysicalUnit
  | .physical unit => [unit]
  | .fusedAxis _ => []

def P93GeneralClaim.physicalUnits : P93GeneralClaim → List P93AuthorityPhysicalUnit
  | .preferredAtLowest _ => []
  | .citation _ unit | .descriptor unit _ => [unit]

def P93NoncarbonClaim.physicalUnits : P93NoncarbonClaim → List P93AuthorityPhysicalUnit
  | .citation _ unit | .descriptor unit _ => [unit]
  | _ => []

def P93AcyclicClaim.physicalUnits : P93AcyclicClaim → List P93AuthorityPhysicalUnit
  | .citation _ physicalUnit => [physicalUnit]
  | .component _ physicalUnit => [physicalUnit]
  | .unit physicalUnit => [physicalUnit]
  | .unitKind physicalUnit _ => [physicalUnit]
  | .descriptor physicalUnit _ => [physicalUnit]
  | .carbonDoubleBondContext physicalUnit _ => [physicalUnit]
  | .singleCenterNaming physicalUnit _ _ _ _ => [physicalUnit]
  | .multipleCenterDescriptors assignments =>
      assignments.map fun assignment => assignment.1
  | .oddCumuleneGeometry path _ => [.axis path]
  | .multipleDoubleBondCollection bonds => bonds
  | .multipleDoubleBondDescriptors assignments =>
      assignments.map fun assignment => assignment.1
  | .numberingCompetition units _ => units.map fun assignment => assignment.1

def P93MonocyclicClaim.physicalUnits : P93MonocyclicClaim → List P93AuthorityPhysicalUnit
  | .citation _ physicalUnit => [physicalUnit]
  | .unitInRing _ physicalUnit => [physicalUnit]
  | .generalDescriptor physicalUnit _ => [physicalUnit]
  | .generalNotation physicalUnit _ _ => [physicalUnit]
  | .unsaturation _ physicalUnit _ _ => [physicalUnit]
  | .seniorGeometry physicalUnit _ => [physicalUnit]
  | .chiralCycloalkene physicalUnit _ _ => [physicalUnit]
  | .exocyclicSystem _ physicalUnit _ _ => [physicalUnit]
  | .exocyclicNaming physicalUnit _ _ _ _ => [physicalUnit]
  | .center centerAtom _ _ _ _ => [.atomCenter centerAtom]
  | .achiralCenter centerAtom => [.atomCenter centerAtom]
  | _ => []

def P93VonBaeyerClaim.physicalUnits : P93VonBaeyerClaim → List P93AuthorityPhysicalUnit
  | .unit _ physicalUnit => [physicalUnit]
  | .citation _ physicalUnit => [physicalUnit]
  | .seniorGeometry physicalUnit _ => [physicalUnit]
  | .doubleBondNaming _ physicalUnit _ _ _ => [physicalUnit]
  | .includedCumuleneContext _ physicalUnit _ => [physicalUnit]
  | .center centerAtom _ _ _ _ => [.atomCenter centerAtom]
  | .includedCumuleneNumbering _ path _ => [.axis path]
  | _ => []

def P93SpiroClaim.physicalUnits : P93SpiroClaim → List P93AuthorityPhysicalUnit
  | .unit _ physicalUnit => [physicalUnit]
  | .citation _ physicalUnit => [physicalUnit]
  | .doubleBondRing _ physicalUnit _ => [physicalUnit]
  | .doubleBondGeometry physicalUnit _ => [physicalUnit]
  | .doubleBondNaming _ physicalUnit _ _ => [physicalUnit]
  | .coordination spiroSystem positions _ =>
      [.polyhedron spiroSystem.center positions]
  | .polyhedralDescriptor spiroSystem positions _ _ =>
      [.polyhedron spiroSystem.center positions]
  | .centerDescriptor spiroSystem _ _ _ => [.atomCenter spiroSystem.center]
  | .axialCenterDescriptor spiroSystem _ => [.atomCenter spiroSystem.center]
  | .axialDescriptor spiroSystem _ => [.atomCenter spiroSystem.center]
  | _ => []

def P93FusedClaim.physicalUnits : P93FusedClaim → List P93AuthorityPhysicalUnit
  | .cipObservation observationValue => observationValue.unit.physicalUnits
  | .unit _ fusedUnit => fusedUnit.physicalUnits
  | .citation _ fusedUnit => fusedUnit.physicalUnits
  | .unitDescriptor _ fusedUnit _ => fusedUnit.physicalUnits
  | _ => []

def P93CyclophaneClaim.physicalUnits : P93CyclophaneClaim → List P93AuthorityPhysicalUnit
  | .unit _ physicalUnit => [physicalUnit]
  | .citation _ physicalUnit => [physicalUnit]
  | .doubleBondRing _ physicalUnit _ _ => [physicalUnit]
  | .doubleBondGeometry physicalUnit _ => [physicalUnit]
  | .carbonDoubleBondContext physicalUnit _ => [physicalUnit]
  | .doubleBondNaming _ physicalUnit _ _ => [physicalUnit]
  | .center _ centerAtom _ _ _ => [.atomCenter centerAtom]
  | .rctEligible _ centerAtom => [.atomCenter centerAtom]
  | .rctCandidate _ centerAtom _ _ _ => [.atomCenter centerAtom]
  | .rctSide _ centerAtom _ => [.atomCenter centerAtom]
  | _ => []

def P93CanonicalFullereneObservation.physicalUnits
    (observation : P93CanonicalFullereneObservation) : List P93AuthorityPhysicalUnit :=
  observation.substituentAssignments.map fun assignment => assignment.unit.toPhysicalUnit

def P93CanonicalFullereneType4Observation.physicalUnits
    (observation : P93CanonicalFullereneType4Observation) : List P93AuthorityPhysicalUnit :=
  observation.substituentAssignments.map fun assignment => assignment.unit.toPhysicalUnit

def P93CanonicalFullerenePrintedObservation.physicalUnits
    (observation : P93CanonicalFullerenePrintedObservation) : List P93AuthorityPhysicalUnit :=
  observation.unitInventory.map fun entry => entry.unit.toPhysicalUnit

def P93FullereneClaim.physicalUnits : P93FullereneClaim → List P93AuthorityPhysicalUnit
  | .printedObservation observationValue => observationValue.physicalUnits
  | .printedSuperimposedObservation observationValue => observationValue.physicalUnits
  | .substituentUnit _ _ _ _ fullereneUnit => [fullereneUnit.toPhysicalUnit]
  | .substituentCitation _ _ _ _ fullereneUnit => [fullereneUnit.toPhysicalUnit]
  | .substituentDescriptor _ _ _ fullereneUnit _ => [fullereneUnit.toPhysicalUnit]
  | _ => []

def P93RingChainStereogenicUnit.physicalUnits :
    P93RingChainStereogenicUnit → List P93AuthorityPhysicalUnit
  | .center centerAtom => [.atomCenter centerAtom]
  | .doubleBond first second | .bondAxis first second => [.bond first second]
  | .cumuleneAxis path => [.axis path]
  | .fusedAxis _ => []
  | .plane members => [.plane members]
  | .helix path => [.helix path]
  | .polyhedron centerAtom positions => [.polyhedron centerAtom positions]

def P93CoupledClaim.physicalUnits : P93CoupledClaim → List P93AuthorityPhysicalUnit
  | .eligibleUnit _ ringChainUnit => ringChainUnit.physicalUnits
  | .citation _ _ ringChainUnit => ringChainUnit.physicalUnits
  | .evidenceBelongs _ evidence => evidence.unit.physicalUnits
  | _ => []



def P93SourceClaim.physicalUnits : P93SourceClaim → List P93AuthorityPhysicalUnit
  | .physical claim => [claim.unit]
  | .general claim => claim.physicalUnits
  | .noncarbon claim => claim.physicalUnits
  | .acyclic claim => claim.physicalUnits
  | .monocyclic claim => claim.physicalUnits
  | .vonBaeyer claim => claim.physicalUnits
  | .spiro claim => claim.physicalUnits
  | .fused claim => claim.physicalUnits
  | .cyclophane claim => claim.physicalUnits
  | .fullerene claim => claim.physicalUnits
  | .ringAssembly _ => []
  | .coupled claim => claim.physicalUnits

def P93SourceClaim.qualitativePhysicalUnits
    (claim : P93SourceClaim) : List P93AuthorityPhysicalUnit :=
  match claim with
  | .cyclophane (.unit _ (.plane _))
  | .cyclophane (.citation _ (.plane _)) => []
  | _ => claim.physicalUnits.flatMap P93AuthorityPhysicalUnit.qualitativeOnly

/-! ## Clause-indexed semantic requirements -/

/-- Payload-free tags for the irreducible source fields.  They are typed data, not predicates;
the finite `all` list below is the closed grammar quantified by clause completeness. -/
inductive P93SourceField where
  | generalPreferred | generalCitation | generalDescriptor
  | noncarbonTetrahedral | noncarbonCitation | noncarbonDescriptor
  | noncarbonOxide | noncarbonPhosphorusOxo | noncarbonChalcogenOxo
  | acyclicCitation | acyclicComponent | acyclicUnit | acyclicUnitKind
  | acyclicDescriptor | acyclicCarbonContext | acyclicSingleCenterNaming
  | acyclicOddCumuleneGeometry | acyclicMultipleCenterDescriptors
  | acyclicMultipleDoubleBondCollection | acyclicMultipleDoubleBondDescriptors
  | acyclicNumberingCompetition
  | monocyclicCitation | monocyclicRing | monocyclicUnitInRing
  | monocyclicGeneralDescriptor | monocyclicCenter | monocyclicAchiralCenter
  | monocyclicRingPlane | monocyclicRingSide | monocyclicRCTCandidate
  | monocyclicUnsaturation | monocyclicSeniorGeometry | monocyclicChiralCycloalkene
  | monocyclicExocyclicSystem | monocyclicExocyclicNaming
  | vonBaeyerSystem | vonBaeyerUnit | vonBaeyerCitation | vonBaeyerCenter
  | vonBaeyerBridgeAttachment | vonBaeyerBridgeheadSide | vonBaeyerRelativeNotation
  | vonBaeyerLargerThan333 | vonBaeyerSeniorGeometry | vonBaeyerDoubleBondNaming
  | vonBaeyerCumuleneNumbering | vonBaeyerCumuleneContext
  | spiroSystem | spiroUnit | spiroCitation | spiroPattern | spiroCenterDescriptor
  | spiroXababOrder | spiroDoubleBondRing | spiroDoubleBondGeometry
  | spiroDoubleBondNaming | spiroCoordination | spiroPolyhedralDescriptor
  | spiroAxialCenterDescriptor | spiroAxialDescriptor
  | fusedCIPObservation | fusedRelationObservation
  | cyclophaneSystem | cyclophaneUnit | cyclophaneCitation
  | cyclophanePlaneReference | cyclophanePlaneOrder | cyclophanePlaneDescriptor
  | cyclophaneCenter | cyclophaneRCTEligible | cyclophaneRCTCandidate
  | cyclophaneRCTSide | cyclophaneDoubleBondRing | cyclophaneDoubleBondGeometry
  | cyclophaneCarbonContext | cyclophaneDoubleBondNaming
  | fullereneObservation | fullereneSuperimposedObservation
  | ringAssembly | ringNormalization | ringAxisEligible | ringAxisCitation | ringAxisDescriptors
  | ringCenterEligible | ringCenterCitation | ringCenterDescriptor
  | ringCenterGeneralEquivalent | ringDoubleBondStereogenic
  | ringDoubleBondNeedsSpecification | ringDoubleBondCitation | ringDoubleBondDescriptor
  | coupledBaseName | coupledEligibleUnit | coupledEvidenceBelongs | coupledCitation
  | coupledRepeatedComponents | coupledMultiplicativeDecision
  deriving DecidableEq, Repr

namespace P93SourceField

def all : List P93SourceField :=
  [ .generalPreferred, .generalCitation, .generalDescriptor,
    .noncarbonTetrahedral, .noncarbonCitation, .noncarbonDescriptor,
    .noncarbonOxide, .noncarbonPhosphorusOxo, .noncarbonChalcogenOxo,
    .acyclicCitation, .acyclicComponent, .acyclicUnit, .acyclicUnitKind,
    .acyclicDescriptor, .acyclicCarbonContext, .acyclicSingleCenterNaming,
    .acyclicOddCumuleneGeometry, .acyclicMultipleCenterDescriptors,
    .acyclicMultipleDoubleBondCollection, .acyclicMultipleDoubleBondDescriptors,
    .acyclicNumberingCompetition,
    .monocyclicCitation, .monocyclicRing, .monocyclicUnitInRing,
    .monocyclicGeneralDescriptor, .monocyclicCenter, .monocyclicAchiralCenter,
    .monocyclicRingPlane, .monocyclicRingSide, .monocyclicRCTCandidate,
    .monocyclicUnsaturation, .monocyclicSeniorGeometry, .monocyclicChiralCycloalkene,
    .monocyclicExocyclicSystem, .monocyclicExocyclicNaming,
    .vonBaeyerSystem, .vonBaeyerUnit, .vonBaeyerCitation, .vonBaeyerCenter,
    .vonBaeyerBridgeAttachment, .vonBaeyerBridgeheadSide, .vonBaeyerRelativeNotation,
    .vonBaeyerLargerThan333, .vonBaeyerSeniorGeometry, .vonBaeyerDoubleBondNaming,
    .vonBaeyerCumuleneNumbering, .vonBaeyerCumuleneContext,
    .spiroSystem, .spiroUnit, .spiroCitation, .spiroPattern, .spiroCenterDescriptor,
    .spiroXababOrder, .spiroDoubleBondRing, .spiroDoubleBondGeometry,
    .spiroDoubleBondNaming, .spiroCoordination, .spiroPolyhedralDescriptor,
    .spiroAxialCenterDescriptor, .spiroAxialDescriptor,
    .fusedCIPObservation, .fusedRelationObservation,
    .cyclophaneSystem, .cyclophaneUnit, .cyclophaneCitation,
    .cyclophanePlaneReference, .cyclophanePlaneOrder, .cyclophanePlaneDescriptor,
    .cyclophaneCenter, .cyclophaneRCTEligible, .cyclophaneRCTCandidate,
    .cyclophaneRCTSide, .cyclophaneDoubleBondRing, .cyclophaneDoubleBondGeometry,
    .cyclophaneCarbonContext, .cyclophaneDoubleBondNaming,
    .fullereneObservation, .fullereneSuperimposedObservation,
    .ringAssembly, .ringNormalization, .ringAxisEligible, .ringAxisCitation,
    .ringAxisDescriptors,
    .ringCenterEligible, .ringCenterCitation, .ringCenterDescriptor,
    .ringCenterGeneralEquivalent, .ringDoubleBondStereogenic,
    .ringDoubleBondNeedsSpecification, .ringDoubleBondCitation, .ringDoubleBondDescriptor,
    .coupledBaseName, .coupledEligibleUnit, .coupledEvidenceBelongs, .coupledCitation,
    .coupledRepeatedComponents, .coupledMultiplicativeDecision ]

end P93SourceField

/-- Semantic-field erasure.  `none` is deliberate: physical claims and the legacy granular
fused/fullerene constructors are support-only.  Only the coherent fused/fullerene observation
constructors project a semantic field and therefore only they can occur in clause coverage. -/
def P93SourceClaim.field? : P93SourceClaim → Option P93SourceField
  | .physical _ => none
  | .general (.preferredAtLowest _) => some .generalPreferred
  | .general (.citation _ _) => some .generalCitation
  | .general (.descriptor _ _) => some .generalDescriptor
  | .noncarbon (.tetrahedral _ _) => some .noncarbonTetrahedral
  | .noncarbon (.citation _ _) => some .noncarbonCitation
  | .noncarbon (.descriptor _ _) => some .noncarbonDescriptor
  | .noncarbon (.oxideVariant _ _ _ _) => some .noncarbonOxide
  | .noncarbon (.phosphorusOxo _ _ _ _ _) => some .noncarbonPhosphorusOxo
  | .noncarbon (.chalcogenOxo _ _ _ _ _) => some .noncarbonChalcogenOxo
  | .acyclic (.citation _ _) => some .acyclicCitation
  | .acyclic (.component _ _) => some .acyclicComponent
  | .acyclic (.unit _) => some .acyclicUnit
  | .acyclic (.unitKind _ _) => some .acyclicUnitKind
  | .acyclic (.descriptor _ _) => some .acyclicDescriptor
  | .acyclic (.carbonDoubleBondContext _ _) => some .acyclicCarbonContext
  | .acyclic (.singleCenterNaming _ _ _ _ _) => some .acyclicSingleCenterNaming
  | .acyclic (.oddCumuleneGeometry _ _) => some .acyclicOddCumuleneGeometry
  | .acyclic (.multipleCenterDescriptors _) => some .acyclicMultipleCenterDescriptors
  | .acyclic (.multipleDoubleBondCollection _) => some .acyclicMultipleDoubleBondCollection
  | .acyclic (.multipleDoubleBondDescriptors _) => some .acyclicMultipleDoubleBondDescriptors
  | .acyclic (.numberingCompetition _ _) => some .acyclicNumberingCompetition
  | .monocyclic (.citation _ _) => some .monocyclicCitation
  | .monocyclic (.ring _) => some .monocyclicRing
  | .monocyclic (.unitInRing _ _) => some .monocyclicUnitInRing
  | .monocyclic (.generalDescriptor _ _) => some .monocyclicGeneralDescriptor
  | .monocyclic (.generalNotation _ _ _) => some .monocyclicGeneralDescriptor
  | .monocyclic (.center _ _ _ _ _) => some .monocyclicCenter
  | .monocyclic (.achiralCenter _) => some .monocyclicAchiralCenter
  | .monocyclic (.ringPlane _ _ _ _) => some .monocyclicRingPlane
  | .monocyclic (.ringSide _ _ _) => some .monocyclicRingSide
  | .monocyclic (.rctCandidate _ _ _ _ _ _) => some .monocyclicRCTCandidate
  | .monocyclic (.unsaturation _ _ _ _) => some .monocyclicUnsaturation
  | .monocyclic (.seniorGeometry _ _) => some .monocyclicSeniorGeometry
  | .monocyclic (.chiralCycloalkene _ _ _) => some .monocyclicChiralCycloalkene
  | .monocyclic (.exocyclicSystem _ _ _ _) => some .monocyclicExocyclicSystem
  | .monocyclic (.exocyclicNaming _ _ _ _ _) => some .monocyclicExocyclicNaming
  | .vonBaeyer (.system _) => some .vonBaeyerSystem
  | .vonBaeyer (.unit _ _) => some .vonBaeyerUnit
  | .vonBaeyer (.citation _ _) => some .vonBaeyerCitation
  | .vonBaeyer (.center _ _ _ _ _) => some .vonBaeyerCenter
  | .vonBaeyer (.bridgeAttachment _ _ _ _) => some .vonBaeyerBridgeAttachment
  | .vonBaeyer (.bridgeheadSide _ _ _ _) => some .vonBaeyerBridgeheadSide
  | .vonBaeyer (.relativeNotation _ _ _) => some .vonBaeyerRelativeNotation
  | .vonBaeyer (.largerThanBicyclo333 _ _) => some .vonBaeyerLargerThan333
  | .vonBaeyer (.seniorGeometry _ _) => some .vonBaeyerSeniorGeometry
  | .vonBaeyer (.doubleBondNaming _ _ _ _ _) => some .vonBaeyerDoubleBondNaming
  | .vonBaeyer (.includedCumuleneNumbering _ _ _) => some .vonBaeyerCumuleneNumbering
  | .vonBaeyer (.includedCumuleneContext _ _ _) => some .vonBaeyerCumuleneContext
  | .spiro (.system _) => some .spiroSystem
  | .spiro (.unit _ _) => some .spiroUnit
  | .spiro (.citation _ _) => some .spiroCitation
  | .spiro (.pattern _ _) => some .spiroPattern
  | .spiro (.centerDescriptor _ _ _ _) => some .spiroCenterDescriptor
  | .spiro (.xababOrder _ _) => some .spiroXababOrder
  | .spiro (.doubleBondRing _ _ _) => some .spiroDoubleBondRing
  | .spiro (.doubleBondGeometry _ _) => some .spiroDoubleBondGeometry
  | .spiro (.doubleBondNaming _ _ _ _) => some .spiroDoubleBondNaming
  | .spiro (.coordination _ _ _) => some .spiroCoordination
  | .spiro (.polyhedralDescriptor _ _ _ _) => some .spiroPolyhedralDescriptor
  | .spiro (.axialCenterDescriptor _ _) => some .spiroAxialCenterDescriptor
  | .spiro (.axialDescriptor _ _) => some .spiroAxialDescriptor
  | .fused (.cipObservation _) => some .fusedCIPObservation
  | .fused (.relationObservation _) => some .fusedRelationObservation
  | .fused _ => none
  | .cyclophane (.system _) => some .cyclophaneSystem
  | .cyclophane (.unit _ _) => some .cyclophaneUnit
  | .cyclophane (.citation _ _) => some .cyclophaneCitation
  | .cyclophane (.planeReference _ _ _) => some .cyclophanePlaneReference
  | .cyclophane (.planeOrder _ _ _ _) => some .cyclophanePlaneOrder
  | .cyclophane (.planeDescriptor _ _ _ _) => some .cyclophanePlaneDescriptor
  | .cyclophane (.center _ _ _ _ _) => some .cyclophaneCenter
  | .cyclophane (.rctEligible _ _) => some .cyclophaneRCTEligible
  | .cyclophane (.rctCandidate _ _ _ _ _) => some .cyclophaneRCTCandidate
  | .cyclophane (.rctSide _ _ _) => some .cyclophaneRCTSide
  | .cyclophane (.doubleBondRing _ _ _ _) => some .cyclophaneDoubleBondRing
  | .cyclophane (.doubleBondGeometry _ _) => some .cyclophaneDoubleBondGeometry
  | .cyclophane (.carbonDoubleBondContext _ _) => some .cyclophaneCarbonContext
  | .cyclophane (.doubleBondNaming _ _ _ _) => some .cyclophaneDoubleBondNaming
  | .fullerene .methodologyDecisionRule => some .fullereneObservation
  | .fullerene (.printedObservation _) => some .fullereneObservation
  | .fullerene (.printedSuperimposedObservation _) =>
      some .fullereneSuperimposedObservation
  | .fullerene _ => none
  | .ringAssembly (.assembly _) => some .ringAssembly
  | .ringAssembly (.normalization _) => some .ringNormalization
  | .ringAssembly (.axisEligible _ _) => some .ringAxisEligible
  | .ringAssembly (.axisCitation _ _ _) => some .ringAxisCitation
  | .ringAssembly (.axisDescriptors _ _ _ _) => some .ringAxisDescriptors
  | .ringAssembly (.centerEligible _ _) => some .ringCenterEligible
  | .ringAssembly (.centerCitation _ _ _) => some .ringCenterCitation
  | .ringAssembly (.centerDescriptor _ _ _) => some .ringCenterDescriptor
  | .ringAssembly (.centerGeneralEquivalent _ _ _ _) => some .ringCenterGeneralEquivalent
  | .ringAssembly (.doubleBondStereogenic _ _ _ _) => some .ringDoubleBondStereogenic
  | .ringAssembly (.doubleBondNeedsSpecification _ _ _ _) =>
      some .ringDoubleBondNeedsSpecification
  | .ringAssembly (.doubleBondCitation _ _ _ _ _) => some .ringDoubleBondCitation
  | .ringAssembly (.doubleBondDescriptor _ _ _ _ _) => some .ringDoubleBondDescriptor
  | .coupled (.baseName _ _) => some .coupledBaseName
  | .coupled (.eligibleUnit _ _) => some .coupledEligibleUnit
  | .coupled (.evidenceBelongs _ _) => some .coupledEvidenceBelongs
  | .coupled (.citation _ _ _) => some .coupledCitation
  | .coupled (.repeatedComponents _ _) => some .coupledRepeatedComponents
  | .coupled (.multiplicativeDecision _ _) => some .coupledMultiplicativeDecision

private def P93GeneralClaim.requiredProvisions : P93GeneralClaim → List IUPACNormativeProvision
  | .preferredAtLowest _ => [.p93RelativeConfiguration, .p93Racemates]
  | .citation _ _ | .descriptor _ _ =>
      [.p93AbsoluteConfiguration, .p93RelativeConfiguration,
        .p93MixedAbsoluteRelativeConfiguration, .p93Racemates, .p93Ambo]

private def P93NoncarbonClaim.requiredProvisions : P93NoncarbonClaim → List IUPACNormativeProvision
  | .tetrahedral _ _ | .descriptor _ _ =>
      [.p93OtherElementTetrahedra, .p93OtherElementGeneralMethodology,
        .p93AzaniumPhosphanium, .p93AminePhosphaneOxides,
        .p93PhosphatesPhosphonates, .p93SulfatesSulfonates, .p93Group14Noncarbon]
  | .citation _ _ => [.p93OtherElementGeneralMethodology]
  | .oxideVariant _ _ _ _ => [.p93AminePhosphaneOxides]
  | .phosphorusOxo _ _ _ _ _ => [.p93PhosphatesPhosphonates]
  | .chalcogenOxo _ _ _ _ _ => [.p93SulfatesSulfonates]

private def P93AcyclicClaim.requiredProvisions : P93AcyclicClaim → List IUPACNormativeProvision
  | .unit _ | .unitKind _ _ | .descriptor _ _ =>
      [.p93AcyclicCenters, .p93SingleAcyclicCenter, .p93MultipleDescriptorsOneCenter,
        .p93PrefixComponentCenters, .p93OrdinaryDoubleBonds, .p93DoubleBondEZCisTrans,
        .p93MultipleDoubleBonds, .p93HeteroatomDoubleBonds, .p93EvenCumulenes,
        .p93OddCumulenes, .p93MultipleAcyclicStereogenicUnits]
  | .citation _ _ =>
      [.p93SingleAcyclicCenter, .p93PrefixComponentCenters,
        .p93MultipleAcyclicStereogenicUnits]
  | .component _ _ => [.p93PrefixComponentCenters]
  | .carbonDoubleBondContext _ _ => [.p93DoubleBondEZCisTrans]
  | .singleCenterNaming _ _ _ _ _ => [.p93SingleAcyclicCenter]
  | .oddCumuleneGeometry _ _ => [.p93OddCumulenes]
  | .multipleCenterDescriptors _ => [.p93MultipleDescriptorsOneCenter]
  | .multipleDoubleBondCollection _ | .multipleDoubleBondDescriptors _ =>
      [.p93MultipleDoubleBonds]
  | .numberingCompetition _ _ => [.p93MultipleAcyclicStereogenicUnits]

private def P93MonocyclicClaim.requiredProvisions : P93MonocyclicClaim → List IUPACNormativeProvision
  | .ring _ | .unitInRing _ _ | .citation _ _ =>
      [.p93CyclicConfigurations, .p93MonocyclicAbsoluteCenters,
        .p93MonocyclicAchiralCenters, .p93MonocyclicCisTrans, .p93MonocyclicRCT,
        .p93UnsaturatedMonocycles, .p93CyclicDoubleBonds,
        .p93ExocyclicDoubleBondEZ, .p93ExocyclicDoubleBondOther]
  | .generalDescriptor _ _ | .generalNotation _ _ _ => [.p93CyclicConfigurations]
  | .center _ _ _ _ _ => [.p93MonocyclicAbsoluteCenters, .p93MonocyclicAchiralCenters]
  | .achiralCenter _ => [.p93MonocyclicAchiralCenters]
  | .ringPlane _ _ _ _ | .ringSide _ _ _ => [.p93MonocyclicCisTrans, .p93MonocyclicRCT]
  | .rctCandidate _ _ _ _ _ _ => [.p93MonocyclicRCT]
  | .unsaturation _ _ _ _ | .seniorGeometry _ _ =>
      [.p93UnsaturatedMonocycles, .p93CyclicDoubleBonds]
  | .chiralCycloalkene _ _ _ => [.p93UnsaturatedMonocycles]
  | .exocyclicSystem _ _ _ _ => [.p93ExocyclicDoubleBondEZ, .p93ExocyclicDoubleBondOther]
  | .exocyclicNaming _ _ _ _ _ => [.p93ExocyclicDoubleBondEZ, .p93ExocyclicDoubleBondOther]

private def P93VonBaeyerClaim.requiredProvisions : P93VonBaeyerClaim → List IUPACNormativeProvision
  | .system _ | .unit _ _ | .citation _ _ =>
      [.p93VonBaeyerCIPCenters, .p93VonBaeyerEndoExoSynAnti,
        .p93VonBaeyerCisTrans, .p93VonBaeyerDoubleBonds]
  | .center _ _ _ _ _ => [.p93VonBaeyerCIPCenters]
  | .bridgeAttachment _ _ _ _ => [.p93VonBaeyerEndoExoSynAnti]
  | .bridgeheadSide _ _ _ _ | .relativeNotation _ _ _ => [.p93VonBaeyerCisTrans]
  | .largerThanBicyclo333 _ _ | .seniorGeometry _ _ | .doubleBondNaming _ _ _ _ _
  | .includedCumuleneNumbering _ _ _ | .includedCumuleneContext _ _ _ =>
      [.p93VonBaeyerDoubleBonds]

private def P93SpiroClaim.requiredProvisions : P93SpiroClaim → List IUPACNormativeProvision
  | .system _ | .unit _ _ | .citation _ _ =>
      [.p93SpiroXabcd, .p93SpiroXabab, .p93SpiroDoubleBonds,
        .p93SpiroAxialChirality, .p93SpiroNontetrahedralCenters]
  | .pattern _ _ | .centerDescriptor _ _ _ _ => [.p93SpiroXabcd, .p93SpiroXabab]
  | .xababOrder _ _ => [.p93SpiroXabab]
  | .doubleBondRing _ _ _ | .doubleBondGeometry _ _ | .doubleBondNaming _ _ _ _ =>
      [.p93SpiroDoubleBonds]
  | .coordination _ _ _ | .polyhedralDescriptor _ _ _ _ =>
      [.p93SpiroNontetrahedralCenters]
  | .axialCenterDescriptor _ _ | .axialDescriptor _ _ => [.p93SpiroAxialChirality]

private def P93FusedClaim.requiredProvisions : P93FusedClaim → List IUPACNormativeProvision
  | .cipObservation _ => [.p93FusedBridgedCIP]
  | .relationObservation _ => [.p93CisoidTransoid]
  | .system _ | .unit _ _ => [.p93FusedBridgedCIP, .p93CisoidTransoid]
  | .citation _ _ | .axis _ _ | .unitDescriptor _ _ _ => [.p93FusedBridgedCIP]
  | .fusionPair _ _ _ | .nearestCandidate _ _ _ _ _ | .fusionCitation _ _ _ _
  | .fusionRelation _ _ _ _ _ _ => [.p93CisoidTransoid]

private def P93CyclophaneClaim.requiredProvisions : P93CyclophaneClaim → List IUPACNormativeProvision
  | .system _ | .unit _ _ | .citation _ _ =>
      [.p93CyclophanePlanes, .p93CyclophaneCenters, .p93CyclophaneDoubleBonds]
  | .planeReference _ _ _ | .planeOrder _ _ _ _ | .planeDescriptor _ _ _ _ =>
      [.p93CyclophanePlanes]
  | .center _ _ _ _ _ | .rctEligible _ _ | .rctCandidate _ _ _ _ _
  | .rctSide _ _ _ => [.p93CyclophaneCenters]
  | .doubleBondRing _ _ _ _ | .doubleBondGeometry _ _ | .carbonDoubleBondContext _ _
  | .doubleBondNaming _ _ _ _ => [.p93CyclophaneDoubleBonds]

private def P93FullereneClaim.requiredProvisions : P93FullereneClaim → List IUPACNormativeProvision
  | .methodologyDecisionRule => [.p93FullereneGeneralMethodology]
  | .printedObservation _ =>
      [.p93FullereneInherentParentChirality,
        .p93FullereneInherentSubstitutionChirality,
        .p93FullereneNoninherentSubstitutionChirality,
        .p93FullereneChiralSubstituents]
  | .printedSuperimposedObservation _ =>
      [.p93FullereneSuperimposedStereogenicElements]
  | .rawMolecule _ | .inputFamily _ _ | .substitutionEvidence _ _ _
  | .preferredNumbering _ _ _ | .originalChirality _ _ _ _ =>
      [.p93FullereneGeneralMethodology, .p93FullereneInherentParentChirality,
        .p93FullereneInherentSubstitutionChirality,
        .p93FullereneNoninherentSubstitutionChirality,
        .p93FullereneChiralSubstituents,
        .p93FullereneSuperimposedStereogenicElements]
  | .substituentUnit _ _ _ _ _ | .substituentCitation _ _ _ _ _
  | .substituentDescriptor _ _ _ _ _ =>
      [.p93FullereneChiralSubstituents, .p93FullereneSuperimposedStereogenicElements]

private def P93RingAssemblyClaim.requiredProvisions : P93RingAssemblyClaim → List IUPACNormativeProvision
  | .assembly _ => [.p93RingAssemblyAxes, .p93RingAssemblyCenters, .p93RingAssemblyDoubleBonds]
  | .normalization _ | .axisEligible _ _ | .axisCitation _ _ _
  | .axisDescriptors _ _ _ _ => [.p93RingAssemblyAxes]
  | .centerEligible _ _ | .centerCitation _ _ _ | .centerDescriptor _ _ _
  | .centerGeneralEquivalent _ _ _ _ => [.p93RingAssemblyCenters]
  | .doubleBondStereogenic _ _ _ _ | .doubleBondNeedsSpecification _ _ _ _
  | .doubleBondCitation _ _ _ _ _ | .doubleBondDescriptor _ _ _ _ _ =>
      [.p93RingAssemblyDoubleBonds]

private def P93CoupledClaim.requiredProvisions (_claim : P93CoupledClaim) :
    List IUPACNormativeProvision := [.p93CoupledRingChainConfigurations]

private def P93SourceClaim.requiredProvisions : P93SourceClaim → List IUPACNormativeProvision
  | .physical _ => []
  | .general claim => claim.requiredProvisions
  | .noncarbon claim => claim.requiredProvisions
  | .acyclic claim => claim.requiredProvisions
  | .monocyclic claim => claim.requiredProvisions
  | .vonBaeyer claim => claim.requiredProvisions
  | .spiro claim => claim.requiredProvisions
  | .fused claim => claim.requiredProvisions
  | .cyclophane claim => claim.requiredProvisions
  | .fullerene claim => claim.requiredProvisions
  | .ringAssembly claim => claim.requiredProvisions
  | .coupled claim => claim.requiredProvisions

def P93SourceField.requiredProvisions : P93SourceField → List IUPACNormativeProvision
  | .generalPreferred => [.p93RelativeConfiguration, .p93Racemates]
  | .generalCitation | .generalDescriptor =>
      [.p93AbsoluteConfiguration, .p93RelativeConfiguration,
        .p93MixedAbsoluteRelativeConfiguration, .p93Racemates, .p93Ambo]
  | .noncarbonTetrahedral | .noncarbonDescriptor =>
      [.p93OtherElementTetrahedra, .p93OtherElementGeneralMethodology,
        .p93AzaniumPhosphanium, .p93AminePhosphaneOxides,
        .p93PhosphatesPhosphonates, .p93SulfatesSulfonates, .p93Group14Noncarbon]
  | .noncarbonCitation => [.p93OtherElementGeneralMethodology]
  | .noncarbonOxide => [.p93AminePhosphaneOxides]
  | .noncarbonPhosphorusOxo => [.p93PhosphatesPhosphonates]
  | .noncarbonChalcogenOxo => [.p93SulfatesSulfonates]
  | .acyclicUnit | .acyclicUnitKind | .acyclicDescriptor =>
      [.p93AcyclicCenters, .p93SingleAcyclicCenter, .p93MultipleDescriptorsOneCenter,
        .p93PrefixComponentCenters, .p93OrdinaryDoubleBonds, .p93DoubleBondEZCisTrans,
        .p93MultipleDoubleBonds, .p93HeteroatomDoubleBonds, .p93EvenCumulenes,
        .p93OddCumulenes, .p93MultipleAcyclicStereogenicUnits]
  | .acyclicCitation =>
      [.p93SingleAcyclicCenter, .p93PrefixComponentCenters,
        .p93MultipleAcyclicStereogenicUnits]
  | .acyclicComponent => [.p93PrefixComponentCenters]
  | .acyclicCarbonContext => [.p93DoubleBondEZCisTrans]
  | .acyclicSingleCenterNaming => [.p93SingleAcyclicCenter]
  | .acyclicOddCumuleneGeometry => [.p93OddCumulenes]
  | .acyclicMultipleCenterDescriptors => [.p93MultipleDescriptorsOneCenter]
  | .acyclicMultipleDoubleBondCollection | .acyclicMultipleDoubleBondDescriptors =>
      [.p93MultipleDoubleBonds]
  | .acyclicNumberingCompetition => [.p93MultipleAcyclicStereogenicUnits]
  | .monocyclicCitation | .monocyclicRing | .monocyclicUnitInRing =>
      [.p93CyclicConfigurations, .p93MonocyclicAbsoluteCenters,
        .p93MonocyclicAchiralCenters, .p93MonocyclicCisTrans, .p93MonocyclicRCT,
        .p93UnsaturatedMonocycles, .p93CyclicDoubleBonds,
        .p93ExocyclicDoubleBondEZ, .p93ExocyclicDoubleBondOther]
  | .monocyclicGeneralDescriptor => [.p93CyclicConfigurations]
  | .monocyclicCenter => [.p93MonocyclicAbsoluteCenters, .p93MonocyclicAchiralCenters]
  | .monocyclicAchiralCenter => [.p93MonocyclicAchiralCenters]
  | .monocyclicRingPlane | .monocyclicRingSide =>
      [.p93MonocyclicCisTrans, .p93MonocyclicRCT]
  | .monocyclicRCTCandidate => [.p93MonocyclicRCT]
  | .monocyclicUnsaturation | .monocyclicSeniorGeometry =>
      [.p93UnsaturatedMonocycles, .p93CyclicDoubleBonds]
  | .monocyclicChiralCycloalkene => [.p93UnsaturatedMonocycles]
  | .monocyclicExocyclicSystem | .monocyclicExocyclicNaming =>
      [.p93ExocyclicDoubleBondEZ, .p93ExocyclicDoubleBondOther]
  | .vonBaeyerSystem | .vonBaeyerUnit | .vonBaeyerCitation =>
      [.p93VonBaeyerCIPCenters, .p93VonBaeyerEndoExoSynAnti,
        .p93VonBaeyerCisTrans, .p93VonBaeyerDoubleBonds]
  | .vonBaeyerCenter => [.p93VonBaeyerCIPCenters]
  | .vonBaeyerBridgeAttachment => [.p93VonBaeyerEndoExoSynAnti]
  | .vonBaeyerBridgeheadSide | .vonBaeyerRelativeNotation => [.p93VonBaeyerCisTrans]
  | .vonBaeyerLargerThan333 | .vonBaeyerSeniorGeometry | .vonBaeyerDoubleBondNaming
  | .vonBaeyerCumuleneNumbering | .vonBaeyerCumuleneContext => [.p93VonBaeyerDoubleBonds]
  | .spiroSystem | .spiroUnit | .spiroCitation =>
      [.p93SpiroXabcd, .p93SpiroXabab, .p93SpiroDoubleBonds,
        .p93SpiroAxialChirality, .p93SpiroNontetrahedralCenters]
  | .spiroPattern | .spiroCenterDescriptor => [.p93SpiroXabcd, .p93SpiroXabab]
  | .spiroXababOrder => [.p93SpiroXabab]
  | .spiroDoubleBondRing | .spiroDoubleBondGeometry | .spiroDoubleBondNaming =>
      [.p93SpiroDoubleBonds]
  | .spiroCoordination | .spiroPolyhedralDescriptor => [.p93SpiroNontetrahedralCenters]
  | .spiroAxialCenterDescriptor | .spiroAxialDescriptor => [.p93SpiroAxialChirality]
  | .fusedCIPObservation => [.p93FusedBridgedCIP]
  | .fusedRelationObservation => [.p93CisoidTransoid]
  | .cyclophaneSystem | .cyclophaneUnit | .cyclophaneCitation =>
      [.p93CyclophanePlanes, .p93CyclophaneCenters, .p93CyclophaneDoubleBonds]
  | .cyclophanePlaneReference | .cyclophanePlaneOrder | .cyclophanePlaneDescriptor =>
      [.p93CyclophanePlanes]
  | .cyclophaneCenter | .cyclophaneRCTEligible | .cyclophaneRCTCandidate
  | .cyclophaneRCTSide => [.p93CyclophaneCenters]
  | .cyclophaneDoubleBondRing | .cyclophaneDoubleBondGeometry
  | .cyclophaneCarbonContext | .cyclophaneDoubleBondNaming => [.p93CyclophaneDoubleBonds]
  | .fullereneObservation =>
      [.p93FullereneGeneralMethodology, .p93FullereneInherentParentChirality,
        .p93FullereneInherentSubstitutionChirality,
        .p93FullereneNoninherentSubstitutionChirality, .p93FullereneChiralSubstituents]
  | .fullereneSuperimposedObservation => [.p93FullereneSuperimposedStereogenicElements]
  | .ringAssembly => [.p93RingAssemblyAxes, .p93RingAssemblyCenters, .p93RingAssemblyDoubleBonds]
  | .ringNormalization => []
  | .ringAxisEligible | .ringAxisCitation | .ringAxisDescriptors =>
      [.p93RingAssemblyAxes]
  | .ringCenterEligible | .ringCenterCitation | .ringCenterDescriptor
  | .ringCenterGeneralEquivalent => [.p93RingAssemblyCenters]
  | .ringDoubleBondStereogenic | .ringDoubleBondNeedsSpecification
  | .ringDoubleBondCitation | .ringDoubleBondDescriptor => [.p93RingAssemblyDoubleBonds]
  | .coupledBaseName | .coupledEligibleUnit | .coupledEvidenceBelongs | .coupledCitation
  | .coupledRepeatedComponents | .coupledMultiplicativeDecision =>
      [.p93CoupledRingChainConfigurations]

def P93Clause.requiredFields (clause : P93Clause) : List P93SourceField :=
  P93SourceField.all.filter fun field => clause.provision ∈ field.requiredProvisions

def P93SourceClaim.SuppliesField
    (claim : P93SourceClaim) (field : P93SourceField) : Prop :=
  claim.field? = some field

/-! ## Computed molecular envelopes -/

/-- Decoration-free molecular envelope.  Unlike `P93AuthorityPhysicalUnit.ValidFor`, this relation
contains no policy predicate. -/
def P93CanonicalPhysicalUnitEnvelope
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
  | .plane members => ∃ frame : P93AuthorityPlaneFrame, frame.ValidFor source members
  | .helix path => ∃ frame : P93AuthorityHelixFrame, frame.ValidFor source path
  | .polyhedron center positions =>
      ∃ geometry frame,
        P93AuthorityPolyhedralFrame.ValidFor source center positions geometry frame

/-- Source-only constitutional carrier for a printed polyhedral unit.  It deliberately contains
no Cartesian coordinates, geometry-recognition frame, or derived orientation.  Those data belong
to a separate executable witness. -/
def P93CanonicalPrintedPolyhedralCarrierEnvelope
    (source : AuthoritativeChemicalInput) (center : Nat) (positions : Finset Nat) : Prop :=
  center < source.molecule.atomCount ∧ center ∉ positions ∧ positions.Nonempty ∧
    P93AuthorityAtomsBounded source positions.toList ∧
    ∀ position ∈ positions,
      P93AuthorityBinaryBond source center position ∨
        P93AuthorityMulticenterIncidence source center position

/-- Source-only constitutional carrier for a printed stereogenic plane.  The Blue Book drawing
fixes the plane membership and the pilot/reference roles, but it does not print Cartesian
coordinates.  Coplanarity and the determinant sign therefore belong to a separate executable
witness. -/
def P93CanonicalPrintedPlaneCarrierEnvelope
    (source : AuthoritativeChemicalInput) (members : Finset Nat)
    (pilot firstReference secondReference inPlaneBondAtom outOfPlaneAtom : Nat) : Prop :=
  3 ≤ members.card ∧
    P93AuthorityAtomsBounded source members.toList ∧
    pilot ∈ members ∧ firstReference ∈ members ∧ secondReference ∈ members ∧
    inPlaneBondAtom ∈ members ∧ outOfPlaneAtom ∉ members ∧
    [pilot, firstReference, secondReference, inPlaneBondAtom].Nodup ∧
    P93AuthorityBinaryBond source pilot firstReference ∧
    P93AuthorityBinaryBond source pilot secondReference ∧
    P93AuthorityBinaryBond source pilot inPlaneBondAtom ∧
    P93AuthorityBinaryBond source inPlaneBondAtom outOfPlaneAtom

def P93CanonicalFusedPathFromTo
    (source : AuthoritativeChemicalInput) (system : P93AuthorityFusedSystem)
    (first second : Nat) (path : List Nat) : Prop :=
  ∃ middle, path = first :: middle ++ [second] ∧ path.Nodup ∧
    P93AuthorityAtomsBounded source path ∧ P93AuthorityConnectedPath source path ∧
    ∀ atom ∈ path, atom ∈ system.atoms

/-- Unlike the legacy candidate relation, this judgment fixes both formerly free numbers:
distance is the length of a shortest molecular path and the locant is the smaller endpoint. -/
def P93CanonicalFusedNearestCandidate.ValidFor
    (source : AuthoritativeChemicalInput) (system : P93AuthorityFusedSystem)
    (evidence : P93CanonicalFusedNearestCandidate) : Prop :=
  let candidate := evidence.candidate
  candidate.firstFusionAtom < candidate.secondFusionAtom ∧
    P93AuthorityFusionAtom system candidate.firstFusionAtom ∧
    P93AuthorityFusionAtom system candidate.secondFusionAtom ∧
    (candidate.firstFusionAtom, candidate.firstFusionLocant) ∈ system.fusionLocants ∧
    (candidate.secondFusionAtom, candidate.secondFusionLocant) ∈ system.fusionLocants ∧
    P93CanonicalFusedPathFromTo source system candidate.firstFusionAtom
      candidate.secondFusionAtom evidence.shortestPath ∧
    candidate.graphDistance + 1 = evidence.shortestPath.length ∧
    candidate.lowerAtomLocant =
      P93FusedLocant.min candidate.firstFusionLocant candidate.secondFusionLocant ∧
    (∀ alternative,
      P93CanonicalFusedPathFromTo source system candidate.firstFusionAtom
        candidate.secondFusionAtom alternative →
      evidence.shortestPath.length ≤ alternative.length)

def P93CanonicalFusedCIPObservation.ValidFor
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFusedCIPObservation) : Prop :=
  observation.system.MechanicallyValidFor source ∧
    (match observation.unit with
    | .physical unit =>
        P93CanonicalPhysicalUnitEnvelope source unit ∧
          P93FusedPhysicalUnitSupported observation.system unit
    | .fusedAxis path =>
        2 ≤ path.length ∧ path.Nodup ∧ P93AuthorityAtomsBounded source path ∧
          P93AuthorityCanonicalDirectedPath path ∧ P93AuthorityConnectedPath source path ∧
          ∀ atom ∈ path, atom ∈ observation.system.atoms) ∧
    P93FusedUnitDescriptorMatches observation.unit observation.descriptor ∧
    observation.citation.Valid ∧
    observation.citation.CitesUnit observation.system observation.unit

def P93CanonicalFusionLegacyDescriptor : CisTrans → FusionRelationDescriptor
  | .cis => .cisoid
  | .trans => .transoid

/-- Closed relation judgment for the source-only P-93.5.4.2 fact.  Both junction states are part
of the single cited fact rather than ignored arguments; the independently stated nearest-atom
relation determines the legacy descriptor, while the preferred result is forced to `relCIP`. -/
def P93CanonicalFusedRelationSourceFact.Judged
    (fact : P93CanonicalFusedRelationSourceFact) : Prop :=
  (fact.firstJunction, fact.legacyDescriptor, fact.secondJunction,
      fact.preferredDescriptor) =
    (fact.firstJunction, P93CanonicalFusionLegacyDescriptor fact.nearestAtomsRelation,
      fact.secondJunction, .relCIP) ∧
    PreferredFusionDescription fact.preferredDescriptor ∧ fact.citation.Valid

def P93CanonicalFusedRelationObservation.ValidFor
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFusedRelationObservation) : Prop :=
  observation.system.MechanicallyValidFor source ∧ observation.candidates ≠ [] ∧
    (observation.candidates.map fun evidence =>
      (evidence.candidate.firstFusionAtom, evidence.candidate.secondFusionAtom)).Nodup ∧
    (∀ evidence ∈ observation.candidates, evidence.ValidFor source observation.system) ∧
    observation.selected ∈ observation.candidates ∧
    P93FusedIsUniqueSelectedNearestPair
      (observation.candidates.map P93CanonicalFusedNearestCandidate.candidate)
      observation.selected.candidate ∧
    observation.relation.citation = observation.selected.candidate.lowerAtomLocant ∧
    observation.relation.Judged

def P93CanonicalFullereneSubstituentAssignment.ValidForInput
    (source : AuthoritativeChemicalInput)
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence)
    (assignment : P93FullereneSubstituentCIPAssignment) : Prop :=
  assignment.substitutedSite ∈ input.carrier ∧
    assignment.substitutedSite ∈ evidence.chiralSubstituentSites ∧
    P93CanonicalPhysicalUnitEnvelope source assignment.unit.toPhysicalUnit ∧
    P93FullereneSubstituentDescriptorMatchesUnit assignment.descriptor assignment.unit ∧
    assignment.citation.Valid

def P93CanonicalFullereneSubstituentAssignment.ValidFor
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFullereneObservation)
    (assignment : P93FullereneSubstituentCIPAssignment) : Prop :=
  P93CanonicalFullereneSubstituentAssignment.ValidForInput source
    observation.selectedInput.symmetryInput.cage
    observation.selectedInput.symmetryInput.substitutionEvidence assignment

def P93CanonicalFullereneObservation.ValidFor
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFullereneObservation) : Prop :=
  source.spatial? = some observation.spatial ∧
    observation.molecule.AuthoritativeStructureAgreement source ∧
    observation.inputs ≠ [] ∧ observation.selectedInput ∈ observation.inputs ∧
    (∀ input ∈ observation.inputs,
      SpatiallyDerivedMolecularFullereneConfigurationInputJudgment
        observation.molecule observation.spatial input ∧
      MolecularFullereneSubstitutionEvidenceJudgment
        input.symmetryInput.cage input.symmetryInput.substitutionEvidence ∧
      MolecularFullereneNumberingEvidenceJudgment
        input.symmetryInput.cage input.numberingEvidence) ∧
    FullereneConfigurationAssignmentJudgment
      observation.selectedInput.symmetryInput.cage.toFullereneConfigurationInput
      observation.assignment ∧
    SpatiallyDerivedMolecularFullereneConfigurationAssignmentJudgment
      observation.molecule observation.spatial observation.inputs observation.assignment ∧
    (observation.substituentAssignments.map fun assignment =>
      (assignment.substitutedSite, assignment.unit)).Nodup ∧
    (observation.substituentAssignments.map fun assignment =>
      assignment.unit.toPhysicalUnit).Nodup ∧
    (observation.substituentAssignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ observation.substituentAssignments,
      P93CanonicalFullereneSubstituentAssignment.ValidFor source observation assignment) ∧
    (observation.assignment.chiralityType = .chiralSubstituentsOnly →
      observation.substituentAssignments ≠ []) ∧
    ∀ site ∈ observation.selectedInput.symmetryInput.substitutionEvidence.chiralSubstituentSites,
      ∃ assignment ∈ observation.substituentAssignments,
        assignment.substitutedSite = site

def P93CanonicalFullereneObservation.Superimposed
    (observation : P93CanonicalFullereneObservation) : Prop :=
  (observation.assignment.chiralityType = .inherentlyChiralSubstitutionPattern ∨
    observation.assignment.chiralityType = .noninherentlyChiralSubstitutionPattern) ∧
  (∃ numberingKind handedness,
    FullereneDescriptorPayload.cageHandedness numberingKind handedness ∈
      observation.assignment.payloads) ∧
  observation.substituentAssignments ≠ [] ∧
  SuperimposedFullereneConfigurationComplete true true

def P93CanonicalFullereneType4Observation.ValidFor
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFullereneType4Observation) : Prop :=
  observation.molecule.AuthoritativeStructureAgreement source ∧
    SymmetryDerivedMolecularFullereneConfigurationInputJudgment
      observation.molecule observation.input ∧
    FullereneTypeMatches observation.input.cage.substitutionTest .chiralSubstituentsOnly ∧
    observation.input.cage.descriptorEvidence.cageNumberingKind = none ∧
    observation.input.cage.descriptorEvidence.cageTurn = none ∧
    observation.input.cage.descriptorEvidence.everyChiralSubstituentHasCIP = true ∧
    observation.substituentAssignments ≠ [] ∧
    (observation.substituentAssignments.map fun assignment =>
      (assignment.substitutedSite, assignment.unit)).Nodup ∧
    (observation.substituentAssignments.map fun assignment =>
      assignment.unit.toPhysicalUnit).Nodup ∧
    (observation.substituentAssignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ observation.substituentAssignments,
      P93CanonicalFullereneSubstituentAssignment.ValidForInput source observation.input.cage
        observation.input.substitutionEvidence assignment) ∧
    (∀ site ∈ observation.input.substitutionEvidence.chiralSubstituentSites,
      ∃ assignment ∈ observation.substituentAssignments,
        assignment.substitutedSite = site)

def P93FullereneSubstituentStereogenicUnit.atomCarrier :
    P93FullereneSubstituentStereogenicUnit → Finset Nat
  | P93FullereneSubstituentStereogenicUnit.center atom => {atom}
  | P93FullereneSubstituentStereogenicUnit.doubleBond first second
  | P93FullereneSubstituentStereogenicUnit.bondAxis first second => {first, second}
  | P93FullereneSubstituentStereogenicUnit.cumuleneAxis path
  | P93FullereneSubstituentStereogenicUnit.helix path => path.toFinset
  | P93FullereneSubstituentStereogenicUnit.plane members => members
  | P93FullereneSubstituentStereogenicUnit.polyhedron centerAtom positions =>
      insert centerAtom positions

def P93AuthorityConsecutivelyBonded
    (source : AuthoritativeChemicalInput) : List Nat → Prop
  | [] | [_] => True
  | first :: second :: rest =>
      P93AuthorityBinaryBond source first second ∧
        P93AuthorityConsecutivelyBonded source (second :: rest)

/-- Constitutional ownership certificate for one independently inventoried substituent unit. -/
def P93CanonicalFullereneSubstituentInventoryEntry.ValidFor
    (source : AuthoritativeChemicalInput) (cageCarrier : Finset Nat)
    (entry : P93CanonicalFullereneSubstituentInventoryEntry) : Prop :=
  entry.substitutedSite ∈ cageCarrier ∧
    entry.attachmentAtom ∈ entry.ownedAtoms ∧
    entry.attachmentAtom ∉ cageCarrier ∧
    P93AuthorityBinaryBond source entry.substitutedSite entry.attachmentAtom ∧
    (∀ atom ∈ entry.ownedAtoms, atom ∉ cageCarrier) ∧
    entry.unit.atomCarrier ⊆ entry.ownedAtoms ∧
    P93CanonicalPhysicalUnitEnvelope source entry.unit.toPhysicalUnit ∧
    (∀ atom ∈ entry.ownedAtoms, ∃ path : List Nat,
      path.head? = some entry.attachmentAtom ∧ path.getLast? = some atom ∧
        (∀ member ∈ path, member ∈ entry.ownedAtoms) ∧
        P93AuthorityConsecutivelyBonded source path) ∧
    ∀ atom ∈ entry.ownedAtoms, ∀ neighbor,
      P93AuthorityBinaryBond source atom neighbor → neighbor ∉ cageCarrier →
        neighbor ∈ entry.ownedAtoms

/-- Printed facts are internally closed without any spatial/oriented-face datum.  The finite
inventory is independent of the CIP assignment list, and the final equality says the assignments
cover exactly that inventory rather than defining eligibility themselves. -/
def P93CanonicalFullerenePrintedObservation.ValidFor
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFullerenePrintedObservation) : Prop :=
  observation.molecule.AuthoritativeStructureAgreement source ∧
    observation.cageCarrier.Nonempty ∧
    P93AuthorityAtomsBounded source observation.cageCarrier.toList ∧
    (observation.unitInventory.map fun entry =>
      (entry.substitutedSite, entry.unit)).Nodup ∧
    (observation.unitInventory.map fun entry => entry.unit.toPhysicalUnit).Nodup ∧
    (∀ entry ∈ observation.unitInventory,
      entry.ValidFor source observation.cageCarrier ∧
        entry.substitutedSite ∈ observation.chiralSubstituentSites) ∧
    (∀ site ∈ observation.chiralSubstituentSites,
      ∃ entry ∈ observation.unitInventory, entry.substitutedSite = site) ∧
    (observation.substituentAssignments.map fun assignment =>
      (assignment.substitutedSite, assignment.unit)) =
      (observation.unitInventory.map fun entry =>
        (entry.substitutedSite, entry.unit)) ∧
    (observation.substituentAssignments.map fun assignment => assignment.citation).Nodup ∧
    ∀ assignment ∈ observation.substituentAssignments,
      P93FullereneSubstituentDescriptorMatchesUnit assignment.descriptor assignment.unit ∧
        assignment.citation.Valid

theorem P93CanonicalFullerenePrintedObservation.inventory_of_assignment
    {source : AuthoritativeChemicalInput}
    {observation : P93CanonicalFullerenePrintedObservation}
    (valid : observation.ValidFor source)
    {assignment : P93FullereneSubstituentCIPAssignment}
    (member : assignment ∈ observation.substituentAssignments) :
    ∃ entry ∈ observation.unitInventory,
      entry.substitutedSite = assignment.substitutedSite ∧ entry.unit = assignment.unit := by
  have pairMember : (assignment.substitutedSite, assignment.unit) ∈
      observation.substituentAssignments.map fun carried =>
        (carried.substitutedSite, carried.unit) :=
    List.mem_map.mpr ⟨assignment, member, rfl⟩
  rw [valid.2.2.2.2.2.2.2.1] at pairMember
  rcases List.mem_map.mp pairMember with ⟨entry, entryMem, pairEq⟩
  exact ⟨entry, entryMem, congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩

theorem P93CanonicalFullerenePrintedObservation.assignment_of_inventory
    {source : AuthoritativeChemicalInput}
    {observation : P93CanonicalFullerenePrintedObservation}
    (valid : observation.ValidFor source)
    {entry : P93CanonicalFullereneSubstituentInventoryEntry}
    (member : entry ∈ observation.unitInventory) :
    ∃ assignment ∈ observation.substituentAssignments,
      assignment.substitutedSite = entry.substitutedSite ∧ assignment.unit = entry.unit := by
  have pairMember : (entry.substitutedSite, entry.unit) ∈
      observation.unitInventory.map fun carried =>
        (carried.substitutedSite, carried.unit) :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [← valid.2.2.2.2.2.2.2.1] at pairMember
  rcases List.mem_map.mp pairMember with ⟨assignment, assignmentMem, pairEq⟩
  exact ⟨assignment, assignmentMem, congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩

def P93PhysicalClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93PhysicalClaim → Prop
  | P93PhysicalClaim.helix path frame => frame.ValidFor source path
  | P93PhysicalClaim.plane members frame => frame.ValidFor source members
  | P93PhysicalClaim.polyhedron center positions geometry frame =>
      frame.ValidFor source center positions geometry

def P93GeneralClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93GeneralClaim → Prop
  | P93GeneralClaim.preferredAtLowest value =>
      value.GeneralRepresentativeEligible ∧ value.mirror ≠ value ∧ value.PreferredAtLowest
  | P93GeneralClaim.citation token unit => token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source unit
  | P93GeneralClaim.descriptor unit _ => P93CanonicalPhysicalUnitEnvelope source unit

def P93NoncarbonClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93NoncarbonClaim → Prop
  | P93NoncarbonClaim.tetrahedral center ligands =>
      center < source.molecule.atomCount ∧ 4 ≤ ligands.length ∧ ligands.Nodup ∧
        P93AuthorityAtomsBounded source ligands
  | P93NoncarbonClaim.citation token unit => token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source unit
  | P93NoncarbonClaim.descriptor unit _ => P93CanonicalPhysicalUnitEnvelope source unit
  | P93NoncarbonClaim.oxideVariant center oxygen _ _
  | P93NoncarbonClaim.phosphorusOxo center oxygen _ _ _
  | P93NoncarbonClaim.chalcogenOxo center oxygen _ _ _ =>
      center < source.molecule.atomCount ∧ oxygen < source.molecule.atomCount ∧
        P93AuthorityBinaryBond source center oxygen

def P93AcyclicClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93AcyclicClaim → Prop
  | P93AcyclicClaim.citation token physicalUnit =>
      token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93AcyclicClaim.component componentValue physicalUnit =>
      componentValue.Valid ∧ P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93AcyclicClaim.unit physicalUnit =>
      P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93AcyclicClaim.unitKind physicalUnit kind =>
      P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        P93AcyclicUnitKindMatchesPhysical kind physicalUnit ∧
        match kind, physicalUnit with
        | .evenDoubleBondCumulene, .axis path =>
            P93AuthorityCanonicalEvenCumuleneAxisPerceived source path
        | .oddDoubleBondCumulene, .axis path =>
            P93AuthorityCanonicalOddCumuleneAxisPerceived source path
        | _, _ => True
  | P93AcyclicClaim.descriptor physicalUnit _ =>
      P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93AcyclicClaim.carbonDoubleBondContext physicalUnit _ =>
      P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93AcyclicClaim.singleCenterNaming physicalUnit citation? _ _ affixes =>
      P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        (∀ citation, citation ∈ citation? → citation.Valid) ∧
        P93AcyclicAffixOrderConforms affixes
  | P93AcyclicClaim.oddCumuleneGeometry path _ =>
      P93AuthorityCanonicalOddCumuleneAxisPerceived source path
  | P93AcyclicClaim.multipleCenterDescriptors assignments =>
      2 ≤ assignments.length ∧
        (assignments.map fun assignment => assignment.1).Nodup ∧
        ∀ assignment ∈ assignments,
          P93CanonicalPhysicalUnitEnvelope source assignment.1 ∧
            (assignment.2.1 = .chiralCenter ∨
              assignment.2.1 = .pseudoasymmetricCenter) ∧
            DescriptorApplies assignment.2.1 assignment.2.2
  | P93AcyclicClaim.multipleDoubleBondCollection bonds =>
      2 ≤ bonds.length ∧ bonds.Nodup ∧
        ∀ bond ∈ bonds,
          P93CanonicalPhysicalUnitEnvelope source bond ∧
            ∃ first second, bond = .bond first second
  | P93AcyclicClaim.multipleDoubleBondDescriptors assignments =>
      2 ≤ assignments.length ∧
        (assignments.map fun assignment => assignment.1).Nodup ∧
        ∀ assignment ∈ assignments,
          P93CanonicalPhysicalUnitEnvelope source assignment.1 ∧
            (assignment.2.1 = .ordinaryDoubleBond ∨
              assignment.2.1 = .heteroatomDoubleBond) ∧
            DescriptorApplies assignment.2.1 assignment.2.2
  | P93AcyclicClaim.numberingCompetition units _ =>
      units ≠ [] ∧
        ∀ entry ∈ units,
          P93CanonicalPhysicalUnitEnvelope source entry.1 ∧
            ∀ citation, citation ∈ entry.2 → citation.Valid

def P93MonocyclicClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93MonocyclicClaim → Prop
  | P93MonocyclicClaim.citation token unit => token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source unit
  | P93MonocyclicClaim.ring atoms => P93AuthorityClosedCycle source atoms
  | P93MonocyclicClaim.unitInRing atoms unit =>
      P93AuthorityClosedCycle source atoms ∧ P93CanonicalPhysicalUnitEnvelope source unit
  | P93MonocyclicClaim.generalDescriptor unit _ => P93CanonicalPhysicalUnitEnvelope source unit
  | P93MonocyclicClaim.generalNotation unit _ _ => P93CanonicalPhysicalUnitEnvelope source unit
  | P93MonocyclicClaim.center centerAtom kind descriptor _ _ =>
      centerAtom < source.molecule.atomCount ∧ DescriptorApplies kind descriptor
  | P93MonocyclicClaim.achiralCenter centerAtom => centerAtom < source.molecule.atomCount
  | P93MonocyclicClaim.ringPlane atoms first second _ =>
      P93AuthorityClosedCycle source atoms ∧ first ∈ atoms ∧ second ∈ atoms ∧ first ≠ second
  | P93MonocyclicClaim.ringSide atoms ligand _ =>
      P93AuthorityClosedCycle source atoms ∧ ligand < source.molecule.atomCount
  | P93MonocyclicClaim.rctCandidate atoms ringPosition substituent token _ _ =>
      P93AuthorityClosedCycle source atoms ∧ ringPosition ∈ atoms ∧ substituent ∉ atoms ∧
        P93AuthorityBinaryBond source ringPosition substituent ∧ token.Valid
  | P93MonocyclicClaim.unsaturation atoms unit _ _ =>
      P93AuthorityClosedCycle source atoms ∧ P93CanonicalPhysicalUnitEnvelope source unit
  | P93MonocyclicClaim.seniorGeometry unit _
  | P93MonocyclicClaim.chiralCycloalkene unit _ _ => P93CanonicalPhysicalUnitEnvelope source unit
  | P93MonocyclicClaim.exocyclicSystem atoms unit _ _ =>
      P93AuthorityClosedCycle source atoms ∧ P93CanonicalPhysicalUnitEnvelope source unit
  | P93MonocyclicClaim.exocyclicNaming unit _ _ _ _ => P93CanonicalPhysicalUnitEnvelope source unit

def P93VonBaeyerClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93VonBaeyerClaim → Prop
  | P93VonBaeyerClaim.system systemValue => systemValue.MechanicallyValidFor source
  | P93VonBaeyerClaim.unit systemValue physicalUnit =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        P93VonBaeyerUnitSupported systemValue physicalUnit
  | P93VonBaeyerClaim.citation token physicalUnit =>
      token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93VonBaeyerClaim.center centerAtom kind descriptor _ _ =>
      centerAtom < source.molecule.atomCount ∧ DescriptorApplies kind descriptor
  | P93VonBaeyerClaim.bridgeAttachment systemValue attachment substituent _ =>
      systemValue.MechanicallyValidFor source ∧ attachment ∈ systemValue.atoms ∧
        substituent ∉ systemValue.atoms ∧ P93AuthorityBinaryBond source attachment substituent
  | P93VonBaeyerClaim.bridgeheadSide systemValue bridgehead ligand _ =>
      systemValue.MechanicallyValidFor source ∧ ligand ∉ systemValue.atoms ∧
        P93AuthorityBinaryBond source bridgehead ligand
  | P93VonBaeyerClaim.relativeNotation systemValue _ _
  | P93VonBaeyerClaim.largerThanBicyclo333 systemValue _ =>
      systemValue.MechanicallyValidFor source
  | P93VonBaeyerClaim.seniorGeometry physicalUnit _ =>
      P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93VonBaeyerClaim.doubleBondNaming systemValue physicalUnit _ _ _ =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93VonBaeyerClaim.includedCumuleneNumbering systemValue path token =>
      systemValue.MechanicallyValidFor source ∧
        P93AuthorityCanonicalCumuleneAxisPerceived source path ∧ token.Valid
  | P93VonBaeyerClaim.includedCumuleneContext systemValue physicalUnit _ =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit

def P93SpiroClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93SpiroClaim → Prop
  | P93SpiroClaim.system systemValue => systemValue.MechanicallyValidFor source
  | P93SpiroClaim.unit systemValue (.polyhedron center positions) =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPrintedPolyhedralCarrierEnvelope source center positions ∧
        P93SpiroUnitSupported systemValue (.polyhedron center positions)
  | P93SpiroClaim.unit systemValue physicalUnit =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        P93SpiroUnitSupported systemValue physicalUnit
  | P93SpiroClaim.citation token (.polyhedron center positions) =>
      token.Valid ∧
        P93CanonicalPrintedPolyhedralCarrierEnvelope source center positions
  | P93SpiroClaim.citation token physicalUnit =>
      token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93SpiroClaim.pattern systemValue _
  | P93SpiroClaim.centerDescriptor systemValue _ _ _
  | P93SpiroClaim.xababOrder systemValue _
  | P93SpiroClaim.axialCenterDescriptor systemValue _
  | P93SpiroClaim.axialDescriptor systemValue _ => systemValue.MechanicallyValidFor source
  | P93SpiroClaim.doubleBondRing systemValue physicalUnit ring =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        (ring = systemValue.firstRing ∨ ring = systemValue.secondRing)
  | P93SpiroClaim.doubleBondGeometry physicalUnit _ =>
      P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93SpiroClaim.doubleBondNaming systemValue physicalUnit _ _ =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93SpiroClaim.coordination systemValue positions _
  | P93SpiroClaim.polyhedralDescriptor systemValue positions _ _ =>
      systemValue.MechanicallyValidFor source ∧ positions.toList ≠ []

def P93FusedClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93FusedClaim → Prop
  | P93FusedClaim.cipObservation observation => observation.ValidFor source
  | P93FusedClaim.relationObservation observation => observation.ValidFor source
  | P93FusedClaim.system systemValue => systemValue.MechanicallyValidFor source
  | P93FusedClaim.unit systemValue (.physical physicalUnit) =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        P93FusedPhysicalUnitSupported systemValue physicalUnit
  | P93FusedClaim.unit systemValue (.fusedAxis path)
  | P93FusedClaim.axis systemValue path =>
      systemValue.MechanicallyValidFor source ∧ 2 ≤ path.length ∧ path.Nodup ∧
        P93AuthorityAtomsBounded source path ∧ P93AuthorityCanonicalDirectedPath path ∧
        P93AuthorityConnectedPath source path ∧ ∀ atom ∈ path, atom ∈ systemValue.atoms
  | P93FusedClaim.citation token (.physical physicalUnit) =>
      token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93FusedClaim.citation token (.fusedAxis path) =>
      token.Valid ∧ 2 ≤ path.length ∧ path.Nodup ∧
        P93AuthorityAtomsBounded source path ∧ P93AuthorityCanonicalDirectedPath path ∧
        P93AuthorityConnectedPath source path
  | P93FusedClaim.unitDescriptor systemValue (.physical physicalUnit) descriptor =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        P93FusedPhysicalUnitSupported systemValue physicalUnit ∧
        P93FusedUnitDescriptorMatches (.physical physicalUnit) descriptor
  | P93FusedClaim.unitDescriptor systemValue (.fusedAxis path) descriptor =>
      systemValue.MechanicallyValidFor source ∧ 2 ≤ path.length ∧ path.Nodup ∧
        P93AuthorityAtomsBounded source path ∧ P93AuthorityCanonicalDirectedPath path ∧
        P93AuthorityConnectedPath source path ∧
        (∀ atom ∈ path, atom ∈ systemValue.atoms) ∧
        P93FusedUnitDescriptorMatches (.fusedAxis path) descriptor
  | P93FusedClaim.fusionPair systemValue first second =>
      systemValue.MechanicallyValidFor source ∧ P93AuthorityFusionAtom systemValue first ∧
        P93AuthorityFusionAtom systemValue second ∧ first ≠ second
  | P93FusedClaim.nearestCandidate systemValue first second distance _ =>
      systemValue.MechanicallyValidFor source ∧ P93AuthorityFusionAtom systemValue first ∧
        P93AuthorityFusionAtom systemValue second ∧ 0 < distance
  | P93FusedClaim.fusionCitation systemValue first second token =>
      systemValue.MechanicallyValidFor source ∧ P93AuthorityFusionAtom systemValue first ∧
        P93AuthorityFusionAtom systemValue second ∧ token.Valid
  | P93FusedClaim.fusionRelation systemValue first second _ _ _ =>
      systemValue.MechanicallyValidFor source ∧ P93AuthorityFusionAtom systemValue first ∧
        P93AuthorityFusionAtom systemValue second

def P93CyclophaneClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93CyclophaneClaim → Prop
  | P93CyclophaneClaim.system systemValue => systemValue.MechanicallyValidFor source
  | P93CyclophaneClaim.unit systemValue (.plane members) =>
      systemValue.MechanicallyValidFor source ∧
        (∃ pilot firstReference secondReference inPlaneBondAtom outOfPlaneAtom,
          P93CanonicalPrintedPlaneCarrierEnvelope source members pilot firstReference
            secondReference inPlaneBondAtom outOfPlaneAtom) ∧
        P93CyclophaneUnitSupported systemValue (.plane members)
  | P93CyclophaneClaim.unit systemValue physicalUnit =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        P93CyclophaneUnitSupported systemValue physicalUnit
  | P93CyclophaneClaim.citation token (.plane members) =>
      token.Valid ∧
        ∃ pilot firstReference secondReference inPlaneBondAtom outOfPlaneAtom,
          P93CanonicalPrintedPlaneCarrierEnvelope source members pilot firstReference
            secondReference inPlaneBondAtom outOfPlaneAtom
  | P93CyclophaneClaim.citation token physicalUnit =>
      token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93CyclophaneClaim.planeReference systemValue (.plane members) _
  | P93CyclophaneClaim.planeOrder systemValue (.plane members) _ _
  | P93CyclophaneClaim.planeDescriptor systemValue (.plane members) _ _ =>
      systemValue.MechanicallyValidFor source ∧
        (∃ pilot firstReference secondReference inPlaneBondAtom outOfPlaneAtom,
          P93CanonicalPrintedPlaneCarrierEnvelope source members pilot firstReference
            secondReference inPlaneBondAtom outOfPlaneAtom) ∧
        P93CyclophaneUnitSupported systemValue (.plane members)
  | P93CyclophaneClaim.planeReference systemValue physicalUnit _
  | P93CyclophaneClaim.planeOrder systemValue physicalUnit _ _
  | P93CyclophaneClaim.planeDescriptor systemValue physicalUnit _ _ =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧
        P93CyclophaneUnitSupported systemValue physicalUnit
  | P93CyclophaneClaim.center systemValue centerAtom kind _ descriptor =>
      systemValue.MechanicallyValidFor source ∧ centerAtom ∈ systemValue.atomCarrier ∧
        DescriptorApplies kind descriptor
  | P93CyclophaneClaim.rctEligible systemValue centerAtom
  | P93CyclophaneClaim.rctSide systemValue centerAtom _ =>
      systemValue.MechanicallyValidFor source ∧ centerAtom ∈ systemValue.atomCarrier
  | P93CyclophaneClaim.rctCandidate systemValue centerAtom token _ _ =>
      systemValue.MechanicallyValidFor source ∧ centerAtom ∈ systemValue.atomCarrier ∧
        token.Valid
  | P93CyclophaneClaim.doubleBondRing systemValue physicalUnit ring phaneRing =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit ∧ ring ∈ systemValue.rings ∧
        (ring, phaneRing) ∈ systemValue.ringPhaneCycles
  | P93CyclophaneClaim.doubleBondGeometry physicalUnit _
  | P93CyclophaneClaim.carbonDoubleBondContext physicalUnit _ =>
      P93CanonicalPhysicalUnitEnvelope source physicalUnit
  | P93CyclophaneClaim.doubleBondNaming systemValue physicalUnit _ _ =>
      systemValue.MechanicallyValidFor source ∧
        P93CanonicalPhysicalUnitEnvelope source physicalUnit

def P93FullereneClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93FullereneClaim → Prop
  | P93FullereneClaim.methodologyDecisionRule =>
      P93FullereneFourWaySubstitutionDecisionRule
  | P93FullereneClaim.printedObservation observationValue
  | P93FullereneClaim.printedSuperimposedObservation observationValue =>
      observationValue.ValidFor source
  | P93FullereneClaim.rawMolecule molecule => molecule.AuthoritativeStructureAgreement source
  | P93FullereneClaim.inputFamily molecule inputs =>
      molecule.AuthoritativeStructureAgreement source ∧ inputs ≠ [] ∧
        ∃ spatial, source.spatial? = some spatial ∧
          ∀ input ∈ inputs,
            SpatiallyDerivedMolecularFullereneConfigurationInputJudgment molecule spatial input
  | P93FullereneClaim.substitutionEvidence molecule input evidence =>
      molecule.AuthoritativeStructureAgreement source ∧
        MolecularFullereneSubstitutionEvidenceJudgment input evidence
  | P93FullereneClaim.preferredNumbering molecule input evidence =>
      molecule.AuthoritativeStructureAgreement source ∧
        MolecularFullereneNumberingEvidenceJudgment input evidence
  | P93FullereneClaim.originalChirality molecule input evidence value =>
      molecule.AuthoritativeStructureAgreement source ∧
        MolecularFullereneSubstitutionEvidenceJudgment input evidence ∧
        value = evidence.originalDerivativeChiral
  | P93FullereneClaim.substituentUnit molecule input evidence site unit =>
      molecule.AuthoritativeStructureAgreement source ∧
        MolecularFullereneSubstitutionEvidenceJudgment input evidence ∧
        site ∈ evidence.chiralSubstituentSites ∧
        P93CanonicalPhysicalUnitEnvelope source unit.toPhysicalUnit
  | P93FullereneClaim.substituentCitation molecule input site token unit =>
      molecule.AuthoritativeStructureAgreement source ∧ site ∈ input.carrier ∧
        token.Valid ∧ P93CanonicalPhysicalUnitEnvelope source unit.toPhysicalUnit
  | P93FullereneClaim.substituentDescriptor molecule input site unit descriptor =>
      molecule.AuthoritativeStructureAgreement source ∧ site ∈ input.carrier ∧
        P93CanonicalPhysicalUnitEnvelope source unit.toPhysicalUnit ∧
        P93FullereneSubstituentDescriptorMatchesUnit descriptor unit

def P93RingAssemblyClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93RingAssemblyClaim → Prop
  | P93RingAssemblyClaim.assembly assemblyValue => assemblyValue.MechanicallyValidFor source
  | P93RingAssemblyClaim.normalization result =>
      result.result.parsed.AuthoritativeStructureAgreement source ∧
        result.result = normalizeRawMolecule result.result.parsed
  | P93RingAssemblyClaim.axisEligible assemblyValue junction
      => assemblyValue.MechanicallyValidFor source ∧ junction ∈ assemblyValue.junctions
  | P93RingAssemblyClaim.axisCitation assemblyValue junction token =>
      assemblyValue.MechanicallyValidFor source ∧ junction ∈ assemblyValue.junctions
        ∧ token.Valid
  | P93RingAssemblyClaim.axisDescriptors assemblyValue junction preferred general =>
      assemblyValue.MechanicallyValidFor source ∧ junction ∈ assemblyValue.junctions ∧
        PreferredRingAssemblyAxisDescriptor preferred ∧
        (general = .Ra ∨ general = .Sa)
  | P93RingAssemblyClaim.centerEligible assemblyValue center
  | P93RingAssemblyClaim.centerDescriptor assemblyValue center _
  | P93RingAssemblyClaim.centerGeneralEquivalent assemblyValue center _ _ =>
      assemblyValue.MechanicallyValidFor source ∧ center < source.molecule.atomCount
  | P93RingAssemblyClaim.centerCitation assemblyValue center token =>
      assemblyValue.MechanicallyValidFor source ∧ center < source.molecule.atomCount ∧ token.Valid
  | P93RingAssemblyClaim.doubleBondStereogenic assemblyValue ringIndex first second
  | P93RingAssemblyClaim.doubleBondNeedsSpecification assemblyValue ringIndex first second
  | P93RingAssemblyClaim.doubleBondDescriptor assemblyValue ringIndex first second _ =>
      assemblyValue.MechanicallyValidFor source ∧
        P93RingAssemblyBondInRing source assemblyValue ringIndex first second
  | P93RingAssemblyClaim.doubleBondCitation assemblyValue ringIndex first second token =>
      assemblyValue.MechanicallyValidFor source ∧
        P93RingAssemblyBondInRing source assemblyValue ringIndex first second ∧ token.Valid

def P93CoupledClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93CoupledClaim → Prop
  | P93CoupledClaim.baseName name certificate => certificate.ValidFor source name
  | P93CoupledClaim.multiplicativeDecision name _ => name.Valid
  | P93CoupledClaim.eligibleUnit name unit =>
      name.Valid ∧ ∀ atom ∈ unit.atoms, atom < source.molecule.atomCount
  | P93CoupledClaim.evidenceBelongs name evidence =>
      name.Valid ∧ ∀ atom ∈ evidence.unit.atoms, atom < source.molecule.atomCount ∧
        ∀ citation, citation ∈ evidence.citation? → citation.Valid
  | P93CoupledClaim.citation name token unit =>
      name.Valid ∧ token.Valid ∧
        ∀ atom ∈ unit.atoms, atom < source.molecule.atomCount
  | P93CoupledClaim.repeatedComponents name components =>
      name.Valid ∧ P93RingChainRepeatedComponentsValid source components

def P93SourceClaim.SourceEnvelope
    (source : AuthoritativeChemicalInput) : P93SourceClaim → Prop
  | P93SourceClaim.physical claim => claim.SourceEnvelope source
  | P93SourceClaim.general claim => claim.SourceEnvelope source
  | P93SourceClaim.noncarbon claim => claim.SourceEnvelope source
  | P93SourceClaim.acyclic claim => claim.SourceEnvelope source
  | P93SourceClaim.monocyclic claim => claim.SourceEnvelope source
  | P93SourceClaim.vonBaeyer claim => claim.SourceEnvelope source
  | P93SourceClaim.spiro claim => claim.SourceEnvelope source
  | P93SourceClaim.fused claim => claim.SourceEnvelope source
  | P93SourceClaim.cyclophane claim => claim.SourceEnvelope source
  | P93SourceClaim.fullerene claim => claim.SourceEnvelope source
  | P93SourceClaim.ringAssembly claim => claim.SourceEnvelope source
  | P93SourceClaim.coupled claim => claim.SourceEnvelope source

/-! ## Payload-first clause observations -/

abbrev P93CanonicalGeneralConfiguration := P93AuthorityConfiguration P93CanonicalDescriptor

structure P93CanonicalGeneralScopedAssignment where
  located : P93AuthorityLocatedAssignment P93CanonicalDescriptor
  scope : GeneralConfiguration.AssignmentScope

structure P93CanonicalGeneralScopePlan where
  assignments : List P93CanonicalGeneralScopedAssignment

inductive P93GeneralClausePayload : Remaining71P93GeneralAuthorityRow → Type where
  | absolute (configuration : P93CanonicalGeneralConfiguration) :
      P93GeneralClausePayload .absoluteConfiguration
  | relative (first second : P93CanonicalGeneralConfiguration)
      (leading : P93AuthorityLocatedAssignment P93CanonicalDescriptor) :
      P93GeneralClausePayload .relativeConfiguration
  | mixed (configuration : P93CanonicalGeneralConfiguration)
      (plan : P93CanonicalGeneralScopePlan)
      (observedTypography : List
        (P93AuthorityCitationToken × GeneralConfiguration.DescriptorTypography)) :
      P93GeneralClausePayload .mixedAbsoluteRelativeConfiguration
  | racemate (mixture : GeneralConfiguration.BinaryMixture P93CanonicalGeneralConfiguration)
      (leading : P93AuthorityLocatedAssignment P93CanonicalDescriptor) :
      P93GeneralClausePayload .racemates
  | ambo (citation : P93AuthorityCitationToken)
      (mixture : GeneralConfiguration.QualitativeBinaryMixture
        P93CanonicalGeneralConfiguration) :
      P93GeneralClausePayload .ambo

def P93CanonicalGeneralConfiguration.toClaims
    (configuration : P93CanonicalGeneralConfiguration) : List P93SourceClaim :=
  configuration.assignments.flatMap fun assignment =>
    [.general (.citation assignment.citation assignment.unit),
      .general (.descriptor assignment.unit assignment.descriptor)]

def P93GeneralClausePayload.toClaims {row : Remaining71P93GeneralAuthorityRow} :
    P93GeneralClausePayload row → List P93SourceClaim
  | .absolute configuration => configuration.toClaims
  | .relative first second leading =>
      first.toClaims ++ second.toClaims ++ [.general (.preferredAtLowest leading.descriptor)]
  | .mixed configuration _ _ => configuration.toClaims
  | .racemate mixture leading =>
      mixture.first.toClaims ++ mixture.second.toClaims ++
        [.general (.preferredAtLowest leading.descriptor)]
  | .ambo _ mixture => mixture.first.toClaims ++ mixture.second.toClaims

def P93CanonicalGeneralConfiguration.StructurallyComplete
    (configuration : P93CanonicalGeneralConfiguration) : Prop :=
  configuration.assignments ≠ [] ∧
    (configuration.assignments.map fun assignment => assignment.unit).Nodup ∧
    (configuration.assignments.map fun assignment => assignment.citation).Nodup

def P93CanonicalGeneralLeading
    (configuration : P93CanonicalGeneralConfiguration)
    (leading : P93AuthorityLocatedAssignment P93CanonicalDescriptor) : Prop :=
  leading ∈ configuration.assignments ∧
    leading.descriptor.GeneralRepresentativeEligible ∧
    leading.descriptor.mirror ≠ leading.descriptor ∧
    leading.descriptor.PreferredAtLowest ∧
    (∀ assignment ∈ configuration.assignments,
      assignment.descriptor.GeneralRepresentativeEligible ∧
          assignment.descriptor.mirror ≠ assignment.descriptor →
        leading.citation.CitationLE assignment.citation)

def P93CanonicalGeneralInvertAt
    (citation : P93AuthorityCitationToken)
    (configuration : P93CanonicalGeneralConfiguration) : P93CanonicalGeneralConfiguration where
  assignments := configuration.assignments.map fun assignment =>
    if assignment.citation = citation then
      { assignment with descriptor := assignment.descriptor.localInvert }
    else assignment

def P93CanonicalMixedRelativeGroupsNontrivial
    (plan : P93CanonicalGeneralScopePlan) : Prop :=
  ∀ group,
    (∃ assignment ∈ plan.assignments, assignment.scope = .relative group) →
      2 ≤ (plan.assignments.filter fun assignment =>
        decide (assignment.scope = .relative group)).length ∧
      ∃ assignment ∈ plan.assignments,
        assignment.scope = .relative group ∧
          assignment.located.descriptor.GeneralRepresentativeEligible ∧
            assignment.located.descriptor.mirror ≠ assignment.located.descriptor

def P93GeneralClausePayload.Intrinsic {row : Remaining71P93GeneralAuthorityRow} :
    P93GeneralClausePayload row → Prop
  | .absolute configuration => configuration.StructurallyComplete
  | .relative first second leading =>
      first.StructurallyComplete ∧ P93CanonicalGeneralLeading first leading ∧
        P93AuthorityConfiguration.RelativeEquivalent
          P93CanonicalDescriptor.mirrorAction first second
  | .mixed configuration plan typography =>
      configuration.StructurallyComplete ∧
        plan.assignments.map (fun assignment => assignment.located) = configuration.assignments ∧
        (∃ assignment ∈ plan.assignments, assignment.scope = .absolute) ∧
        (∃ assignment ∈ plan.assignments, ∃ group,
          assignment.scope = .relative group) ∧
        P93CanonicalMixedRelativeGroupsNontrivial plan ∧
        typography = plan.assignments.map fun assignment =>
          (assignment.located.citation,
            match assignment.scope with
            | .absolute => .plain
            | .relative _ => .starred)
  | .racemate mixture leading =>
      mixture.first.StructurallyComplete ∧ P93CanonicalGeneralLeading mixture.first leading ∧
        mixture.Valid ∧
        mixture.second = mixture.first.globallyMirrored P93CanonicalDescriptor.mirrorAction ∧
        mixture.first ≠ mixture.second ∧ mixture.firstFraction = (1 : ℚ) / 2
  | .ambo citation mixture =>
      mixture.first.StructurallyComplete ∧ mixture.composition = .nonEquimolar ∧
        (∃ assignment ∈ mixture.first.assignments,
          assignment.citation = citation ∧
            P93CanonicalDescriptor.localInvert assignment.descriptor ≠
              assignment.descriptor) ∧
        mixture.second = P93CanonicalGeneralInvertAt citation mixture.first ∧
        ¬P93AuthorityConfiguration.RelativeEquivalent
          P93CanonicalDescriptor.mirrorAction mixture.first mixture.second ∧
        mixture.first ≠ mixture.second

structure P93NoncarbonAssignmentPayload where
  frame : P93NoncarbonTetrahedralFrame
  descriptor : P93CanonicalDescriptor

inductive P93NoncarbonClausePayload : Remaining71P93NoncarbonAuthorityRow → Type where
  | tetrahedra (a : P93NoncarbonAssignmentPayload) :
      P93NoncarbonClausePayload .otherElementTetrahedra
  | methodology (a : P93NoncarbonAssignmentPayload)
      (citation? : Option P93AuthorityCitationToken)
      (citationRule : BlueBookP93.NoncarbonTetrahedra.DescriptorCitationObservation) :
      P93NoncarbonClausePayload .otherElementGeneralMethodology
  | onic (a : P93NoncarbonAssignmentPayload)
      (family : BlueBookP93.NoncarbonTetrahedra.OnicCenter) :
      P93NoncarbonClausePayload .azaniumPhosphanium
  | oxide (a : P93NoncarbonAssignmentPayload) (oxygen : Nat)
      (family : BlueBookP93.NoncarbonTetrahedra.OxideCenter)
      (first second : BlueBookP93.NoncarbonTetrahedra.WrittenBondingToOxygen) :
      P93NoncarbonClausePayload .aminePhosphaneOxides
  | phosphorus (a : P93NoncarbonAssignmentPayload) (oxygen : Nat)
      (family : BlueBookP93.NoncarbonTetrahedra.PhosphorusOxoFamily)
      (firstDouble secondDouble : Bool)
      (firstCharges secondCharges : BlueBookP93.NoncarbonTetrahedra.FormalChargeArrangement) :
      P93NoncarbonClausePayload .phosphatesPhosphonates
  | chalcogen (a : P93NoncarbonAssignmentPayload) (oxygen : Nat)
      (family : BlueBookP93.NoncarbonTetrahedra.ChalcogenOxoFamily)
      (firstDouble secondDouble : Bool)
      (firstCharges secondCharges : BlueBookP93.NoncarbonTetrahedra.FormalChargeArrangement) :
      P93NoncarbonClausePayload .sulfatesSulfonates
  | group14 (a : P93NoncarbonAssignmentPayload)
      (family : BlueBookP93.NoncarbonTetrahedra.NoncarbonGroup14Center) :
      P93NoncarbonClausePayload .group14Noncarbon

def P93NoncarbonAssignmentPayload.baseClaims
    (a : P93NoncarbonAssignmentPayload) : List P93SourceClaim :=
  [.noncarbon (.tetrahedral a.frame.center a.frame.ligands),
    .noncarbon (.descriptor (.atomCenter a.frame.center) a.descriptor)]

def P93NoncarbonClausePayload.toClaims {row : Remaining71P93NoncarbonAuthorityRow} :
    P93NoncarbonClausePayload row → List P93SourceClaim
  | .tetrahedra a | .onic a _ | .group14 a _ => a.baseClaims
  | .methodology a citation? _ => a.baseClaims ++
      citation?.toList.map fun citation =>
        .noncarbon (.citation citation (.atomCenter a.frame.center))
  | .oxide a oxygen family first second => a.baseClaims ++
      [.noncarbon (.oxideVariant a.frame.center oxygen family first),
        .noncarbon (.oxideVariant a.frame.center oxygen family second)]
  | .phosphorus a oxygen family firstDouble secondDouble firstCharges secondCharges =>
      a.baseClaims ++
      [.noncarbon (.phosphorusOxo a.frame.center oxygen family firstDouble firstCharges),
        .noncarbon (.phosphorusOxo a.frame.center oxygen family secondDouble secondCharges)]
  | .chalcogen a oxygen family firstDouble secondDouble firstCharges secondCharges =>
      a.baseClaims ++
      [.noncarbon (.chalcogenOxo a.frame.center oxygen family firstDouble firstCharges),
        .noncarbon (.chalcogenOxo a.frame.center oxygen family secondDouble secondCharges)]

def P93NoncarbonClausePayload.Intrinsic
    {row : Remaining71P93NoncarbonAuthorityRow} (source : AuthoritativeChemicalInput) :
    P93NoncarbonClausePayload row → Prop
  | .tetrahedra a => a.frame.StructurallyValidFor source
  | .methodology a citation? rule =>
      a.frame.StructurallyValidFor source ∧
        (∃ atom, source.molecule.atoms[a.frame.center]? = some atom ∧
          P93NoncarbonCentralElementFamilyMatches
            rule.centralElement atom.element.atomicNumber) ∧
        (match rule.locant with
        | .none => citation? = none
        | .numerical => ∃ citation, citation? = some citation ∧ citation.Valid
        | .letter => False) ∧ CitationConforms rule
  | .onic a family =>
      a.frame.StructurallyValidFor source ∧
        P93NoncarbonElementAt source a.frame.center (P93NoncarbonOnicAtomicNumber family)
  | .oxide a oxygen family first second =>
      a.frame.StructurallyValidFor source ∧
        P93NoncarbonElementAt source a.frame.center (P93NoncarbonOxideAtomicNumber family) ∧
        oxygen ∈ a.frame.ligands ∧ P93NoncarbonElementAt source oxygen 8 ∧
        P93AuthorityBinaryBond source a.frame.center oxygen ∧ first ≠ second ∧
        oxideLigandCount family first = oxideLigandCount family second
  | .phosphorus a oxygen family firstDouble secondDouble firstCharges secondCharges =>
      a.frame.StructurallyValidFor source ∧ P93NoncarbonElementAt source a.frame.center 15 ∧
        oxygen ∈ a.frame.ligands ∧ P93NoncarbonElementAt source oxygen 8 ∧
        P93AuthorityBinaryBond source a.frame.center oxygen ∧
        (firstDouble, firstCharges) ≠ (secondDouble, secondCharges) ∧
        phosphorusOxoEffectiveBondOrder family firstDouble =
          phosphorusOxoEffectiveBondOrder family secondDouble ∧
        SameConfigurationIgnoringFormalCharges firstCharges secondCharges
  | .chalcogen a oxygen family firstDouble secondDouble firstCharges secondCharges =>
      a.frame.StructurallyValidFor source ∧
        (∃ atom, source.molecule.atoms[a.frame.center]? = some atom ∧
          P93NoncarbonChalcogenOxoFamilyMatches family atom.element.atomicNumber) ∧
        oxygen ∈ a.frame.ligands ∧ P93NoncarbonElementAt source oxygen 8 ∧
        P93AuthorityBinaryBond source a.frame.center oxygen ∧
        (firstDouble, firstCharges) ≠ (secondDouble, secondCharges) ∧
        UsesPhosphateConfigurationTreatment family ∧
        phosphorusOxoEffectiveBondOrder .related firstDouble =
          phosphorusOxoEffectiveBondOrder .related secondDouble ∧
        SameConfigurationIgnoringFormalCharges firstCharges secondCharges
  | .group14 a family =>
      a.frame.StructurallyValidFor source ∧
        P93NoncarbonElementAt source a.frame.center (P93NoncarbonGroup14AtomicNumber family) ∧
        UsesCarbonTetrahedralMethod family

structure P93AcyclicBasePayload where
  unit : P93AuthorityPhysicalUnit
  citation? : Option P93AuthorityCitationToken
  component : P93CanonicalNameComponent
  kind : UnitKind
  descriptor : BlueBookP93.Acyclic.Descriptor

structure P93AcyclicPlacedPayload where
  assignment : P93AcyclicBasePayload
  observedPosition : CitationPosition P93CanonicalNameComponent

inductive P93AcyclicClausePayload : Remaining71P93AcyclicAuthorityRow → Type where
  | centers (base : P93AcyclicBasePayload) : P93AcyclicClausePayload .acyclicCenters
  | single (base : P93AcyclicBasePayload) (needsLocant isotopePresent : Bool)
      (affixes : List AffixKind) : P93AcyclicClausePayload .singleAcyclicCenter
  | multipleCenters (assignments : List P93AcyclicBasePayload) :
      P93AcyclicClausePayload .multipleDescriptorsOneCenter
  | prefix (base : P93AcyclicBasePayload)
      (observedPosition : CitationPosition P93CanonicalNameComponent) :
      P93AcyclicClausePayload .prefixComponentCenters
  | ordinaryDouble (base : P93AcyclicBasePayload) :
      P93AcyclicClausePayload .ordinaryDoubleBonds
  | ezCisTrans (base : P93AcyclicBasePayload) (context : NomenclatureContext)
      (carbonContext : CarbonDoubleBondContext) :
      P93AcyclicClausePayload .doubleBondEZCisTrans
  | multipleDouble (assignments : List P93AcyclicBasePayload) :
      P93AcyclicClausePayload .multipleDoubleBonds
  | heteroDouble (base : P93AcyclicBasePayload) (context : NomenclatureContext) :
      P93AcyclicClausePayload .heteroatomDoubleBonds
  | evenCumulene (base : P93AcyclicBasePayload) (context : NomenclatureContext)
      (generalDescriptor preferredDescriptor : BlueBookP93.Acyclic.Descriptor) :
      P93AcyclicClausePayload .evenCumulenes
  | oddCumulene (base : P93AcyclicBasePayload) (path : List Nat)
      (geometry : OddCumuleneTerminalGeometry) : P93AcyclicClausePayload .oddCumulenes
  | multipleUnits (assignments : List P93AcyclicPlacedPayload)
      (competition : P93AcyclicNumberingCompetition) :
      P93AcyclicClausePayload .multipleAcyclicStereogenicUnits

def P93AcyclicBasePayload.baseClaims (base : P93AcyclicBasePayload) : List P93SourceClaim :=
  (base.citation?.toList.map fun citation => .acyclic (.citation citation base.unit)) ++
    [.acyclic (.component base.component base.unit), .acyclic (.unit base.unit),
      .acyclic (.unitKind base.unit base.kind), .acyclic (.descriptor base.unit base.descriptor)]

def P93AcyclicBasePayload.triple
    (base : P93AcyclicBasePayload) :
    P93AuthorityPhysicalUnit × UnitKind × BlueBookP93.Acyclic.Descriptor :=
  (base.unit, base.kind, base.descriptor)

def P93AcyclicBasePresentCitations
    (assignments : List P93AcyclicBasePayload) : List P93AuthorityCitationToken :=
  assignments.filterMap fun assignment => assignment.citation?

def P93AcyclicClausePayload.toClaims {row : Remaining71P93AcyclicAuthorityRow} :
    P93AcyclicClausePayload row → List P93SourceClaim
  | .centers b | .ordinaryDouble b => b.baseClaims
  | .heteroDouble b _ | .evenCumulene b _ _ _ => b.baseClaims
  | .single b needs isotope affixes => b.baseClaims ++
      [.acyclic (.singleCenterNaming b.unit b.citation? needs isotope affixes)]
  | .multipleCenters assignments =>
      assignments.flatMap P93AcyclicBasePayload.baseClaims ++
        [.acyclic (.multipleCenterDescriptors
          (assignments.map P93AcyclicBasePayload.triple))]
  | .prefix b _ => b.baseClaims
  | .ezCisTrans b _ carbonContext => b.baseClaims ++
      [.acyclic (.carbonDoubleBondContext b.unit carbonContext)]
  | .multipleDouble assignments =>
      assignments.flatMap P93AcyclicBasePayload.baseClaims ++
      [.acyclic (.multipleDoubleBondCollection
          (assignments.map fun assignment => assignment.unit)),
        .acyclic (.multipleDoubleBondDescriptors
          (assignments.map P93AcyclicBasePayload.triple))]
  | .oddCumulene b path geometry => b.baseClaims ++
      [.acyclic (.oddCumuleneGeometry path geometry)]
  | .multipleUnits assignments competition =>
      assignments.flatMap (fun placed => placed.assignment.baseClaims) ++
        [.acyclic (.numberingCompetition
          (assignments.map fun placed =>
            (placed.assignment.unit, placed.assignment.citation?)) competition)]

def P93AcyclicBasePayload.Intrinsic (base : P93AcyclicBasePayload) : Prop :=
  base.component.Valid ∧
    P93AcyclicUnitKindMatchesPhysical base.kind base.unit ∧
    DescriptorApplies base.kind base.descriptor ∧
    ∀ citation, citation ∈ base.citation? → citation.Valid

def P93AcyclicPayloadPresentCitations
    (assignments : List P93AcyclicPlacedPayload) : List P93AuthorityCitationToken :=
  assignments.filterMap fun placed => placed.assignment.citation?




def P93AcyclicClausePayload.Intrinsic
    {row : Remaining71P93AcyclicAuthorityRow} : P93AcyclicClausePayload row → Prop
  | .centers base =>
      base.Intrinsic ∧
        (base.kind = .chiralCenter ∨ base.kind = .pseudoasymmetricCenter)
  | .single base needsLocant isotopePresent affixes =>
      base.Intrinsic ∧
        (base.kind = .chiralCenter ∨ base.kind = .pseudoasymmetricCenter) ∧
        SingleCenterLocantConforms
          { descriptor := base.descriptor
            locant? := base.citation?
            centerNeedsLocantInBaseName := needsLocant } ∧
        P93AcyclicAffixOrderConforms affixes ∧ .stereochemical ∈ affixes ∧
        (isotopePresent = true ↔ .isotopic ∈ affixes)
  | .multipleCenters assignments =>
      2 ≤ assignments.length ∧
        (∀ assignment ∈ assignments,
          assignment.Intrinsic ∧
            (assignment.kind = .chiralCenter ∨
              assignment.kind = .pseudoasymmetricCenter) ∧
            ∃ citation, assignment.citation? = some citation) ∧
        (assignments.map fun assignment => assignment.unit).Nodup ∧
        (P93AcyclicBasePresentCitations assignments).Nodup ∧
        (P93AcyclicBasePresentCitations assignments).Pairwise
          P93AuthorityCitationToken.CitationLE
  | .prefix base observedPosition =>
      base.Intrinsic ∧
        (base.kind = .chiralCenter ∨ base.kind = .pseudoasymmetricCenter) ∧
        CorrectComponentPlacement
          { locant := base.citation?
            component := base.component
            kind := base.kind
            descriptor := base.descriptor }
          observedPosition
  | .ordinaryDouble base =>
      base.Intrinsic ∧ base.kind = .ordinaryDoubleBond
  | .ezCisTrans base context carbonContext =>
      base.Intrinsic ∧ base.kind = .ordinaryDoubleBond ∧
        DescriptorRecommended context .ordinaryDoubleBond base.descriptor ∧
        ((base.descriptor = .cis ∨ base.descriptor = .trans) →
          CisTransGeneralApplicable carbonContext)
  | .multipleDouble assignments =>
      2 ≤ assignments.length ∧
        (∀ assignment ∈ assignments,
          assignment.Intrinsic ∧
            (assignment.kind = .ordinaryDoubleBond ∨
              assignment.kind = .heteroatomDoubleBond) ∧
            ∃ citation, assignment.citation? = some citation) ∧
        (assignments.map fun assignment => assignment.unit).Nodup ∧
        (P93AcyclicBasePresentCitations assignments).Nodup ∧
        (P93AcyclicBasePresentCitations assignments).Pairwise
          P93AuthorityCitationToken.CitationLE
  | .heteroDouble base context =>
      base.Intrinsic ∧ base.kind = .heteroatomDoubleBond ∧
        HeteroDoubleBondDescriptorRecommended context base.descriptor
  | .evenCumulene base context generalDescriptor preferredDescriptor =>
      base.Intrinsic ∧ base.kind = .evenDoubleBondCumulene ∧
        EvenCumuleneAxialDescriptorCorrespondence generalDescriptor preferredDescriptor ∧
        base.descriptor =
          (match context with
          | .preferredIUPACName => preferredDescriptor
          | .general => generalDescriptor) ∧
        DescriptorRecommended context .evenDoubleBondCumulene base.descriptor
  | .oddCumulene base path geometry =>
      base.Intrinsic ∧ base.kind = .oddDoubleBondCumulene ∧
        base.unit = .axis path ∧ OddCumuleneEZAssignment geometry base.descriptor
  | .multipleUnits assignments competition =>
      2 ≤ assignments.length ∧
        (∀ placed ∈ assignments,
          placed.assignment.Intrinsic ∧
            ∃ citation, placed.assignment.citation? = some citation ∧
              P93AcyclicGroupedDescriptorPlacement
                { locant := citation
                  component := placed.assignment.component
                  kind := placed.assignment.kind
                  descriptor := placed.assignment.descriptor }
                placed.observedPosition) ∧
        (assignments.map fun placed => placed.assignment.unit).Nodup ∧
        (P93AcyclicPayloadPresentCitations assignments).Nodup ∧
        (P93AcyclicPayloadPresentCitations assignments).Pairwise
          P93AuthorityCitationToken.CitationLE ∧
        match competition with
        | .unique => True
        | .competing alternativeCitations firstDifference =>
            alternativeCitations.Nodup ∧
              alternativeCitations.Perm (P93AcyclicPayloadPresentCitations assignments) ∧
              alternativeCitations ≠ P93AcyclicPayloadPresentCitations assignments ∧
              PreferredAtFirstDifference firstDifference

structure P93MonocyclicPhysicalPayload where
  ring : List Nat
  unit : P93AuthorityPhysicalUnit

structure P93MonocyclicCitedPayload extends P93MonocyclicPhysicalPayload where
  citation : P93AuthorityCitationToken

inductive P93MonocyclicClausePayload : Remaining71P93MonocyclicAuthorityRow → Type where
  | configurations (b : P93MonocyclicCitedPayload) (descriptor : P93CanonicalDescriptor)
      (knowledge : ConfigurationKnowledge) (notationValue : MonocycleNotation) :
      P93MonocyclicClausePayload .cyclicConfigurations
  | absoluteCenter (b : P93MonocyclicCitedPayload) (center : Nat) (kind : UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor) (knowledge : ConfigurationKnowledge)
      (notationValue : MonocycleNotation) : P93MonocyclicClausePayload .monocyclicAbsoluteCenters
  | achiralCenter (b : P93MonocyclicCitedPayload) (center : Nat) (kind : UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor) (knowledge : ConfigurationKnowledge)
      (notationValue : MonocycleNotation) : P93MonocyclicClausePayload .monocyclicAchiralCenters
  | cisTrans (ring : List Nat) (first second ligandA ligandB : Nat)
      (plane : RingPlaneObservation) (firstSide secondSide : RingSide)
      (descriptor : CisTrans) :
      P93MonocyclicClausePayload .monocyclicCisTrans
  | rct (ring : List Nat) (candidates : List P93MonocyclicRCTReferenceCandidate)
      (selected : P93MonocyclicRCTReferenceCandidate) (referenceSide : RingSide)
      (assignments : List P93MonocyclicRCTLocatedAssignment) :
      P93MonocyclicClausePayload .monocyclicRCT
  | unsaturated (b : P93MonocyclicPhysicalPayload) (topology : CyclicUnsaturationTopology)
      (count : Nat)
      (descriptor : ChiralCycloalkeneDescriptor) (contextIsPIN : Bool) :
      P93MonocyclicClausePayload .unsaturatedMonocycles
  | cyclicDouble (b : P93MonocyclicPhysicalPayload) (count : Nat)
      (geometry : MonocyclicSeniorLigandGeometry)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor) :
      P93MonocyclicClausePayload .cyclicDoubleBonds
  | exocyclicEZ (b : P93MonocyclicPhysicalPayload) (count : Nat) (opposite : Bool)
      (contextIsPIN : Bool) (method : ExocyclicNamingMethod)
      (treatment : ExocyclicSystemTreatment)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor) :
      P93MonocyclicClausePayload .exocyclicDoubleBondEZ
  | exocyclicOther (b : P93MonocyclicPhysicalPayload) (count : Nat) (opposite : Bool)
      (contextIsPIN : Bool) (method : ExocyclicNamingMethod)
      (treatment : ExocyclicSystemTreatment)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor) :
      P93MonocyclicClausePayload .exocyclicDoubleBondOther

def P93MonocyclicPhysicalPayload.baseClaims
    (b : P93MonocyclicPhysicalPayload) : List P93SourceClaim :=
  [.monocyclic (.ring b.ring), .monocyclic (.unitInRing b.ring b.unit)]

def P93MonocyclicCitedPayload.baseClaims
    (b : P93MonocyclicCitedPayload) : List P93SourceClaim :=
  b.toP93MonocyclicPhysicalPayload.baseClaims ++ [.monocyclic (.citation b.citation b.unit)]

def P93MonocyclicClausePayload.toClaims {row : Remaining71P93MonocyclicAuthorityRow} :
    P93MonocyclicClausePayload row → List P93SourceClaim
  | .configurations b d knowledge notationValue => b.baseClaims ++
      [.monocyclic (.generalDescriptor b.unit d),
        .monocyclic (.generalNotation b.unit knowledge notationValue)]
  | .absoluteCenter b center kind d knowledge notationValue => b.baseClaims ++
      [.monocyclic (.center center kind d knowledge notationValue)]
  | .achiralCenter b center kind d knowledge notationValue => b.baseClaims ++
      [.monocyclic (.center center kind d knowledge notationValue),
        .monocyclic (.achiralCenter center)]
  | .cisTrans ring first second ligandA ligandB plane sideA sideB _ =>
      [.monocyclic (.ring ring), .monocyclic (.ringPlane ring first second plane),
        .monocyclic (.ringSide ring ligandA sideA),
        .monocyclic (.ringSide ring ligandB sideB)]
  | .rct ring candidates selected referenceSide assignments =>
      [.monocyclic (.ring ring), .monocyclic (.ringSide ring selected.substituent referenceSide)] ++
      (candidates.flatMap fun c =>
        [.monocyclic (.citation c.citation (.atomCenter c.ringPosition)),
          .monocyclic (.rctCandidate ring c.ringPosition c.substituent c.citation
            c.namedAsSuffix c.sequencePriority)]) ++
      (assignments.map fun a => .monocyclic (.ringSide ring a.substituent a.side))
  | .unsaturated b topology count descriptor pin => b.baseClaims ++
      [.monocyclic (.unsaturation b.ring b.unit topology count),
        .monocyclic (.chiralCycloalkene b.unit descriptor pin)]
  | .cyclicDouble b count geometry _ => b.baseClaims ++
      [.monocyclic (.unsaturation b.ring b.unit .ordinaryCyclicDoubleBondSystem count),
        .monocyclic (.seniorGeometry b.unit geometry)]
  | .exocyclicEZ b count opposite pin method treatment descriptor
  | .exocyclicOther b count opposite pin method treatment descriptor => b.baseClaims ++
      [.monocyclic (.exocyclicSystem b.ring b.unit count opposite),
        .monocyclic (.exocyclicNaming b.unit pin method treatment descriptor)]

def P93MonocyclicPhysicalPayload.Intrinsic
    (source : AuthoritativeChemicalInput) (b : P93MonocyclicPhysicalPayload) : Prop :=
  P93AuthorityClosedCycle source b.ring

def P93MonocyclicClausePayload.Intrinsic
    {row : Remaining71P93MonocyclicAuthorityRow} (source : AuthoritativeChemicalInput) :
    P93MonocyclicClausePayload row → Prop
  | .configurations b _ knowledge notationValue =>
      b.toP93MonocyclicPhysicalPayload.Intrinsic source ∧ b.citation.Valid ∧
        notationValue = PreferredMonocycleNotation knowledge
  | .absoluteCenter b center kind descriptor knowledge notationValue =>
      b.toP93MonocyclicPhysicalPayload.Intrinsic source ∧ b.unit = .atomCenter center ∧
        (kind = .chiralCenter ∨ kind = .pseudoasymmetricCenter) ∧
        DescriptorApplies kind descriptor ∧ knowledge = .absolute ∧
        notationValue = PreferredMonocycleNotation knowledge ∧ b.citation.Valid
  | .achiralCenter b center kind descriptor knowledge notationValue =>
      b.toP93MonocyclicPhysicalPayload.Intrinsic source ∧ b.unit = .atomCenter center ∧
        (kind = .chiralCenter ∨ kind = .pseudoasymmetricCenter) ∧
        DescriptorApplies kind descriptor ∧
        notationValue = PreferredMonocycleNotation knowledge ∧ b.citation.Valid
  | .cisTrans ring first second ligandA ligandB plane firstSide secondSide descriptor =>
      P93AuthorityClosedCycle source ring ∧ first ∈ ring ∧ second ∈ ring ∧ first ≠ second ∧
        ligandA ≠ ligandB ∧ ligandA ∉ ring ∧ ligandB ∉ ring ∧
        P93AuthorityBinaryBond source first ligandA ∧
        P93AuthorityBinaryBond source second ligandB ∧ CisTransPlaneApplicable plane ∧
        RelativeRingSide firstSide secondSide descriptor
  | .rct ring candidates selected referenceSide assignments =>
      P93AuthorityClosedCycle source ring ∧ candidates ≠ [] ∧
        (candidates.map fun c => (c.ringPosition, c.substituent)).Nodup ∧
        (∀ candidate ∈ candidates,
          candidate.ringPosition ∈ ring ∧ candidate.substituent ∉ ring ∧
            P93AuthorityBinaryBond source candidate.ringPosition candidate.substituent ∧
            candidate.citation.Valid) ∧
        P93MonocyclicIsRCTReference candidates selected ∧ referenceSide ≠ .onMeanPlane ∧
        assignments ≠ [] ∧
        (assignments.map fun a => (a.ringPosition, a.substituent)).Nodup ∧
        (∀ candidate ∈ candidates, ∃ assignment ∈ assignments,
          assignment.ringPosition = candidate.ringPosition ∧
            assignment.substituent = candidate.substituent) ∧
        ∀ assignment ∈ assignments,
          (∃ candidate ∈ candidates,
            assignment.ringPosition = candidate.ringPosition ∧
              assignment.substituent = candidate.substituent) ∧
          if assignment.ringPosition = selected.ringPosition ∧
              assignment.substituent = selected.substituent then
            assignment.side = referenceSide ∧ assignment.descriptor = .reference
          else rctDescriptor referenceSide assignment.side = some assignment.descriptor
  | .unsaturated b topology _ descriptor contextIsPIN =>
      b.Intrinsic source ∧ topology = .ordinaryCyclicDoubleBondSystem ∧
        (contextIsPIN = true → PreferredChiralCycloalkeneDescriptor descriptor)
  | .cyclicDouble b count geometry descriptor? =>
      b.Intrinsic source ∧ (∃ first second, b.unit = .bond first second) ∧
        requiredMonocyclicEZDescriptor? b.ring.length count geometry = descriptor?
  | .exocyclicEZ b count opposite contextIsPIN method _treatment descriptor? =>
      b.Intrinsic source ∧
        ExocyclicMethodAllowed contextIsPIN count b.ring.length opposite method ∧
        (match method with
        | .integralParentDoubleBond | .ylideneSubstituent =>
            ∃ first second, b.unit = .bond first second
        | .wholeOddCumulene => ∃ path, b.unit = .axis path) ∧
        P93ExocyclicEZDescriptor descriptor?
  | .exocyclicOther b count opposite contextIsPIN method _treatment descriptor? =>
      b.Intrinsic source ∧
        ExocyclicMethodAllowed contextIsPIN count b.ring.length opposite method ∧
        (match method with
        | .integralParentDoubleBond | .ylideneSubstituent =>
            ∃ first second, b.unit = .bond first second
        | .wholeOddCumulene => ∃ path, b.unit = .axis path) ∧
        P93ExocyclicOtherDescriptor descriptor?

structure P93SystemUnitPayload (System Unit : Type) where
  system : System
  unit : Unit
  citation : P93AuthorityCitationToken

inductive P93CanonicalVonBaeyerUnsaturation where
  | ordinary (contextIsPIN larger : Bool) (geometry : MonocyclicSeniorLigandGeometry)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor)
  | included (context : NomenclatureContext) (parity : OpenCumuleneParity)
      (descriptor : BlueBookP93.Acyclic.Descriptor)

inductive P93VonBaeyerClausePayload : Remaining71P93VonBaeyerAuthorityRow → Type where
  | cip (b : P93SystemUnitPayload P93AuthorityVonBaeyerSystem P93AuthorityPhysicalUnit)
      (center : Nat) (kind : UnitKind) (descriptor : BlueBookP93.Acyclic.Descriptor)
      (knowledge : ConfigurationKnowledge) (notationValue : MonocycleNotation) :
      P93VonBaeyerClausePayload .vonBaeyerCIPCenters
  | bridge (system : P93AuthorityVonBaeyerSystem) (attachment substituent : Nat)
      (citation : P93AuthorityCitationToken) (kind : BridgeAttachment)
      (descriptor : BridgeDescriptor) :
      P93VonBaeyerClausePayload .vonBaeyerEndoExoSynAnti
  | relative (system : P93AuthorityVonBaeyerSystem) (firstLigand secondLigand : Nat)
      (firstCitation? secondCitation? : Option P93AuthorityCitationToken)
      (firstSide secondSide : RingSide) (descriptor : CisTrans) (pin : Bool)
      (notationValue : BridgeheadRelativeNotation) : P93VonBaeyerClausePayload .vonBaeyerCisTrans
  | doubleBond (b : P93SystemUnitPayload P93AuthorityVonBaeyerSystem P93AuthorityPhysicalUnit)
      (specification : P93CanonicalVonBaeyerUnsaturation) :
      P93VonBaeyerClausePayload .vonBaeyerDoubleBonds

def P93VonBaeyerClausePayload.toClaims {row : Remaining71P93VonBaeyerAuthorityRow} :
    P93VonBaeyerClausePayload row → List P93SourceClaim
  | .cip b center kind d knowledge notationValue =>
      [.vonBaeyer (.system b.system), .vonBaeyer (.unit b.system b.unit),
        .vonBaeyer (.citation b.citation b.unit),
        .vonBaeyer (.center center kind d knowledge notationValue)]
  | .bridge system attachment substituent citation kind _ =>
      let unit := P93AuthorityPhysicalUnit.atomCenter attachment
      [.vonBaeyer (.system system), .vonBaeyer (.unit system unit),
        .vonBaeyer (.citation citation unit),
        .vonBaeyer (.bridgeAttachment system attachment substituent kind)]
  | .relative system firstLigand secondLigand firstCitation? secondCitation?
      firstSide secondSide _ pin notationValue =>
      [.vonBaeyer (.system system),
        .vonBaeyer (.bridgeheadSide system system.firstBridgehead firstLigand firstSide),
        .vonBaeyer (.bridgeheadSide system system.secondBridgehead secondLigand secondSide),
        .vonBaeyer (.relativeNotation system pin notationValue)] ++
      (firstCitation?.toList.map fun citation =>
        .vonBaeyer (.citation citation (.atomCenter system.firstBridgehead))) ++
      (secondCitation?.toList.map fun citation =>
        .vonBaeyer (.citation citation (.atomCenter system.secondBridgehead)))
  | .doubleBond b (.ordinary pin larger geometry descriptor) =>
      [.vonBaeyer (.system b.system), .vonBaeyer (.unit b.system b.unit),
        .vonBaeyer (.citation b.citation b.unit),
        .vonBaeyer (.largerThanBicyclo333 b.system larger),
        .vonBaeyer (.seniorGeometry b.unit geometry),
        .vonBaeyer (.doubleBondNaming b.system b.unit pin larger descriptor)]
  | .doubleBond b (.included context _ _) =>
      [.vonBaeyer (.system b.system), .vonBaeyer (.unit b.system b.unit),
        .vonBaeyer (.citation b.citation b.unit)] ++
      match b.unit with
      | .axis path =>
          [.vonBaeyer (.includedCumuleneNumbering b.system path b.citation),
            .vonBaeyer (.includedCumuleneContext b.system b.unit context)]
      | _ => []

def P93VonBaeyerClausePayload.Intrinsic
    {row : Remaining71P93VonBaeyerAuthorityRow} (source : AuthoritativeChemicalInput) :
    P93VonBaeyerClausePayload row → Prop
  | .cip b center kind descriptor knowledge notationValue =>
      b.system.MechanicallyValidFor source ∧ b.unit = .atomCenter center ∧
        P93VonBaeyerUnitSupported b.system b.unit ∧
        (kind = .chiralCenter ∨ kind = .pseudoasymmetricCenter) ∧
        DescriptorApplies kind descriptor ∧ knowledge = .absolute ∧
        notationValue = PreferredMonocycleNotation knowledge ∧ b.citation.Valid
  | .bridge system attachment substituent citation kind descriptor =>
      system.MechanicallyValidFor source ∧ EndoExoSynAntiApplicable system.dimensions ∧
        attachment ∈ system.atoms ∧ substituent ∉ system.atoms ∧
        P93AuthorityBinaryBond source attachment substituent ∧
        descriptor = bridgeDescriptor kind ∧ ¬BridgeDescriptorDeterminesAbsolute descriptor ∧
        citation.Valid
  | .relative system firstLigand secondLigand firstCitation? secondCitation?
      firstSide secondSide descriptor pin notationValue =>
      system.MechanicallyValidFor source ∧ firstLigand ≠ secondLigand ∧
        firstLigand ∉ system.atoms ∧ secondLigand ∉ system.atoms ∧
        P93AuthorityBinaryBond source system.firstBridgehead firstLigand ∧
        P93AuthorityBinaryBond source system.secondBridgehead secondLigand ∧
        RelativeRingSide firstSide secondSide descriptor ∧
        (pin = true → PreferredBridgeheadRelativeNotation notationValue) ∧
        (∀ citation, citation ∈ firstCitation? → citation.Valid) ∧
        (∀ citation, citation ∈ secondCitation? → citation.Valid) ∧
        (pin = true → ∃ firstCitation secondCitation,
          firstCitation? = some firstCitation ∧ secondCitation? = some secondCitation)
  | .doubleBond b (.ordinary pin larger geometry descriptor?) =>
      b.system.MechanicallyValidFor source ∧ P93VonBaeyerUnitSupported b.system b.unit ∧
        (∃ first second, b.unit = .bond first second) ∧ b.citation.Valid ∧
        P93VonBaeyerOrdinaryDescriptorAllowed descriptor? ∧
        (pin = true → descriptor? = P93VonBaeyerOrdinaryDoubleBondExpected larger geometry)
  | .doubleBond b (.included context parity descriptor) =>
      b.system.MechanicallyValidFor source ∧ P93VonBaeyerUnitSupported b.system b.unit ∧
        (∃ path, b.unit = .axis path) ∧ b.citation.Valid ∧
        OpenTerminalCumuleneDescriptorApplies .includedOpenCumuleneSegment parity descriptor ∧
        match parity with
        | .even => DescriptorRecommended context .evenDoubleBondCumulene descriptor
        | .odd => DescriptorRecommended context .oddDoubleBondCumulene descriptor

inductive P93SpiroClausePayload : Remaining71P93SpiroReadyAuthorityRow → Type where
  | xabcd (system : P93AuthoritySpiroSystem) (citation : P93AuthorityCitationToken)
      (descriptor : BlueBookP93.Acyclic.Descriptor) : P93SpiroClausePayload .spiroXabcd
  | xabab (system : P93AuthoritySpiroSystem) (citation : P93AuthorityCitationToken)
      (family : SpiroDescriptorFamily)
      (descriptor : BlueBookP93.Acyclic.Descriptor) (order : XababOccurrenceOrder) :
      P93SpiroClausePayload .spiroXabab
  | doubleBond (b : P93SystemUnitPayload P93AuthoritySpiroSystem P93AuthorityPhysicalUnit)
      (ring : List Nat) (geometry : MonocyclicSeniorLigandGeometry)
      (context : NomenclatureContext) (descriptor? : Option BlueBookP93.Acyclic.Descriptor) :
      P93SpiroClausePayload .spiroDoubleBonds
  | axial (system : P93AuthoritySpiroSystem) (citation : P93AuthorityCitationToken)
      (centerDescriptor descriptor : BlueBookP93.Acyclic.Descriptor) :
      P93SpiroClausePayload .spiroAxialChirality

def P93SpiroClausePayload.toClaims {row : Remaining71P93SpiroReadyAuthorityRow} :
    P93SpiroClausePayload row → List P93SourceClaim
  | .xabcd system citation d =>
      let unit := P93AuthorityPhysicalUnit.atomCenter system.center
      [.spiro (.system system), .spiro (.unit system unit),
        .spiro (.citation citation unit), .spiro (.pattern system .Xabcd),
        .spiro (.centerDescriptor system .Xabcd .centerRS d)]
  | .xabab system citation family d order =>
      let unit := P93AuthorityPhysicalUnit.atomCenter system.center
      [.spiro (.system system), .spiro (.unit system unit),
        .spiro (.citation citation unit), .spiro (.pattern system .Xabab),
        .spiro (.centerDescriptor system .Xabab family d), .spiro (.xababOrder system order)]
  | .doubleBond b ring geometry context descriptor =>
      [.spiro (.system b.system), .spiro (.unit b.system b.unit),
        .spiro (.citation b.citation b.unit), .spiro (.doubleBondRing b.system b.unit ring),
        .spiro (.doubleBondGeometry b.unit geometry),
        .spiro (.doubleBondNaming b.system b.unit context descriptor)]
  | .axial system citation centerDescriptor descriptor =>
      let unit := P93AuthorityPhysicalUnit.atomCenter system.center
      [.spiro (.system system), .spiro (.unit system unit),
        .spiro (.citation citation unit), .spiro (.pattern system .Xaabb),
        .spiro (.axialCenterDescriptor system centerDescriptor),
        .spiro (.axialDescriptor system descriptor)]

def P93SpiroClausePayload.Intrinsic
    {row : Remaining71P93SpiroReadyAuthorityRow} (source : AuthoritativeChemicalInput) :
    P93SpiroClausePayload row → Prop
  | .xabcd system citation descriptor =>
      system.MechanicallyValidFor source ∧ SpiroFamilySupported .Xabcd .centerRS ∧
        P93SpiroCenterDescriptorMatchesFamily .centerRS descriptor ∧ citation.Valid
  | .xabab system citation family descriptor order =>
      system.MechanicallyValidFor source ∧ SpiroFamilySupported .Xabab family ∧
        (family = .centerRS ∨ family = .centerRrSs) ∧ ValidXababOccurrenceOrder order ∧
        P93SpiroCenterDescriptorMatchesFamily family descriptor ∧ citation.Valid
  | .doubleBond b ring geometry context descriptor? =>
      b.system.MechanicallyValidFor source ∧ P93SpiroUnitSupported b.system b.unit ∧
        (∃ first second, b.unit = .bond first second ∧ first ∈ ring ∧ second ∈ ring) ∧
        P93SpiroRingBelongsToSystem b.system ring ∧
        P93SpiroGeneralDoubleBondDescriptorAllowed descriptor? ∧
        (context = .preferredIUPACName →
          descriptor? = P93SpiroDoubleBondExpected ring.length geometry) ∧ b.citation.Valid
  | .axial system citation centerDescriptor descriptor =>
      system.MechanicallyValidFor source ∧ SpiroFamilySupported .Xaabb .centerRS ∧
        SpiroFamilySupported .Xaabb .axialMP ∧
        P93SpiroCenterDescriptorMatchesFamily .centerRS centerDescriptor ∧
        P93SpiroCenterDescriptorMatchesFamily .axialMP descriptor ∧
        P93SpiroCenterAxialCorrespondence centerDescriptor descriptor ∧
        DescriptorRecommended .preferredIUPACName .chiralCenter centerDescriptor ∧ citation.Valid

/-- Exactly the qualitative polyhedral facts printed for one spiro example.  The molecule is
retained here so an executable source with idealized coordinates cannot be mistaken for a literal
coordinate transcription from the Blue Book figure. -/
structure P93CanonicalSpiroPrintedPolyhedralObservation where
  molecule : SemanticMolecule
  system : P93AuthoritySpiroSystem
  positions : Finset Nat
  citation : P93AuthorityCitationToken
  geometry : BlueBookP93.Geometry
  coordination : SpiroCenterCoordination
  knowledge : ConfigurationKnowledge
  descriptor : PolyhedralChiralitySymbol



structure P93CanonicalSpiroPolyhedralExecutableWitness where
  geometry : BlueBookP93.Geometry
  frame : P93AuthorityPolyhedralFrame

def P93SpiroCoordinationMatchesGeometry
    (coordination : SpiroCenterCoordination) (geometry : BlueBookP93.Geometry) : Prop :=
  match coordination with
  | .tetrahedral => geometry = .tetrahedron
  | .lambda4 => geometry.coordinationNumber = 4 ∧ geometry ≠ .tetrahedron
  | .lambda5 => geometry.coordinationNumber = 5
  | .lambda6 => geometry.coordinationNumber = 6

def P93CanonicalSpiroPolyhedralExecutableWitness.DescriptorAgrees
    (witness : P93CanonicalSpiroPolyhedralExecutableWitness)
    (descriptor : PolyhedralChiralitySymbol) : Prop :=
  ∃ sense,
    RedBookIR9.AbsoluteOrientationRecognized
      witness.frame.record.absoluteOrientation witness.geometry (some sense) ∧
    PolyhedralChiralitySymbol.ofRotation
      (PolyhedralRotationSense.ofIndependent sense) = descriptor

def P93CanonicalSpiroPolyhedralExecutableWitness.ValidFor
    (source : AuthoritativeChemicalInput)
    (printed : P93CanonicalSpiroPrintedPolyhedralObservation)
    (witness : P93CanonicalSpiroPolyhedralExecutableWitness) : Prop :=
  source.molecule = printed.molecule ∧ witness.geometry = printed.geometry ∧
    P93AuthorityPolyhedralFrame.ValidFor source printed.system.center
      printed.positions witness.geometry witness.frame ∧
    witness.DescriptorAgrees printed.descriptor

structure P93SpiroNontetrahedralPayload where
  printed : P93CanonicalSpiroPrintedPolyhedralObservation
  executable : P93CanonicalSpiroPolyhedralExecutableWitness

namespace P93SpiroNontetrahedralPayload

def system (p : P93SpiroNontetrahedralPayload) := p.printed.system
def positions (p : P93SpiroNontetrahedralPayload) := p.printed.positions
def citation (p : P93SpiroNontetrahedralPayload) := p.printed.citation
def geometry (p : P93SpiroNontetrahedralPayload) := p.printed.geometry
def coordination (p : P93SpiroNontetrahedralPayload) := p.printed.coordination
def knowledge (p : P93SpiroNontetrahedralPayload) := p.printed.knowledge
def descriptor (p : P93SpiroNontetrahedralPayload) := p.printed.descriptor

def toClaims (p : P93SpiroNontetrahedralPayload) :
    List P93SourceClaim :=
  let unit := P93AuthorityPhysicalUnit.polyhedron p.system.center p.positions
  [.spiro (.system p.system), .spiro (.unit p.system unit),
    .spiro (.citation p.citation unit),
    .spiro (.coordination p.system p.positions p.coordination),
    .spiro (.polyhedralDescriptor p.system p.positions p.knowledge p.descriptor)]

def Intrinsic
    (source : AuthoritativeChemicalInput) (p : P93SpiroNontetrahedralPayload) : Prop :=
  p.system.MechanicallyValidFor source ∧
    P93SpiroUnitSupported p.system (.polyhedron p.system.center p.positions) ∧
    P93CanonicalPrintedPolyhedralCarrierEnvelope source p.system.center p.positions ∧
    p.positions.card = p.geometry.coordinationNumber ∧
    P93SpiroCoordinationMatchesGeometry p.coordination p.geometry ∧
    PolyhedralACApplicable p.coordination ∧ p.citation.Valid ∧
    p.executable.ValidFor source p.printed

def exactQualitativePhysicalClaims
    (p : P93SpiroNontetrahedralPayload) : List P93PhysicalClaim :=
  [.polyhedron p.system.center p.positions p.executable.geometry p.executable.frame]

end P93SpiroNontetrahedralPayload

/-- Qualitative facts transcribed from one printed P-93.5.5.1 cyclophane drawing.  This record is
deliberately coordinate-free: `torsionRestricted` and `planeCannotBeSymmetryPlane` record the two
physical applicability observations, while the five atom roles record the planar `a-x-b`/`y-z`
construction.  The inherited `pilotAtom` field names the derived-tetrahedron center `x`; it is not
the distinct phane viewing-pilot atom used to establish the composite locant. -/
structure P93CanonicalCyclophanePrintedPlaneObservation where
  molecule : SemanticMolecule
  system : P93AuthorityCyclophaneSystem
  members : Finset Nat
  citation : P93AuthorityCitationToken
  reference : CyclophanePlaneReference
  high : Nat
  low : Nat
  pilotAtom : Nat
  inPlaneBondAtom : Nat
  outOfPlaneAtom : Nat
  context : NomenclatureContext
  descriptor : CyclophanePlaneDescriptor
  torsionRestricted : Bool
  planeCannotBeSymmetryPlane : Bool

/-- Exact rational reconstruction used only to prove the executable geometry judgment.  It is
not a claim that the Blue Book drawing printed these coordinates. -/
structure P93CanonicalCyclophanePlaneExecutableWitness where
  frame : P93AuthorityPlaneFrame

def P93CanonicalCyclophanePrintedPlaneObservation.ValidFor
    (source : AuthoritativeChemicalInput)
    (printed : P93CanonicalCyclophanePrintedPlaneObservation) : Prop :=
  source.molecule = printed.molecule ∧
    printed.system.MechanicallyValidFor source ∧
    P93CanonicalPrintedPlaneCarrierEnvelope source printed.members printed.pilotAtom
      printed.high printed.low printed.inPlaneBondAtom printed.outOfPlaneAtom ∧
    P93CyclophaneUnitSupported printed.system (.plane printed.members) ∧
    printed.torsionRestricted = true ∧
    printed.planeCannotBeSymmetryPlane = true ∧
    ValidCyclophanePlaneReference printed.reference ∧
    (printed.context = .preferredIUPACName →
      PreferredCyclophanePlaneDescriptor printed.descriptor) ∧
    printed.citation.Valid

def P93CanonicalCyclophanePlaneExecutableWitness.ValidFor
    (source : AuthoritativeChemicalInput)
    (printed : P93CanonicalCyclophanePrintedPlaneObservation)
    (executable : P93CanonicalCyclophanePlaneExecutableWitness) : Prop :=
  executable.frame.record.planeAtoms.toFinset = printed.members ∧
    executable.frame.record.pilotAtom = printed.pilotAtom ∧
    ((executable.frame.record.firstReference = printed.high ∧
        executable.frame.record.secondReference = printed.low) ∨
      (executable.frame.record.firstReference = printed.low ∧
        executable.frame.record.secondReference = printed.high)) ∧
    executable.frame.record.inPlaneBondAtom = printed.inPlaneBondAtom ∧
    executable.frame.record.outOfPlaneAtom = printed.outOfPlaneAtom ∧
    executable.frame.record.torsionRestricted = printed.torsionRestricted ∧
    executable.frame.record.planeCannotBeSymmetryPlane =
      printed.planeCannotBeSymmetryPlane ∧
    executable.frame.ValidFor source printed.members ∧
    ∃ spatial highPoint lowPoint inPlanePoint outOfPlanePoint general,
      source.spatial? = some spatial ∧
      BlueBookP94.CoordinateRing.SpatialPointAt spatial printed.high highPoint ∧
      BlueBookP94.CoordinateRing.SpatialPointAt spatial printed.low lowPoint ∧
      BlueBookP94.CoordinateRing.SpatialPointAt spatial printed.inPlaneBondAtom inPlanePoint ∧
      BlueBookP94.CoordinateRing.SpatialPointAt spatial printed.outOfPlaneAtom outOfPlanePoint ∧
      BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor
        highPoint lowPoint inPlanePoint outOfPlanePoint general ∧
      printed.descriptor =
        match printed.context with
        | .preferredIUPACName =>
            CyclophanePlaneDescriptor.preferredOfGeneralPlanar general
        | .general => CyclophanePlaneDescriptor.ofGeneralPlanar general

inductive P93FusedCyclophaneClausePayload : Remaining71P93FusedCyclophaneAuthorityRow → Type where
  | fusedCIP (observation : P93CanonicalFusedCIPObservation) :
      P93FusedCyclophaneClausePayload .fusedBridgedCIP
  | fusedRelation (observation : P93CanonicalFusedRelationObservation) :
      P93FusedCyclophaneClausePayload .cisoidTransoid
  | cyclophanePlanes (printed : P93CanonicalCyclophanePrintedPlaneObservation)
      (executable : P93CanonicalCyclophanePlaneExecutableWitness) :
      P93FusedCyclophaneClausePayload .cyclophanePlanes
  | cyclophaneCenters (system : P93AuthorityCyclophaneSystem)
      (unit : P93AuthorityPhysicalUnit) (citation : P93AuthorityCitationToken)
      (specification : P93CyclophaneCenterSpecification) :
      P93FusedCyclophaneClausePayload .cyclophaneCenters
  | cyclophaneDoubleBonds (system : P93AuthorityCyclophaneSystem)
      (unit : P93AuthorityPhysicalUnit) (citation : P93AuthorityCitationToken)
      (ring phaneRing : List Nat) (geometry : MonocyclicSeniorLigandGeometry)
      (carbonContext : CarbonDoubleBondContext) (context : NomenclatureContext)
      (descriptor? : Option BlueBookP93.Acyclic.Descriptor) :
      P93FusedCyclophaneClausePayload .cyclophaneDoubleBonds

def P93FusedCyclophaneClausePayload.toClaims
    {row : Remaining71P93FusedCyclophaneAuthorityRow} :
    P93FusedCyclophaneClausePayload row → List P93SourceClaim
  | .fusedCIP o => [.fused (.cipObservation o)]
  | .fusedRelation o => [.fused (.relationObservation o)]
  | .cyclophanePlanes printed _executable =>
      let unit := P93AuthorityPhysicalUnit.plane printed.members
      [.cyclophane (.system printed.system), .cyclophane (.unit printed.system unit),
        .cyclophane (.citation printed.citation unit),
        .cyclophane (.planeReference printed.system unit printed.reference),
        .cyclophane (.planeOrder printed.system unit printed.high printed.low),
        .cyclophane (.planeDescriptor printed.system unit printed.context printed.descriptor)]
  | .cyclophaneCenters s u c (.cip context kind d) =>
      [.cyclophane (.system s), .cyclophane (.unit s u), .cyclophane (.citation c u),
        match u with
        | .atomCenter center => .cyclophane (.center s center kind context d)
        | _ => .cyclophane (.unit s u)]
  | .cyclophaneCenters s u c (.relativeRCT candidates selected referenceSide assignments) =>
      [.cyclophane (.system s), .cyclophane (.unit s u), .cyclophane (.citation c u),
        .cyclophane (.rctSide s selected.center referenceSide)] ++
      (candidates.flatMap fun candidate =>
        [.cyclophane (.unit s (.atomCenter candidate.center)),
          .cyclophane (.citation candidate.citation (.atomCenter candidate.center)),
          .cyclophane (.rctEligible s candidate.center),
          .cyclophane (.rctCandidate s candidate.center candidate.citation
            candidate.namedAsSuffix candidate.sequencePriority)]) ++
      (assignments.map fun assignment =>
        .cyclophane (.rctSide s assignment.center assignment.side))
  | .cyclophaneDoubleBonds s u c ring phaneRing geometry carbonContext context d =>
      [.cyclophane (.system s), .cyclophane (.unit s u), .cyclophane (.citation c u),
        .cyclophane (.doubleBondRing s u ring phaneRing),
        .cyclophane (.doubleBondGeometry u geometry),
        .cyclophane (.carbonDoubleBondContext u carbonContext),
        .cyclophane (.doubleBondNaming s u context d)]

/-- Exact qualitative frames retained by this payload.  Unlike unit-only requirements, these
claims must be reproduced byte-for-byte by the audited physical-support entry. -/
def P93FusedCyclophaneClausePayload.exactQualitativePhysicalClaims
    {row : Remaining71P93FusedCyclophaneAuthorityRow} :
    P93FusedCyclophaneClausePayload row → List P93PhysicalClaim
  | .cyclophanePlanes printed executable => [.plane printed.members executable.frame]
  | _ => []

def P93FusedCyclophaneClausePayload.Intrinsic
    {row : Remaining71P93FusedCyclophaneAuthorityRow} (source : AuthoritativeChemicalInput) :
    P93FusedCyclophaneClausePayload row → Prop
  | .fusedCIP observation => observation.ValidFor source
  | .fusedRelation observation => observation.ValidFor source
  | .cyclophanePlanes printed executable =>
      printed.ValidFor source ∧ executable.ValidFor source printed
  | .cyclophaneCenters system unit citation (.cip context kind descriptor) =>
      system.MechanicallyValidFor source ∧ P93CyclophaneUnitSupported system unit ∧
        (∃ center, unit = .atomCenter center) ∧
        (kind = .chiralCenter ∨ kind = .pseudoasymmetricCenter) ∧
        DescriptorApplies kind descriptor ∧ DescriptorRecommended context kind descriptor ∧
        citation.Valid
  | .cyclophaneCenters system unit citation
      (.relativeRCT candidates selected referenceSide assignments) =>
      system.MechanicallyValidFor source ∧ P93CyclophaneUnitSupported system unit ∧
        unit = .atomCenter selected.center ∧ citation = selected.citation ∧
        candidates ≠ [] ∧ (candidates.map fun candidate => candidate.center).Nodup ∧
        (candidates.map fun candidate => candidate.citation).Nodup ∧
        (∀ candidate ∈ candidates,
          candidate.center ∈ system.atomCarrier ∧ candidate.citation.Valid) ∧
        P93CyclophaneIsUniqueRCTReference candidates selected ∧
        referenceSide ≠ .onMeanPlane ∧ assignments ≠ [] ∧
        (assignments.map fun assignment => assignment.center).Nodup ∧
        (assignments.map fun assignment => assignment.citation).Nodup ∧
        (∀ candidate ∈ candidates, ∃ assignment ∈ assignments,
          assignment.center = candidate.center ∧ assignment.citation = candidate.citation) ∧
        ∀ assignment ∈ assignments,
          (∃ candidate ∈ candidates,
            assignment.center = candidate.center ∧ assignment.citation = candidate.citation) ∧
          if assignment.center = selected.center then
            assignment.side = referenceSide ∧ assignment.descriptor = .reference
          else rctDescriptor referenceSide assignment.side = some assignment.descriptor
  | .cyclophaneDoubleBonds system unit citation ring phaneRing geometry carbonContext context
      descriptor? =>
      system.MechanicallyValidFor source ∧ P93CyclophaneUnitSupported system unit ∧
        (∃ first second, unit = .bond first second ∧ first ∈ ring ∧ second ∈ ring) ∧
        ring ∈ system.rings ∧ (ring, phaneRing) ∈ system.ringPhaneCycles ∧
        P93CyclophaneDoubleBondDescriptorAllowed context geometry descriptor? ∧
        ((descriptor? = some .cis ∨ descriptor? = some .trans) →
          CisTransGeneralApplicable carbonContext) ∧
        (CyclophaneDoubleBondDescriptorRequired system.phaneNodes.length phaneRing.length = true →
          ∃ descriptor, descriptor? = some descriptor) ∧
        (context = .preferredIUPACName → descriptor? =
          P93CyclophaneDoubleBondExpected system.phaneNodes.length phaneRing.length geometry) ∧
        citation.Valid

def P93CanonicalFullerenePrintedObservation.AgreesWith
    (printed : P93CanonicalFullerenePrintedObservation)
    (executable : P93CanonicalFullereneObservation) : Prop :=
  printed.molecule = executable.molecule ∧
    printed.cageCarrier = executable.selectedInput.symmetryInput.cage.carrier ∧
    printed.substitutionTest = executable.selectedInput.symmetryInput.cage.substitutionTest ∧
    printed.chiralSubstituentSites =
      executable.selectedInput.symmetryInput.substitutionEvidence.chiralSubstituentSites ∧
    printed.substituentAssignments = executable.substituentAssignments

def P93CanonicalFullerenePrintedObservation.AgreesWithType4
    (printed : P93CanonicalFullerenePrintedObservation)
    (executable : P93CanonicalFullereneType4Observation) : Prop :=
  printed.molecule = executable.molecule ∧
    printed.cageCarrier = executable.input.cage.carrier ∧
    printed.substitutionTest = executable.input.cage.substitutionTest ∧
    printed.chiralSubstituentSites = executable.input.substitutionEvidence.chiralSubstituentSites ∧
    printed.substituentAssignments = executable.substituentAssignments




inductive P93FullereneClausePayload : Remaining71P93FullereneAuthorityRow → Type where
  | methodology : P93FullereneClausePayload .generalMethodology
  | inherentParent
      (observation : P93RelationalFullereneHandedAuthorityObservation
        P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy) :
      P93FullereneClausePayload .inherentParentChirality
  | inherentSubstitution
      (observation : P93RelationalFullereneHandedAuthorityObservation
        P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy) :
      P93FullereneClausePayload .inherentSubstitutionChirality
  | noninherentSubstitution
      (observation : P93RelationalFullereneHandedAuthorityObservation
        P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy) :
      P93FullereneClausePayload .noninherentSubstitutionChirality
  | chiralSubstituents
      (observation : P93RelationalFullereneType4AuthorityObservation
        P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy) :
      P93FullereneClausePayload .chiralSubstituents
  | superimposed
      (observation : P93RelationalFullereneSuperimposedAuthorityObservation
        P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy) :
      P93FullereneClausePayload .superimposedStereogenicElements

def P93FullereneClausePayload.toClaims {row : Remaining71P93FullereneAuthorityRow} :
    P93FullereneClausePayload row → List P93SourceClaim
  | .methodology => [.fullerene .methodologyDecisionRule]
  | .inherentParent _
  | .inherentSubstitution _
  | .noninherentSubstitution _
  | .chiralSubstituents _
  | .superimposed _ => []

def P93FullereneClausePayload.Intrinsic
    {row : Remaining71P93FullereneAuthorityRow} (source : AuthoritativeChemicalInput) :
    P93FullereneClausePayload row → Prop
  | .methodology => True
  | .inherentParent observation =>
      observation.ValidFor
          P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy
          source ∧
        observation.base.assignment.chiralityType = .inherentlyChiralParent
  | .inherentSubstitution observation =>
      observation.ValidFor
          P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy
          source ∧
        observation.base.assignment.chiralityType = .inherentlyChiralSubstitutionPattern
  | .noninherentSubstitution observation =>
      observation.ValidFor
          P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy
          source ∧
        observation.base.assignment.chiralityType = .noninherentlyChiralSubstitutionPattern
  | .chiralSubstituents observation =>
      observation.ValidFor
        P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy source
  | .superimposed observation =>
      observation.ValidFor
        P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy source

/-- Coordinate-free transcription of one printed ring-assembly axial assignment.  The four
reference atoms are copied from the adjacent source diagram; no Cartesian realization or raw
orientation bit is stored here. -/
structure P93CanonicalRingAssemblyPrintedAxisAssignment where
  junction : P93RingAssemblyJunction
  startFirst : Nat
  startSecond : Nat
  endFirst : Nat
  endSecond : Nat
  citation : P93AuthorityCitationToken
  cipDescriptor : AxialDescriptor
  preferredDescriptor : RingAssemblyAxisDescriptor
  generalDescriptor : RingAssemblyAxisDescriptor
  deriving DecidableEq, Repr

def P93CanonicalRingAssemblyPrintedAxisAssignment.sense
    (assignment : P93CanonicalRingAssemblyPrintedAxisAssignment) : StereoSense :=
  match assignment.cipDescriptor with
  | .Ra => .positive
  | .Sa => .negative

def P93CanonicalRingAssemblyPrintedAxisAssignment.record
    (assignment : P93CanonicalRingAssemblyPrintedAxisAssignment) :
    IndexedAxialGeometryObservation where
  axisStart := assignment.junction.leftAtom
  axisEnd := assignment.junction.rightAtom
  startFirst := assignment.startFirst
  startSecond := assignment.startSecond
  endFirst := assignment.endFirst
  endSecond := assignment.endSecond
  sense := assignment.sense

structure P93CanonicalRingAssemblyPrintedAxesObservation where
  molecule : SemanticMolecule
  assembly : P93AuthorityRingAssembly
  assignments : List P93CanonicalRingAssemblyPrintedAxisAssignment

/-- Exact normalization and Cartesian reconstruction used only by the executable axial theorem.
The agreement equation below prevents these records from changing any printed locator or
descriptor. -/
structure P93CanonicalRingAssemblyAxesExecutableWitness where
  normalization : CertifiedChemistryNormalizationResult
  spatial : SpatialConfiguration
  assignments : List P93RingAssemblyAxisAssignment

def P93RingAssemblyAxisAssignment.toPrinted
    (assignment : P93RingAssemblyAxisAssignment) :
    P93CanonicalRingAssemblyPrintedAxisAssignment where
  junction := assignment.junction
  startFirst := assignment.record.startFirst
  startSecond := assignment.record.startSecond
  endFirst := assignment.record.endFirst
  endSecond := assignment.record.endSecond
  citation := assignment.citation
  cipDescriptor := assignment.cipDescriptor
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor := assignment.generalDescriptor

def P93CanonicalRingAssemblyPrintedAxesObservation.ValidFor
    (source : AuthoritativeChemicalInput)
    (printed : P93CanonicalRingAssemblyPrintedAxesObservation) : Prop :=
  source.molecule = printed.molecule ∧
    printed.assembly.MechanicallyValidFor source ∧
    printed.assignments ≠ [] ∧
    (printed.assignments.map fun assignment => assignment.junction).Nodup ∧
    (printed.assignments.map fun assignment => assignment.citation).Nodup ∧
    ∀ assignment ∈ printed.assignments,
      assignment.junction ∈ printed.assembly.junctions ∧
        P93RingAssemblyAxisFrameValid source printed.assembly assignment.junction
          assignment.record ∧
        assignment.cipDescriptor = AxialDescriptor.ofSense assignment.record.sense ∧
        assignment.preferredDescriptor =
          preferredRingAssemblyAxisDescriptor assignment.cipDescriptor ∧
        assignment.generalDescriptor =
          generalRingAssemblyAxisDescriptor assignment.cipDescriptor ∧
        PreferredRingAssemblyAxisDescriptor assignment.preferredDescriptor ∧
        assignment.citation.Valid

def P93CanonicalRingAssemblyAxesExecutableWitness.ValidFor
    (source : AuthoritativeChemicalInput)
    (printed : P93CanonicalRingAssemblyPrintedAxesObservation)
    (executable : P93CanonicalRingAssemblyAxesExecutableWitness) : Prop :=
  source.spatial? = some executable.spatial ∧
    executable.normalization.result.parsed.AuthoritativeStructureAgreement source ∧
    executable.normalization.result =
      normalizeRawMolecule executable.normalization.result.parsed ∧
    printed.assignments = executable.assignments.map P93RingAssemblyAxisAssignment.toPrinted ∧
    ∀ assignment ∈ executable.assignments,
      assignment.toPrinted.record = assignment.record ∧
        BlueBookP93.GeometryIngress.RationalAxialObservationJudgment
          executable.normalization.result executable.spatial assignment.record
            assignment.cipDescriptor

inductive P93RingAssemblyClausePayload : Remaining71P93RingAssemblyAuthorityRow → Type where
  | axes (printed : P93CanonicalRingAssemblyPrintedAxesObservation)
      (executable : P93CanonicalRingAssemblyAxesExecutableWitness) :
      P93RingAssemblyClausePayload .axes
  | centers (assembly : P93AuthorityRingAssembly)
      (assignments : List P93RingAssemblyCenterAssignment) : P93RingAssemblyClausePayload .centers
  | doubleBonds (assembly : P93AuthorityRingAssembly)
      (assignments : List P93RingAssemblyDoubleBondAssignment) :
      P93RingAssemblyClausePayload .doubleBonds

def P93RingAssemblyClausePayload.toClaims {row : Remaining71P93RingAssemblyAuthorityRow} :
    P93RingAssemblyClausePayload row → List P93SourceClaim
  | .axes printed _executable =>
      [.ringAssembly (.assembly printed.assembly)] ++
        printed.assignments.flatMap fun a =>
          [.ringAssembly (.axisEligible printed.assembly a.junction),
            .ringAssembly (.axisCitation printed.assembly a.junction a.citation),
            .ringAssembly (.axisDescriptors printed.assembly a.junction
              a.preferredDescriptor a.generalDescriptor)]
  | .centers assembly assignments => [.ringAssembly (.assembly assembly)] ++
      assignments.flatMap fun a =>
        [.ringAssembly (.centerEligible assembly a.center),
          .ringAssembly (.centerCitation assembly a.center a.citation),
          .ringAssembly (.centerDescriptor assembly a.center a.preferredDescriptor)] ++
        match a.generalDescriptor? with
        | none => []
        | some general =>
            [.ringAssembly (.centerGeneralEquivalent assembly a.center
              a.preferredDescriptor general)]
  | .doubleBonds assembly assignments => [.ringAssembly (.assembly assembly)] ++
      assignments.flatMap fun a =>
          [.ringAssembly (.doubleBondStereogenic assembly a.ringIndex a.first a.second),
          .ringAssembly (.doubleBondNeedsSpecification assembly a.ringIndex a.first a.second),
          .ringAssembly (.doubleBondCitation assembly a.ringIndex a.first a.second a.citation),
          .ringAssembly (.doubleBondDescriptor assembly a.ringIndex a.first a.second a.descriptor)]

def P93RingAssemblyClausePayload.Intrinsic
    {row : Remaining71P93RingAssemblyAuthorityRow} (source : AuthoritativeChemicalInput) :
    P93RingAssemblyClausePayload row → Prop
  | .axes printed executable =>
      printed.ValidFor source ∧ executable.ValidFor source printed
  | .centers assembly assignments =>
      assembly.MechanicallyValidFor source ∧ assignments ≠ [] ∧
        (assignments.map fun assignment => assignment.center).Nodup ∧
        (assignments.map fun assignment => assignment.citation).Nodup ∧
        ∀ assignment ∈ assignments,
          P93RingAssemblyCenterInExactlyOneRing assembly assignment.center ∧
            P93CanonicalPhysicalUnitEnvelope source (.atomCenter assignment.center) ∧
            PreferredRingAssemblyCenterDescriptor assignment.preferredDescriptor ∧
            assignment.citation.Valid ∧
            match assignment.generalDescriptor? with
            | none => True
            | some generalDescriptor => P93RingAssemblyGeneralCenterDescriptor generalDescriptor
  | .doubleBonds assembly assignments =>
      assembly.MechanicallyValidFor source ∧ assignments ≠ [] ∧
        (assignments.map fun assignment =>
          (assignment.ringIndex, assignment.first, assignment.second)).Nodup ∧
        (assignments.map fun assignment => assignment.citation).Nodup ∧
        ∀ assignment ∈ assignments,
          P93RingAssemblyBondInRing source assembly assignment.ringIndex
              assignment.first assignment.second ∧
            P93RingAssemblyEZDescriptor assignment.descriptor ∧ assignment.citation.Valid

/-- Closed counterpart of the fifteen legacy reviewed-evidence constructors.  Each constructor
retains the complete upstream clause payload; the coupled unit, citation, and descriptor are
computed projections rather than three caller-maintained parallel lists. -/
inductive P93CanonicalReviewedDescriptorEvidence where
  | acyclicCenter (payload : P93AcyclicClausePayload .singleAcyclicCenter)
  | acyclicDoubleBond (payload : P93AcyclicClausePayload .doubleBondEZCisTrans)
  | acyclicEvenCumulene (payload : P93AcyclicClausePayload .evenCumulenes)
  | acyclicOddCumulene (payload : P93AcyclicClausePayload .oddCumulenes)
  | monocyclicAbsoluteCenter
      (payload : P93MonocyclicClausePayload .monocyclicAbsoluteCenters)
  | monocyclicAchiralCenter
      (payload : P93MonocyclicClausePayload .monocyclicAchiralCenters)
  | monocyclicDoubleBond
      (payload : P93MonocyclicClausePayload .cyclicDoubleBonds)
      (citation : P93AuthorityCitationToken) (descriptor : BlueBookP93.Acyclic.Descriptor)
  | fusedCIP (observation : P93CanonicalFusedCIPObservation)
  | cyclophanePlane
      (payload : P93FusedCyclophaneClausePayload .cyclophanePlanes)
  | cyclophaneCenterCIP
      (payload : P93FusedCyclophaneClausePayload .cyclophaneCenters)
  | cyclophaneCenterRelative
      (payload : P93FusedCyclophaneClausePayload .cyclophaneCenters)
      (assignment : P93CyclophaneRCTLocatedAssignment)
  | cyclophaneDoubleBond
      (payload : P93FusedCyclophaneClausePayload .cyclophaneDoubleBonds)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | spiroPolyhedral (payload : P93SpiroNontetrahedralPayload)
  | ringAssemblyAxis (payload : P93RingAssemblyClausePayload .axes)
      (assignment : P93RingAssemblyAxisAssignment)
  | ringAssemblyCenter (payload : P93RingAssemblyClausePayload .centers)
      (assignment : P93RingAssemblyCenterAssignment)
  | ringAssemblyDoubleBond (payload : P93RingAssemblyClausePayload .doubleBonds)
      (assignment : P93RingAssemblyDoubleBondAssignment)

def P93CanonicalReviewedDescriptorEvidence.unit :
    P93CanonicalReviewedDescriptorEvidence → P93RingChainStereogenicUnit
  | .acyclicCenter (.single base ..)
  | .acyclicDoubleBond (.ezCisTrans base ..)
  | .acyclicEvenCumulene (.evenCumulene base ..)
  | .acyclicOddCumulene (.oddCumulene base ..) =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical base.unit
  | .monocyclicAbsoluteCenter (.absoluteCenter base ..)
  | .monocyclicAchiralCenter (.achiralCenter base ..) =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical base.unit
  | .monocyclicDoubleBond (.cyclicDouble base ..) _ _ =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical base.unit
  | .fusedCIP observation =>
      match observation.unit with
      | .physical unit => P93RingChainStereogenicUnit.ofAuthorityPhysical unit
      | .fusedAxis path => .fusedAxis path
  | .cyclophanePlane (.cyclophanePlanes printed _) =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical (.plane printed.members)
  | .cyclophaneCenterCIP (.cyclophaneCenters _ unit ..)
  | .cyclophaneDoubleBond (.cyclophaneDoubleBonds _ unit ..) _ =>
      P93RingChainStereogenicUnit.ofAuthorityPhysical unit
  | .cyclophaneCenterRelative _ assignment => .center assignment.center
  | .spiroPolyhedral payload =>
      .polyhedron payload.system.center payload.positions
  | .ringAssemblyAxis _ assignment =>
      .bondAxis assignment.junction.leftAtom assignment.junction.rightAtom
  | .ringAssemblyCenter _ assignment => .center assignment.center
  | .ringAssemblyDoubleBond _ assignment => .doubleBond assignment.first assignment.second

def P93CanonicalReviewedDescriptorEvidence.citation? :
    P93CanonicalReviewedDescriptorEvidence → Option P93AuthorityCitationToken
  | .acyclicCenter (.single base ..)
  | .acyclicDoubleBond (.ezCisTrans base ..)
  | .acyclicEvenCumulene (.evenCumulene base ..)
  | .acyclicOddCumulene (.oddCumulene base ..) => base.citation?
  | .monocyclicAbsoluteCenter (.absoluteCenter base ..)
  | .monocyclicAchiralCenter (.achiralCenter base ..) => some base.citation
  | .monocyclicDoubleBond _ citation _ => some citation
  /- The coupled legacy locator channel carries only unsigned numeric tokens.  A suffixed fused
  locant such as `3a` is retained in the upstream fused observation and is not lossy-coerced. -/
  | .fusedCIP _ => none
  | .cyclophanePlane (.cyclophanePlanes printed _) => some printed.citation
  | .cyclophaneCenterCIP (.cyclophaneCenters _ _ citation ..)
  | .cyclophaneDoubleBond (.cyclophaneDoubleBonds _ _ citation ..) _ => some citation
  | .cyclophaneCenterRelative _ assignment => some assignment.citation
  | .spiroPolyhedral payload => some payload.citation
  | .ringAssemblyAxis _ assignment => some assignment.citation
  | .ringAssemblyCenter _ assignment => some assignment.citation
  | .ringAssemblyDoubleBond _ assignment => some assignment.citation

def P93CanonicalReviewedDescriptorEvidence.descriptor :
    P93CanonicalReviewedDescriptorEvidence → P93CanonicalDescriptor
  | .acyclicCenter (.single base ..)
  | .acyclicDoubleBond (.ezCisTrans base ..)
  | .acyclicEvenCumulene (.evenCumulene base ..)
  | .acyclicOddCumulene (.oddCumulene base ..) => .acyclic base.descriptor
  | .monocyclicAbsoluteCenter (.absoluteCenter _ _ _ descriptor ..)
  | .monocyclicAchiralCenter (.achiralCenter _ _ _ descriptor ..) => .acyclic descriptor
  | .monocyclicDoubleBond _ _ descriptor => .acyclic descriptor
  | .fusedCIP observation => .fused observation.descriptor
  | .cyclophanePlane (.cyclophanePlanes printed _) =>
      .cyclophanePlane printed.descriptor
  | .cyclophaneCenterCIP (.cyclophaneCenters _ _ _ (.cip _ _ descriptor)) =>
      .acyclic descriptor
  | .cyclophaneCenterCIP (.cyclophaneCenters _ _ _ (.relativeRCT ..)) =>
      .cyclophaneRelativeCenter .reference
  | .cyclophaneCenterRelative _ assignment => .cyclophaneRelativeCenter assignment.descriptor
  | .cyclophaneDoubleBond _ descriptor => .acyclic descriptor
  | .spiroPolyhedral payload => .polyhedral payload.descriptor
  | .ringAssemblyAxis _ assignment => .ringAssemblyAxis assignment.preferredDescriptor
  | .ringAssemblyCenter _ assignment => .ringAssemblyCenter assignment.preferredDescriptor
  | .ringAssemblyDoubleBond _ assignment => .acyclic assignment.descriptor

/-- Exact descriptor projection used by the coupled authority carrier.  The reviewed coupled
evidence type has no fullerene constructor, so the fallback branch is unreachable for values
produced by `descriptor` but keeps the closed canonical descriptor map total. -/
def P93CanonicalReviewedDescriptorEvidence.ringDescriptor
    (evidence : P93CanonicalReviewedDescriptorEvidence) : P93RingChainDescriptor :=
  match evidence.descriptor with
  | .acyclic descriptor => .acyclic descriptor
  | .fused descriptor => .fused descriptor
  | .cyclophanePlane descriptor => .cyclophanePlane descriptor
  | .cyclophaneRelativeCenter descriptor => .cyclophaneRelativeCenter descriptor
  | .polyhedral descriptor => .polyhedral descriptor
  | .fullerene _ => .acyclic .R
  | .ringAssemblyAxis descriptor => .ringAssemblyAxis descriptor
  | .ringAssemblyCenter descriptor => .ringAssemblyCenter descriptor

def P93CanonicalReviewedDescriptorEvidence.located
    (evidence : P93CanonicalReviewedDescriptorEvidence) : P93CanonicalLocatedDescriptor where
  unit := evidence.unit
  citation? := evidence.citation?
  descriptor := evidence.descriptor

def P93CanonicalReviewedDescriptorEvidence.upstreamClaims :
    P93CanonicalReviewedDescriptorEvidence → List P93SourceClaim
  | .acyclicCenter payload | .acyclicDoubleBond payload
  | .acyclicEvenCumulene payload | .acyclicOddCumulene payload => payload.toClaims
  | .monocyclicAbsoluteCenter payload | .monocyclicAchiralCenter payload => payload.toClaims
  | .monocyclicDoubleBond payload _ _ => payload.toClaims
  | .fusedCIP observation => [.fused (.cipObservation observation)]
  | .cyclophanePlane payload | .cyclophaneCenterCIP payload
  | .cyclophaneCenterRelative payload _ | .cyclophaneDoubleBond payload _ => payload.toClaims
  | .spiroPolyhedral payload => payload.toClaims
  | .ringAssemblyAxis payload _ | .ringAssemblyCenter payload _
  | .ringAssemblyDoubleBond payload _ => payload.toClaims

/-- Exact retained qualitative frames contributed by nested reviewed evidence. -/
def P93CanonicalReviewedDescriptorEvidence.exactQualitativePhysicalClaims :
    P93CanonicalReviewedDescriptorEvidence → List P93PhysicalClaim
  | .cyclophanePlane payload => payload.exactQualitativePhysicalClaims
  | .spiroPolyhedral payload => payload.exactQualitativePhysicalClaims
  | _ => []

def P93CanonicalReviewedDescriptorEvidence.ValidFor
    (source : AuthoritativeChemicalInput) (evidence : P93CanonicalReviewedDescriptorEvidence) : Prop :=
  (∀ claim ∈ evidence.upstreamClaims, claim.SourceEnvelope source) ∧
  match evidence with
  | .acyclicCenter payload | .acyclicDoubleBond payload
  | .acyclicEvenCumulene payload | .acyclicOddCumulene payload => payload.Intrinsic
  | .monocyclicAbsoluteCenter payload | .monocyclicAchiralCenter payload =>
      payload.Intrinsic source
  | .monocyclicDoubleBond payload citation descriptor =>
      payload.Intrinsic source ∧ citation.Valid ∧
        (match payload with
        | .cyclicDouble _ _ _ descriptor? => descriptor? = some descriptor)
  | .fusedCIP observation => observation.ValidFor source
  | .cyclophanePlane payload => payload.Intrinsic source
  | .cyclophaneCenterCIP payload =>
      payload.Intrinsic source ∧
        (match payload with
        | .cyclophaneCenters _ _ _ specification =>
            ∃ context kind descriptor, specification = .cip context kind descriptor)
  | .cyclophaneCenterRelative payload assignment =>
      payload.Intrinsic source ∧
        (match payload with
        | .cyclophaneCenters _ _ _ specification =>
            ∃ candidates selected referenceSide assignments,
              specification = .relativeRCT candidates selected referenceSide assignments ∧
                assignment ∈ assignments)
  | .cyclophaneDoubleBond payload descriptor =>
      payload.Intrinsic source ∧
        (match payload with
        | .cyclophaneDoubleBonds _ _ _ _ _ _ _ _ descriptor? =>
            descriptor? = some descriptor)
  | .spiroPolyhedral payload => payload.Intrinsic source
  | .ringAssemblyAxis payload assignment =>
      payload.Intrinsic source ∧
        (match payload with | .axes _ executable => assignment ∈ executable.assignments)
  | .ringAssemblyCenter payload assignment =>
      payload.Intrinsic source ∧
        (match payload with | .centers _ assignments => assignment ∈ assignments)
  | .ringAssemblyDoubleBond payload assignment =>
      payload.Intrinsic source ∧
        (match payload with | .doubleBonds _ assignments => assignment ∈ assignments)

/-- A fact whose compiled relation has a closed-world (all eligible facts are present) consumer
inside one coupled P-93.6 observation.  Only the four non-monotone upstream families occur here;
all other reviewed-evidence constructors remain monotone under claim union. -/
inductive P93CoupledClosedWorldFact where
  | cyclophaneRelativeCenter (system : P93AuthorityCyclophaneSystem) (center : Nat)
  | ringAssemblyAxis (assembly : P93AuthorityRingAssembly)
      (junction : P93RingAssemblyJunction)
  | ringAssemblyCenter (assembly : P93AuthorityRingAssembly) (center : Nat)
  | ringAssemblyDoubleBond (assembly : P93AuthorityRingAssembly)
      (ringIndex first second : Nat)
  deriving DecidableEq

/-- Exact eligibility facts emitted by the non-monotone nested payloads. -/
def P93CanonicalReviewedDescriptorEvidence.closedWorldFacts :
    P93CanonicalReviewedDescriptorEvidence → List P93CoupledClosedWorldFact
  | .cyclophaneCenterRelative
      (.cyclophaneCenters system _ _ (.relativeRCT candidates _ _ _)) _ =>
      candidates.map fun candidate => .cyclophaneRelativeCenter system candidate.center
  | .ringAssemblyAxis (.axes printed _) _ =>
      printed.assignments.map fun assignment =>
        .ringAssemblyAxis printed.assembly assignment.junction
  | .ringAssemblyCenter (.centers assembly assignments) _ =>
      assignments.map fun assignment => .ringAssemblyCenter assembly assignment.center
  | .ringAssemblyDoubleBond (.doubleBonds assembly assignments) _ =>
      assignments.map fun assignment =>
        .ringAssemblyDoubleBond assembly assignment.ringIndex assignment.first assignment.second
  | _ => []

/-- A nested observation covers a producer fact exactly when, for the same family discriminator,
its own exhaustive corpus contains that fact.  Different systems/assemblies and monotone evidence
are intentionally irrelevant. -/
def P93CanonicalReviewedDescriptorEvidence.Covers
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (fact : P93CoupledClosedWorldFact) : Prop :=
  match evidence, fact with
  | .cyclophaneCenterRelative
        (.cyclophaneCenters system _ _ (.relativeRCT candidates _ _ _)) _,
      .cyclophaneRelativeCenter producerSystem center =>
      system = producerSystem → ∃ candidate ∈ candidates, candidate.center = center
  | .ringAssemblyAxis (.axes printed _) _,
      .ringAssemblyAxis producerAssembly junction =>
      printed.assembly = producerAssembly →
        ∃ assignment ∈ printed.assignments, assignment.junction = junction
  | .ringAssemblyCenter (.centers assembly assignments) _,
      .ringAssemblyCenter producerAssembly center =>
      assembly = producerAssembly →
        ∃ assignment ∈ assignments, assignment.center = center
  | .ringAssemblyDoubleBond (.doubleBonds assembly assignments) _,
      .ringAssemblyDoubleBond producerAssembly ringIndex first second =>
      assembly = producerAssembly →
        ∃ assignment ∈ assignments,
          assignment.ringIndex = ringIndex ∧ assignment.first = first ∧ assignment.second = second
  | _, _ => True

/-- Pairwise union closure for the coupled claim scope.  Any closed-world consumer covers every
fact emitted by another nested payload sharing its exact system/assembly discriminator. -/
def P93CoupledAssignmentsUnionClosed
    (assignments : List P93CanonicalReviewedDescriptorEvidence) : Prop :=
  ∀ consumer ∈ assignments, ∀ producer ∈ assignments,
    ∀ fact ∈ producer.closedWorldFacts, consumer.Covers fact

structure P93CoupledClausePayload where
  reviewedBaseName : P93RingChainBaseName
  baseNameCertificate : P93RingChainReviewedBaseNameCertificate
  assignments : List P93CanonicalReviewedDescriptorEvidence
  multiplicativeSelected : Bool
  repeatedComponents : List P93RingChainRepeatedComponent
  componentCorrespondences : List P93RingChainComponentCorrespondence
  assignmentOwnerships : List P93RingChainAssignmentOwnership

def P93CoupledClausePayload.toClaims (p : P93CoupledClausePayload) : List P93SourceClaim :=
  [P93SourceClaim.coupled (.baseName p.reviewedBaseName p.baseNameCertificate)] ++
    p.assignments.flatMap (fun evidence => evidence.upstreamClaims ++
      [P93SourceClaim.coupled (.eligibleUnit p.reviewedBaseName evidence.unit),
        P93SourceClaim.coupled (.evidenceBelongs p.reviewedBaseName evidence.located)] ++
      evidence.citation?.toList.map fun citation =>
        P93SourceClaim.coupled (.citation p.reviewedBaseName citation evidence.unit)) ++
    [P93SourceClaim.coupled
      (.repeatedComponents p.reviewedBaseName p.repeatedComponents),
      P93SourceClaim.coupled
        (.multiplicativeDecision p.reviewedBaseName p.multiplicativeSelected)]

def P93CoupledClausePayload.exactQualitativePhysicalClaims
    (payload : P93CoupledClausePayload) : List P93PhysicalClaim :=
  payload.assignments.flatMap
    P93CanonicalReviewedDescriptorEvidence.exactQualitativePhysicalClaims

def P93CanonicalAssignmentTouchesComponent
    (assignment : P93CanonicalReviewedDescriptorEvidence)
    (component : P93RingChainRepeatedComponent) : Prop :=
  ¬Disjoint assignment.unit.atoms component.atoms

def P93CanonicalAssignmentOwnershipsComplete
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership) : Prop :=
  (ownerships.map fun ownership =>
      (ownership.assignmentIndex, ownership.componentIndex)).Nodup ∧
    (∀ ownership ∈ ownerships,
      ∃ assignment component,
        assignments[ownership.assignmentIndex]? = some assignment ∧
          components[ownership.componentIndex]? = some component ∧
          P93CanonicalAssignmentTouchesComponent assignment component) ∧
    ∀ assignmentIndex assignment,
      assignments[assignmentIndex]? = some assignment →
        ∀ componentIndex component,
          components[componentIndex]? = some component →
            P93CanonicalAssignmentTouchesComponent assignment component →
              ∃ ownership ∈ ownerships,
                ownership.assignmentIndex = assignmentIndex ∧
                  ownership.componentIndex = componentIndex

def P93CanonicalAtomInOwnedBoundaryUnit
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex atom : Nat) : Prop :=
  ∃ ownership ∈ ownerships, ∃ assignment,
    ownership.componentIndex = componentIndex ∧
      assignments[ownership.assignmentIndex]? = some assignment ∧
      atom ∈ assignment.unit.atoms

def P93CanonicalRingChainInterfaceAtom
    (source : AuthoritativeChemicalInput)
    (_components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex : Nat) (component : P93RingChainRepeatedComponent)
    (atom : Nat) : Prop :=
  atom ∉ component.atoms ∧
    ((∃ interaction ∈ source.molecule.interactions,
      P93RingChainInteractionTouches component.atoms interaction ∧
        atom ∈ interaction.participants) ∨
      P93CanonicalAtomInOwnedBoundaryUnit assignments ownerships componentIndex atom)

def P93CanonicalInteractionTouchesOwnedInterface
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex : Nat) (component : P93RingChainRepeatedComponent)
    (interaction : SemanticInteraction) : Prop :=
  (∀ atom ∈ interaction.participants,
    atom ∈ component.atoms ∨
      P93CanonicalRingChainInterfaceAtom source components assignments ownerships
        componentIndex component atom) ∧
    ∃ atom ∈ interaction.participants,
      atom ∈ component.atoms ∨
        P93CanonicalAtomInOwnedBoundaryUnit assignments ownerships componentIndex atom

def P93CanonicalComponentCorrespondenceValidFor
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership)
    (correspondence : P93RingChainComponentCorrespondence) : Prop :=
  correspondence.leftIndex = 0 ∧ 0 < correspondence.rightIndex ∧
    ∃ left right,
      components[correspondence.leftIndex]? = some left ∧
        components[correspondence.rightIndex]? = some right ∧
        (correspondence.atomPairs.map Prod.fst).Nodup ∧
        (correspondence.atomPairs.map Prod.snd).Nodup ∧
        (correspondence.attachmentPairs.map Prod.fst).Nodup ∧
        (correspondence.attachmentPairs.map Prod.snd).Nodup ∧
        (correspondence.atomPairs.map Prod.fst).toFinset = left.atoms ∧
        (correspondence.atomPairs.map Prod.snd).toFinset = right.atoms ∧
        (∀ atom,
          atom ∈ (correspondence.attachmentPairs.map Prod.fst).toFinset ↔
            P93CanonicalRingChainInterfaceAtom source components assignments ownerships
              correspondence.leftIndex left atom) ∧
        (∀ atom,
          atom ∈ (correspondence.attachmentPairs.map Prod.snd).toFinset ↔
            P93CanonicalRingChainInterfaceAtom source components assignments ownerships
              correspondence.rightIndex right atom) ∧
        (∀ leftAtom rightAtom,
          P93RingChainAtomsCorrespond correspondence leftAtom rightAtom →
            source.molecule.atoms[leftAtom]? = source.molecule.atoms[rightAtom]?) ∧
        (∀ leftInteraction ∈ source.molecule.interactions,
          P93CanonicalInteractionTouchesOwnedInterface source components assignments
              ownerships correspondence.leftIndex left leftInteraction →
            ∃ rightInteraction ∈ source.molecule.interactions,
              P93CanonicalInteractionTouchesOwnedInterface source components assignments
                  ownerships correspondence.rightIndex right rightInteraction ∧
                P93RingChainInteractionCorresponds correspondence
                  leftInteraction rightInteraction) ∧
        ∀ rightInteraction ∈ source.molecule.interactions,
          P93CanonicalInteractionTouchesOwnedInterface source components assignments
              ownerships correspondence.rightIndex right rightInteraction →
            ∃ leftInteraction ∈ source.molecule.interactions,
              P93CanonicalInteractionTouchesOwnedInterface source components assignments
                  ownerships correspondence.leftIndex left leftInteraction ∧
                P93RingChainInteractionCorresponds correspondence leftInteraction rightInteraction

def P93CanonicalAssignmentsStereoCorrespond
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership)
    (leftIndex rightIndex : Nat)
    (correspondence : P93RingChainComponentCorrespondence) : Prop :=
  (∀ ownership ∈ ownerships,
    ownership.componentIndex = leftIndex →
      ∀ assignment,
        assignments[ownership.assignmentIndex]? = some assignment →
          ∃ mappedOwnership ∈ ownerships, ∃ mapped,
            mappedOwnership.componentIndex = rightIndex ∧
              assignments[mappedOwnership.assignmentIndex]? = some mapped ∧
              P93RingChainUnitsCorrespond correspondence assignment.unit mapped.unit ∧
              assignment.descriptor = mapped.descriptor) ∧
    ∀ mappedOwnership ∈ ownerships,
      mappedOwnership.componentIndex = rightIndex →
        ∀ mapped,
          assignments[mappedOwnership.assignmentIndex]? = some mapped →
            ∃ ownership ∈ ownerships, ∃ assignment,
              ownership.componentIndex = leftIndex ∧
                assignments[ownership.assignmentIndex]? = some assignment ∧
                P93RingChainUnitsCorrespond correspondence assignment.unit mapped.unit ∧
                assignment.descriptor = mapped.descriptor

def P93CanonicalMultiplicativeSymmetryComplete
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (correspondences : List P93RingChainComponentCorrespondence)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership) : Prop :=
  P93RingChainRepeatedComponentsValid source components ∧
    P93CanonicalAssignmentOwnershipsComplete components assignments ownerships ∧
    (correspondences.map fun correspondence => correspondence.rightIndex).Nodup ∧
    (∀ correspondence ∈ correspondences,
      P93CanonicalComponentCorrespondenceValidFor source components assignments ownerships
          correspondence ∧
        P93CanonicalAssignmentsStereoCorrespond assignments ownerships
          correspondence.leftIndex correspondence.rightIndex correspondence) ∧
    ∀ index, 0 < index → index < components.length →
      ∃ correspondence ∈ correspondences, correspondence.rightIndex = index

def P93CanonicalOwnedDescriptorMismatch
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership) : Prop :=
  ∃ leftOwnership ∈ ownerships, ∃ rightOwnership ∈ ownerships,
    leftOwnership.componentIndex ≠ rightOwnership.componentIndex ∧
      ∃ leftAssignment rightAssignment,
        assignments[leftOwnership.assignmentIndex]? = some leftAssignment ∧
          assignments[rightOwnership.assignmentIndex]? = some rightAssignment ∧
          leftAssignment.ringDescriptor ≠ rightAssignment.ringDescriptor

/-- Canonical source evidence for the printed rejection of a multiplicative name.  Empty
correspondence and ownership lists cannot satisfy this branch. -/
structure P93CanonicalMultiplicativeRejectionEvidence
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership) : Prop where
  componentsValid : P93RingChainRepeatedComponentsValid source components
  ownershipsComplete :
    P93CanonicalAssignmentOwnershipsComplete components assignments ownerships
  descriptorMismatch : P93CanonicalOwnedDescriptorMismatch assignments ownerships
  componentNonisomorphism :
    ∃ leftOwnership ∈ ownerships, ∃ rightOwnership ∈ ownerships,
      leftOwnership.componentIndex ≠ rightOwnership.componentIndex ∧
        ∃ leftComponent rightComponent,
          components[leftOwnership.componentIndex]? = some leftComponent ∧
            components[rightOwnership.componentIndex]? = some rightComponent ∧
            P93RingChainComponentsConstitutionallyNonisomorphic
              source leftComponent rightComponent

inductive P93CanonicalMultiplicativeDecisionValid
    (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (correspondences : List P93RingChainComponentCorrespondence)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership) : Bool → Prop where
  | selected
      (symmetryComplete : P93CanonicalMultiplicativeSymmetryComplete source components
        correspondences assignments ownerships) :
      P93CanonicalMultiplicativeDecisionValid source components correspondences
        assignments ownerships true
  | rejected
      (evidence : P93CanonicalMultiplicativeRejectionEvidence source components
        assignments ownerships) :
      P93CanonicalMultiplicativeDecisionValid source components correspondences
        assignments ownerships false

def P93CoupledClausePayload.Intrinsic
    (source : AuthoritativeChemicalInput) (payload : P93CoupledClausePayload) : Prop :=
  payload.baseNameCertificate.ValidFor source payload.reviewedBaseName ∧
    payload.assignments ≠ [] ∧
    (payload.assignments.map fun assignment => assignment.unit.physicalIdentity).Nodup ∧
    (payload.assignments.filterMap fun assignment => assignment.citation?).Nodup ∧
    (∀ assignment ∈ payload.assignments, assignment.ValidFor source) ∧
    P93CoupledAssignmentsUnionClosed payload.assignments ∧
    P93CanonicalMultiplicativeDecisionValid source payload.repeatedComponents
      payload.componentCorrespondences payload.assignments payload.assignmentOwnerships
      payload.multiplicativeSelected

/-- The semantic package is indexed by the exact manifest row.  Every constructor stores one
coherent payload capable of producing all repeated source-relation applications for that row. -/
inductive P93ClausePayloadData : P93Clause → Type where
  | fullerene {row : Remaining71P93FullereneAuthorityRow}
      (payload : P93FullereneClausePayload row) :
      P93ClausePayloadData (.fullerene row)
  | noncarbon {row : Remaining71P93NoncarbonAuthorityRow}
      (payload : P93NoncarbonClausePayload row) :
      P93ClausePayloadData (.noncarbon row)
  | general {row : Remaining71P93GeneralAuthorityRow}
      (payload : P93GeneralClausePayload row) : P93ClausePayloadData (.general row)
  | monocyclic {row : Remaining71P93MonocyclicAuthorityRow}
      (payload : P93MonocyclicClausePayload row) :
      P93ClausePayloadData (.monocyclic row)
  | vonBaeyer {row : Remaining71P93VonBaeyerAuthorityRow}
      (payload : P93VonBaeyerClausePayload row) :
      P93ClausePayloadData (.vonBaeyer row)
  | ringAssembly {row : Remaining71P93RingAssemblyAuthorityRow}
      (payload : P93RingAssemblyClausePayload row) :
      P93ClausePayloadData (.ringAssembly row)
  | acyclic {row : Remaining71P93AcyclicAuthorityRow}
      (payload : P93AcyclicClausePayload row) : P93ClausePayloadData (.acyclic row)
  | spiro {row : Remaining71P93SpiroReadyAuthorityRow}
      (payload : P93SpiroClausePayload row) : P93ClausePayloadData (.spiro row)
  | spiroNontetrahedral (payload : P93SpiroNontetrahedralPayload) :
      P93ClausePayloadData .spiroNontetrahedral
  | fusedCyclophane {row : Remaining71P93FusedCyclophaneAuthorityRow}
      (payload : P93FusedCyclophaneClausePayload row) :
      P93ClausePayloadData (.fusedCyclophane row)
  | coupled (payload : P93CoupledClausePayload) :
      P93ClausePayloadData (.coupledRingChain .configurations)

def P93ClausePayloadData.toClaims {clause : P93Clause} :
    P93ClausePayloadData clause → List P93SourceClaim
  | .fullerene payload => payload.toClaims
  | .noncarbon payload => payload.toClaims
  | .general payload => payload.toClaims
  | .monocyclic payload => payload.toClaims
  | .vonBaeyer payload => payload.toClaims
  | .ringAssembly payload => payload.toClaims
  | .acyclic payload => payload.toClaims
  | .spiro payload => payload.toClaims
  | .spiroNontetrahedral payload => payload.toClaims
  | .fusedCyclophane payload => payload.toClaims
  | .coupled payload => payload.toClaims

/-- Payload-level projection of qualitative evidence whose exact frame is semantically retained.
All other qualitative uses remain existential unit requirements and are handled separately. -/
def P93ClausePayloadData.exactQualitativePhysicalClaims {clause : P93Clause} :
    P93ClausePayloadData clause → List P93PhysicalClaim
  | .fusedCyclophane payload => payload.exactQualitativePhysicalClaims
  | .spiroNontetrahedral payload => payload.exactQualitativePhysicalClaims
  | .coupled payload => payload.exactQualitativePhysicalClaims
  | _ => []

def P93ClausePayloadData.ValidFor
    {clause : P93Clause} (source : AuthoritativeChemicalInput)
    (payload : P93ClausePayloadData clause) : Prop :=
  (∀ claim ∈ payload.toClaims, claim.SourceEnvelope source) ∧
    match payload with
    | .general generalPayload => generalPayload.Intrinsic
    | .fullerene fullerenePayload => fullerenePayload.Intrinsic source
    | .fusedCyclophane familyPayload => familyPayload.Intrinsic source
    | .noncarbon familyPayload => familyPayload.Intrinsic source
    | .monocyclic familyPayload => familyPayload.Intrinsic source
    | .vonBaeyer familyPayload => familyPayload.Intrinsic source
    | .ringAssembly familyPayload => familyPayload.Intrinsic source
    | .acyclic familyPayload => familyPayload.Intrinsic
    | .spiro familyPayload => familyPayload.Intrinsic source
    | .spiroNontetrahedral familyPayload => familyPayload.Intrinsic source
    | .coupled familyPayload => familyPayload.Intrinsic source

/-! ## Finite proof-carrying source packages -/



structure P93ClauseObservation
    (source : AuthoritativeChemicalInput) (clause : P93Clause) where
  payload : P93ClausePayloadData clause
  validFor : payload.ValidFor source

def P93ClauseObservation.auditClaims
    {source : AuthoritativeChemicalInput} {clause : P93Clause}
    (observation : P93ClauseObservation source clause) : List P93SourceClaim :=
  observation.payload.toClaims




theorem P93ClauseObservation.generatedClaims_valid
    {source : AuthoritativeChemicalInput} {clause : P93Clause}
    (observation : P93ClauseObservation source clause) :
    observation.payload.ValidFor source := observation.validFor

/-- Whether an audited source datum is carried completely by printed text or also requires a
reviewed interpretation of the adjacent source figure.  The distinction is frozen in each entry;
figure-derived geometry cannot silently masquerade as a textual statement. -/
inductive P93SourceObservationMode where
  | verbatimText
  | textAndFigure
  deriving DecidableEq, Repr




structure P93CanonicalClaimTranscription (claim : P93SourceClaim) where
  supportingLocator : String
  supportingLocatorNonempty : supportingLocator ≠ ""
  supportingObservation : String
  supportingObservationNonempty : supportingObservation ≠ ""
  mode : P93SourceObservationMode










structure P93CanonicalSourceTranscription
    (source : AuthoritativeChemicalInput) (clause : P93Clause)
    (observation : P93ClauseObservation source clause) where
  normativeSource : IUPACNormativeSource
  sourceIsBlueBookP9 : normativeSource = .blueBook2013P9
  artifactSha256 : String
  artifactSha256Exact : normativeSource.sha256? = some artifactSha256
  pdfPage : Nat
  pdfPagePositive : 0 < pdfPage
  pdfPageWithinFrozenArtifact : pdfPage ≤ 91
  clauseSection : String
  clauseSectionExact : clauseSection = clause.provision.sourceSection
  observationSubsection : String
  observationSubsectionNonempty : observationSubsection ≠ ""
  printedObservation : String
  printedObservationNonempty : printedObservation ≠ ""
  claimTranscriptions : ∀ claim, claim ∈ observation.auditClaims →
    P93CanonicalClaimTranscription claim

structure P93CanonicalClauseObservationEntry where
  source : AuthoritativeChemicalInput
  sourceAdmitted : source.StructurallyWellFormed
  clause : P93Clause
  clauseListed : clause ∈ P93Clause.all
  observation : P93ClauseObservation source clause
  transcription : P93CanonicalSourceTranscription source clause observation

def P93CanonicalClauseObservationEntry.qualitativePhysicalUnits
    (entry : P93CanonicalClauseObservationEntry) : List P93AuthorityPhysicalUnit :=
  entry.observation.auditClaims.flatMap P93SourceClaim.qualitativePhysicalUnits

def P93CanonicalClauseObservationEntry.exactQualitativePhysicalClaims
    (entry : P93CanonicalClauseObservationEntry) : List P93PhysicalClaim :=
  entry.observation.payload.exactQualitativePhysicalClaims

/-- Shared physical evidence can support the family-level mechanics used by a clause, but it is
deliberately stored outside semantic coverage: no physical support entry can witness that the
textual requirement of a P-93 provision has been represented. -/
structure P93CanonicalPhysicalSupportEntry where
  source : AuthoritativeChemicalInput
  sourceAdmitted : source.StructurallyWellFormed
  clause : P93Clause
  claim : P93PhysicalClaim
  clauseListed : clause ∈ P93Clause.all
  supports : P93SourceClaim.PhysicalSupports clause.family
  sourceEnvelope : claim.SourceEnvelope source

/-- The canonical source artifact is a finite *program*, not fifty-six observations forced onto
one chemical input.  Each clause entry owns an admitted source and a payload valid for that exact
source.  The `observationSourceUnique` invariant makes the `(family, source)` key invert to the
entire entry, so no duplicate payload can enlarge a family-scoped closed-world relation.  The
same printed molecule may legitimately illustrate clauses in different families. -/
structure P93CanonicalSourceProgram where
  observations : List P93CanonicalClauseObservationEntry
  physicalSupports : List P93CanonicalPhysicalSupportEntry
  clausesCovered : ∀ clause ∈ P93Clause.all,
    ∃ entry ∈ observations, entry.clause = clause
  observationSourceUnique :
    ∀ first ∈ observations, ∀ second ∈ observations,
      first.source = second.source → first.clause.family = second.clause.family →
        first = second
  supportSourceSeparated :
    ∀ first ∈ physicalSupports, ∀ second ∈ physicalSupports,
      first.source = second.source → first.clause = second.clause
  observationSupportSeparated :
    ∀ observation ∈ observations, ∀ support ∈ physicalSupports,
      observation.source = support.source → observation.clause = support.clause
  qualitativePhysicalCovered :
    ∀ observation ∈ observations, ∀ unit ∈ observation.qualitativePhysicalUnits,
      ∃ support ∈ physicalSupports,
        support.source = observation.source ∧ support.clause = observation.clause ∧
          support.claim.unit = unit
  exactQualitativePhysicalCovered :
    ∀ observation ∈ observations,
      ∀ claim ∈ observation.exactQualitativePhysicalClaims,
        ∃ support ∈ physicalSupports,
          support.source = observation.source ∧ support.clause = observation.clause ∧
            support.claim = claim

def P93CanonicalSourceProgram.Observed
    (program : P93CanonicalSourceProgram)
    (clause : P93Clause) : Prop :=
  ∃ entry ∈ program.observations, entry.clause = clause

theorem P93CanonicalSourceProgram.all_clauses_observed
    (program : P93CanonicalSourceProgram) (clause : P93Clause)
    (listed : clause ∈ P93Clause.all) : program.Observed clause :=
  program.clausesCovered clause listed

/-- A family/source key identifies its entire observation entry, including the dependent payload. -/
theorem P93CanonicalSourceProgram.entry_eq_of_source_eq
    (program : P93CanonicalSourceProgram)
    {first second : P93CanonicalClauseObservationEntry}
    (firstMem : first ∈ program.observations)
    (secondMem : second ∈ program.observations)
    (sourceEq : first.source = second.source)
    (familyEq : first.clause.family = second.clause.family) : first = second :=
  program.observationSourceUnique first firstMem second secondMem sourceEq familyEq

/-- Within one family, entries for distinct clauses necessarily have distinct source keys. -/
theorem P93CanonicalSourceProgram.source_ne_of_clause_ne
    (program : P93CanonicalSourceProgram)
    {first second : P93CanonicalClauseObservationEntry}
    (firstMem : first ∈ program.observations)
    (secondMem : second ∈ program.observations)
    (familyEq : first.clause.family = second.clause.family)
    (clauseNe : first.clause ≠ second.clause) :
    first.source ≠ second.source := by
  intro sourceEq
  exact clauseNe (congrArg P93CanonicalClauseObservationEntry.clause
    (program.entry_eq_of_source_eq firstMem secondMem sourceEq familyEq))

/-- Exact audited qualitative support is available at the same source and clause as every
observation that uses a plane, helix, or polyhedron. -/
theorem P93CanonicalSourceProgram.qualitative_support_for
    (program : P93CanonicalSourceProgram)
    {observation : P93CanonicalClauseObservationEntry}
    (observationMem : observation ∈ program.observations)
    {unit : P93AuthorityPhysicalUnit}
    (unitMem : unit ∈ observation.qualitativePhysicalUnits) :
    ∃ support ∈ program.physicalSupports,
      support.source = observation.source ∧ support.clause = observation.clause ∧
        support.claim.unit = unit :=
  program.qualitativePhysicalCovered observation observationMem unit unitMem

/-- An explicitly retained qualitative frame is reproduced exactly—not merely by another frame
for the same unit—at the observation's source and clause. -/
theorem P93CanonicalSourceProgram.exact_qualitative_support_for
    (program : P93CanonicalSourceProgram)
    {observation : P93CanonicalClauseObservationEntry}
    (observationMem : observation ∈ program.observations)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ observation.exactQualitativePhysicalClaims) :
    ∃ support ∈ program.physicalSupports,
      support.source = observation.source ∧ support.clause = observation.clause ∧
        support.claim = claim :=
  program.exactQualitativePhysicalCovered observation observationMem claim claimMem

/-- Exact manifest projection carried by every clause observation. -/
def P93CanonicalClauseObservationEntry.provision
    (entry : P93CanonicalClauseObservationEntry) : IUPACNormativeProvision :=
  entry.clause.provision

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93CanonicalDescriptor.mirror_mirror
assert_kernel_only TetraStereo.OneCenter.P93CanonicalDescriptor.localInvert_involutive
assert_kernel_only TetraStereo.OneCenter.P93CanonicalDescriptor.localInvert_generalRepresentativeEligible_iff
assert_kernel_only TetraStereo.OneCenter.P93CanonicalDescriptor.representativeEligible_mirror_iff
assert_kernel_only TetraStereo.OneCenter.P93CanonicalDescriptor.mirrorPreferredAtLowest
assert_kernel_only TetraStereo.OneCenter.P93FullereneClausePayload.Intrinsic
assert_kernel_only TetraStereo.OneCenter.P93CanonicalMultiplicativeRejectionEvidence
assert_kernel_only TetraStereo.OneCenter.P93CanonicalMultiplicativeDecisionValid
assert_kernel_only TetraStereo.OneCenter.P93CoupledClausePayload.Intrinsic
assert_kernel_only TetraStereo.OneCenter.P93CanonicalSourceProgram
