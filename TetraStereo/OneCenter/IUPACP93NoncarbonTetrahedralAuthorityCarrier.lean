import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93NoncarbonTetrahedra

set_option autoImplicit false

/-!
# Authority carrier for the seven P-93.2 provisions

The independent P-93.2 vocabulary describes element families and representation quotients.  This
module binds those rules to one exact four-ligand unit in `AuthoritativeChemicalInput`.  It keeps
source indices, printed citations, and audited descriptor judgments separate, and it makes every
oxo spelling variant name the same center/oxygen pair before a family rule can compare them.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.NoncarbonTetrahedra

def P93NoncarbonElementAt
    (source : AuthoritativeChemicalInput) (atomIndex atomicNumber : Nat) : Prop :=
  ∃ atom, source.molecule.atoms[atomIndex]? = some atom ∧
    atom.element.atomicNumber = atomicNumber

def P93NoncarbonCentralElementFamilyMatches
    (family : CentralElementFamily) (atomicNumber : Nat) : Prop :=
  match family with
  | .boron => atomicNumber = 5
  | .sulfur => atomicNumber = 16
  | .selenium => atomicNumber = 34
  | .tellurium => atomicNumber = 52
  | .nitrogen => atomicNumber = 7
  | .phosphorus => atomicNumber = 15
  | .arsenic => atomicNumber = 33
  | .antimony => atomicNumber = 51
  | .bismuth => atomicNumber = 83
  | .other => atomicNumber ∉ [5, 7, 15, 16, 33, 34, 51, 52, 83]

def P93NoncarbonOnicAtomicNumber : OnicCenter → Nat
  | .azanium => 7
  | .phosphanium => 15
  | .arsanium => 33
  | .stibanium => 51
  | .bismuthanium => 83

def P93NoncarbonOxideAtomicNumber : OxideCenter → Nat
  | .amineOxide => 7
  | .phosphaneOxide => 15

def P93NoncarbonChalcogenOxoFamilyMatches
    (family : ChalcogenOxoFamily) (atomicNumber : Nat) : Prop :=
  match family with
  | .sulfate | .sulfonate => atomicNumber = 16
  | .selenate | .selenonate => atomicNumber = 34
  | .tellurate | .telluronate => atomicNumber = 52
  | .related => atomicNumber ∈ [16, 34, 52]

def P93NoncarbonGroup14AtomicNumber : NoncarbonGroup14Center → Nat
  | .silicon => 14
  | .germanium => 32
  | .tin => 50
  | .lead => 82

/-- Decoration-free four-ligand unit.  The ligand list is the complete constitutional incidence
frame, not merely four selected neighbors. -/
structure P93NoncarbonTetrahedralFrame where
  center : Nat
  ligands : List Nat
  deriving DecidableEq, Repr

def P93NoncarbonTetrahedralFrame.StructurallyValidFor
    (source : AuthoritativeChemicalInput)
    (frame : P93NoncarbonTetrahedralFrame) : Prop :=
  P93AuthorityAtomsBounded source (frame.center :: frame.ligands) ∧
    frame.ligands.length = 4 ∧ frame.ligands.Nodup ∧
    (∀ ligand,
      (P93AuthorityBinaryBond source frame.center ligand ∨
        P93AuthorityMulticenterIncidence source frame.center ligand) ↔
          ligand ∈ frame.ligands) ∧
    ∃ atom, source.molecule.atoms[frame.center]? = some atom ∧
      atom.element.atomicNumber ≠ 6

/-- Audited facts not derivable from constitution alone.  Descriptor and citation relations are
source-indexed and can therefore be supplied by the frozen authority corpus without reading a
production result.  Representation-variant relations certify hypothetical alternative source
spellings of one already fixed oxo unit. -/
structure P93NoncarbonTetrahedralAuthorityPolicy where
  Descriptor : Type
  TetrahedralArrangementObserved :
    AuthoritativeChemicalInput → Nat → List Nat → Prop
  CitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCitationToken →
      P93AuthorityPhysicalUnit → Prop
  DescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit → Descriptor → Prop
  OxideBondingVariantAuthorized :
    AuthoritativeChemicalInput → Nat → Nat → OxideCenter →
      WrittenBondingToOxygen → Prop
  PhosphorusOxoVariantAuthorized :
    AuthoritativeChemicalInput → Nat → Nat → PhosphorusOxoFamily → Bool →
      FormalChargeArrangement → Prop
  ChalcogenOxoVariantAuthorized :
    AuthoritativeChemicalInput → Nat → Nat → ChalcogenOxoFamily → Bool →
      FormalChargeArrangement → Prop

def P93NoncarbonTetrahedralFrame.ValidFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (frame : P93NoncarbonTetrahedralFrame) : Prop :=
  frame.StructurallyValidFor source ∧
    policy.TetrahedralArrangementObserved source frame.center frame.ligands

structure P93NoncarbonTetrahedralAssignment
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  frame : P93NoncarbonTetrahedralFrame
  descriptor : policy.Descriptor

def P93NoncarbonTetrahedralAssignment.ValidFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93NoncarbonTetrahedralAssignment policy) : Prop :=
  assignment.frame.ValidFor policy source ∧
    policy.DescriptorAuthorized source (.atomCenter assignment.frame.center)
      assignment.descriptor

structure P93NoncarbonCitationAuthorityObservation
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  assignment : P93NoncarbonTetrahedralAssignment policy
  citation? : Option P93AuthorityCitationToken
  citationRule : DescriptorCitationObservation

def P93NoncarbonCitationBindingValid
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonCitationAuthorityObservation policy) : Prop :=
  match observation.citationRule.locant with
  | .none => observation.citation? = none
  | .numerical =>
      ∃ citation, observation.citation? = some citation ∧ citation.Valid ∧
        policy.CitationAuthorized source citation
          (.atomCenter observation.assignment.frame.center)
  | .letter => False

def P93NoncarbonCitationAuthorityObservation.ValidFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonCitationAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    (∃ atom, source.molecule.atoms[observation.assignment.frame.center]? = some atom ∧
      P93NoncarbonCentralElementFamilyMatches
        observation.citationRule.centralElement atom.element.atomicNumber) ∧
    P93NoncarbonCitationBindingValid policy source observation ∧
    CitationConforms observation.citationRule

structure P93NoncarbonOnicAuthorityObservation
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  assignment : P93NoncarbonTetrahedralAssignment policy
  family : OnicCenter

def P93NoncarbonOnicAuthorityObservation.ValidFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonOnicAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    P93NoncarbonElementAt source observation.assignment.frame.center
      (P93NoncarbonOnicAtomicNumber observation.family)

structure P93NoncarbonOxideAuthorityObservation
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  assignment : P93NoncarbonTetrahedralAssignment policy
  family : OxideCenter
  oxygen : Nat
  firstBonding : WrittenBondingToOxygen
  secondBonding : WrittenBondingToOxygen

def P93NoncarbonOxideAuthorityObservation.ValidFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonOxideAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    P93NoncarbonElementAt source observation.assignment.frame.center
      (P93NoncarbonOxideAtomicNumber observation.family) ∧
    observation.oxygen ∈ observation.assignment.frame.ligands ∧
    P93NoncarbonElementAt source observation.oxygen 8 ∧
    P93AuthorityBinaryBond source observation.assignment.frame.center
      observation.oxygen ∧
    policy.OxideBondingVariantAuthorized source
      observation.assignment.frame.center observation.oxygen observation.family
      observation.firstBonding ∧
    policy.OxideBondingVariantAuthorized source
      observation.assignment.frame.center observation.oxygen observation.family
      observation.secondBonding
    ∧ observation.firstBonding ≠ observation.secondBonding

structure P93NoncarbonPhosphorusOxoAuthorityObservation
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  assignment : P93NoncarbonTetrahedralAssignment policy
  family : PhosphorusOxoFamily
  oxygen : Nat
  firstWrittenAsDouble : Bool
  secondWrittenAsDouble : Bool
  firstCharges : FormalChargeArrangement
  secondCharges : FormalChargeArrangement

def P93NoncarbonPhosphorusOxoAuthorityObservation.ValidFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonPhosphorusOxoAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    P93NoncarbonElementAt source observation.assignment.frame.center 15 ∧
    observation.oxygen ∈ observation.assignment.frame.ligands ∧
    P93NoncarbonElementAt source observation.oxygen 8 ∧
    P93AuthorityBinaryBond source observation.assignment.frame.center
      observation.oxygen ∧
    policy.PhosphorusOxoVariantAuthorized source
      observation.assignment.frame.center observation.oxygen observation.family
      observation.firstWrittenAsDouble observation.firstCharges ∧
    policy.PhosphorusOxoVariantAuthorized source
      observation.assignment.frame.center observation.oxygen observation.family
      observation.secondWrittenAsDouble observation.secondCharges
    ∧ (observation.firstWrittenAsDouble, observation.firstCharges) ≠
      (observation.secondWrittenAsDouble, observation.secondCharges)

structure P93NoncarbonChalcogenOxoAuthorityObservation
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  assignment : P93NoncarbonTetrahedralAssignment policy
  family : ChalcogenOxoFamily
  oxygen : Nat
  firstWrittenAsDouble : Bool
  secondWrittenAsDouble : Bool
  firstCharges : FormalChargeArrangement
  secondCharges : FormalChargeArrangement

def P93NoncarbonChalcogenOxoAuthorityObservation.ValidFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonChalcogenOxoAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    (∃ atom : SemanticAtom,
      source.molecule.atoms[observation.assignment.frame.center]? = some atom ∧
      P93NoncarbonChalcogenOxoFamilyMatches observation.family
        atom.element.atomicNumber) ∧
    observation.oxygen ∈ observation.assignment.frame.ligands ∧
    P93NoncarbonElementAt source observation.oxygen 8 ∧
    P93AuthorityBinaryBond source observation.assignment.frame.center
      observation.oxygen ∧
    policy.ChalcogenOxoVariantAuthorized source
      observation.assignment.frame.center observation.oxygen observation.family
      observation.firstWrittenAsDouble observation.firstCharges ∧
    policy.ChalcogenOxoVariantAuthorized source
      observation.assignment.frame.center observation.oxygen observation.family
      observation.secondWrittenAsDouble observation.secondCharges
    ∧ (observation.firstWrittenAsDouble, observation.firstCharges) ≠
      (observation.secondWrittenAsDouble, observation.secondCharges)

structure P93NoncarbonGroup14AuthorityObservation
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) where
  assignment : P93NoncarbonTetrahedralAssignment policy
  family : NoncarbonGroup14Center

def P93NoncarbonGroup14AuthorityObservation.ValidFor
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonGroup14AuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    P93NoncarbonElementAt source observation.assignment.frame.center
      (P93NoncarbonGroup14AtomicNumber observation.family)

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93NoncarbonTetrahedralFrame.StructurallyValidFor
assert_kernel_only TetraStereo.OneCenter.P93NoncarbonCitationAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93NoncarbonChalcogenOxoAuthorityObservation.ValidFor
