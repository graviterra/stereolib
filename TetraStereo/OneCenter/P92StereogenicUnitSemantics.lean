import TetraStereo.OneCenter.CIPBlueBookConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent P-92.1 stereogenic-unit and assignment semantics

`CIPBlueBookConformance` independently transcribes the primitive ranking decisions.  This module
transcribes the surrounding P-92.1 domain: what the named stereogenic-unit kinds mean, the
bonding-number scope, chirality/helicity conversion, mirror behaviour, denticity, and hierarchical
rule application.  It does not call molecular perception or the production descriptor pipeline.
-/

namespace BlueBookP92

/-! ## P-92.1.1: chirality and stereogenic units -/

/-- Chirality is nonsuperposability with the mirror image.  `superposable` is supplied by the exact
geometric/group-action model used at the authority boundary. -/
def IsChiral {Entity : Type*} (mirror : Entity → Entity)
    (superposable : Entity → Entity → Prop) (entity : Entity) : Prop :=
  ¬superposable entity (mirror entity)

def IsAchiral {Entity : Type*} (mirror : Entity → Entity)
    (superposable : Entity → Entity → Prop) (entity : Entity) : Prop :=
  superposable entity (mirror entity)

theorem chiral_not_achiral {Entity : Type*} (mirror : Entity → Entity)
    (superposable : Entity → Entity → Prop) (entity : Entity)
    (chiral : IsChiral mirror superposable entity) :
    ¬IsAchiral mirror superposable entity :=
  chiral

/-- A local unit is stereogenic when at least one allowed local change generates a stereoisomer. -/
def IsStereogenicUnit {Configuration : Type*}
    (localChange : Configuration → Configuration → Prop)
    (stereoisomers : Configuration → Configuration → Prop)
    (configuration : Configuration) : Prop :=
  ∃ changed, localChange configuration changed ∧ stereoisomers configuration changed

/-- The source asserts only the forward implication: a chiral entity has a stereogenic unit. -/
def ChiralEntityHasStereogenicUnit {Entity Unit : Type*}
    (isChiral : Entity → Prop) (belongsTo : Unit → Entity → Prop)
    (isStereogenic : Unit → Prop) : Prop :=
  ∀ entity, isChiral entity → ∃ unit, belongsTo unit entity ∧ isStereogenic unit

/-- A four-ligand center is stereogenic in the P-92.1.1(a) sense only when its ligands are
distinguishable and every interchange of two ligand positions produces a stereoisomer. -/
structure FourLigandCenterObservation (Ligand Configuration : Type*) where
  ligand : Fin 4 → Ligand
  configuration : Configuration
  afterSwap : Fin 4 → Fin 4 → Configuration

def IsChiralityCenter {Ligand Configuration : Type*}
    (distinguishable : Ligand → Ligand → Prop)
    (stereoisomers : Configuration → Configuration → Prop)
    (observation : FourLigandCenterObservation Ligand Configuration) : Prop :=
  (∀ first second, first ≠ second →
      distinguishable (observation.ligand first) (observation.ligand second)) ∧
  (∀ first second, first ≠ second →
      stereoisomers observation.configuration (observation.afterSwap first second))

structure ChiralityAxisObservation where
  nearPairDistinguishable : Prop
  farPairDistinguishable : Prop
  arrangementNotSuperposableOnMirror : Prop

/-- Reduced axial symmetry requires the two ligands within each end pair to differ; the two pairs
need not contain four mutually different ligands. -/
def IsChiralityAxis (observation : ChiralityAxisObservation) : Prop :=
  observation.nearPairDistinguishable ∧
  observation.farPairDistinguishable ∧
  observation.arrangementNotSuperposableOnMirror

structure ChiralityPlaneObservation where
  hasPlanarUnit : Prop
  hasAdjacentOutOfPlaneBond : Prop
  torsionRestricted : Prop
  planeCannotBeSymmetryPlane : Prop

def IsChiralityPlane (observation : ChiralityPlaneObservation) : Prop :=
  observation.hasPlanarUnit ∧ observation.hasAdjacentOutOfPlaneBond ∧
  observation.torsionRestricted ∧ observation.planeCannotBeSymmetryPlane

/-- Exactly one unordered pair among four ligands is enantiomorphic. -/
def ExactlyOneEnantiomorphicPair {Ligand : Type*}
    (ligand : Fin 4 → Ligand) (enantiomorphic : Ligand → Ligand → Prop) : Prop :=
  ∃ first second, first ≠ second ∧
    enantiomorphic (ligand first) (ligand second) ∧
    ∀ otherFirst otherSecond, otherFirst ≠ otherSecond →
      enantiomorphic (ligand otherFirst) (ligand otherSecond) →
      ((otherFirst = first ∧ otherSecond = second) ∨
       (otherFirst = second ∧ otherSecond = first))

def IsPseudoasymmetricUnit {Ligand : Type*}
    (ligand : Fin 4 → Ligand)
    (distinguishable enantiomorphic : Ligand → Ligand → Prop) : Prop :=
  (∀ first second, first ≠ second →
      distinguishable (ligand first) (ligand second)) ∧
  ExactlyOneEnantiomorphicPair ligand enantiomorphic

structure DoubleBondUnitObservation where
  firstEndLigandsDifferent : Prop
  secondEndLigandsDifferent : Prop
  interchangeGeneratesCisTransIsomer : Prop

def IsCisTransDoubleBondUnit (observation : DoubleBondUnitObservation) : Prop :=
  observation.firstEndLigandsDifferent ∧ observation.secondEndLigandsDifferent ∧
  observation.interchangeGeneratesCisTransIsomer

structure EnantiomorphicDoubleBondObservation where
  firstEndLigandsDifferent : Prop
  secondEndLigandsEnantiomorphic : Prop
  bondArrangementStereogenic : Prop

def IsEnantiomorphicDoubleBond
    (observation : EnantiomorphicDoubleBondObservation) : Prop :=
  observation.firstEndLigandsDifferent ∧
  observation.secondEndLigandsEnantiomorphic ∧
  observation.bondArrangementStereogenic

/-! ## P-92.1.1(f), P-92.4.1, and P-92.6: enantiomorphic double-bond descriptors -/

/-- Relative placement of the two sequence-senior terminal ligands after one end has been ordered
as an enantiomorphic pair.  This geometry domain is independent of production marker types. -/
inductive EnantiomorphicDoubleBondTerminalGeometry where
  | together
  | opposite
  deriving DecidableEq, Repr

/-- The reflection-variant descriptor pair prescribed for geometrically enantiomorphic double
bonds.  These are not lowercase `e/z` variants. -/
inductive EnantiomorphicDoubleBondDescriptor where
  | seqCis
  | seqTrans
  deriving DecidableEq, Repr

/-- Independent P-92 assignment relation: together senior ligands give `seqCis`; opposite senior
ligands give `seqTrans`. -/
def EnantiomorphicDoubleBondDescriptorAssignment :
    EnantiomorphicDoubleBondTerminalGeometry → EnantiomorphicDoubleBondDescriptor → Prop
  | .together, .seqCis
  | .opposite, .seqTrans => True
  | _, _ => False

/-- Executable transcription of the independent assignment relation. -/
def enantiomorphicDoubleBondDescriptor :
    EnantiomorphicDoubleBondTerminalGeometry → EnantiomorphicDoubleBondDescriptor
  | .together => .seqCis
  | .opposite => .seqTrans

theorem enantiomorphicDoubleBondDescriptor_eq_iff_assignment
    (geometry : EnantiomorphicDoubleBondTerminalGeometry)
    (descriptor : EnantiomorphicDoubleBondDescriptor) :
    enantiomorphicDoubleBondDescriptor geometry = descriptor ↔
      EnantiomorphicDoubleBondDescriptorAssignment geometry descriptor := by
  cases geometry <;> cases descriptor <;>
    simp [enantiomorphicDoubleBondDescriptor,
      EnantiomorphicDoubleBondDescriptorAssignment]

/-- Reflection exchanges the two descriptors, as required by their reflection-variant status. -/
def EnantiomorphicDoubleBondDescriptor.reflected :
    EnantiomorphicDoubleBondDescriptor → EnantiomorphicDoubleBondDescriptor
  | .seqCis => .seqTrans
  | .seqTrans => .seqCis

@[simp] theorem enantiomorphicDoubleBondDescriptor_reflection_involutive
    (descriptor : EnantiomorphicDoubleBondDescriptor) :
    descriptor.reflected.reflected = descriptor := by
  cases descriptor <;> rfl

@[simp] theorem enantiomorphicDoubleBondDescriptor_reflection_changes
    (descriptor : EnantiomorphicDoubleBondDescriptor) :
    descriptor.reflected ≠ descriptor := by
  cases descriptor <;> decide

theorem existsUnique_enantiomorphicDoubleBondDescriptor
    (geometry : EnantiomorphicDoubleBondTerminalGeometry) :
    ∃! descriptor, EnantiomorphicDoubleBondDescriptorAssignment geometry descriptor := by
  cases geometry
  · refine ⟨.seqCis, trivial, ?_⟩
    intro descriptor assigned
    cases descriptor <;>
      simp_all [EnantiomorphicDoubleBondDescriptorAssignment]
  · refine ⟨.seqTrans, trivial, ?_⟩
    intro descriptor assigned
    cases descriptor <;>
      simp_all [EnantiomorphicDoubleBondDescriptorAssignment]

/-! ## P-92.1.2: scope and configuration rules -/

/-- The stated organic-compound scope of this CIP treatment. -/
def WithinBondingNumberScope (bondingNumber : ℕ) : Prop :=
  bondingNumber ≤ 6

@[simp] theorem bonding_number_six_is_in_scope : WithinBondingNumberScope 6 := by
  norm_num [WithinBondingNumberScope]

theorem bonding_number_above_six_is_not_in_scope (bondingNumber : ℕ)
    (above : 6 < bondingNumber) :
    ¬WithinBondingNumberScope bondingNumber := by
  simp only [WithinBondingNumberScope]
  omega

inductive TurnSense where
  | clockwise
  | anticlockwise
  deriving DecidableEq, Repr

inductive CenterDescriptor where
  | R | S | r | s
  deriving DecidableEq, Repr

/-- Viewed from the side remote from the lowest-precedence ligand. -/
def centerDescriptor (pseudoasymmetric : Bool) : TurnSense → CenterDescriptor
  | .clockwise => if pseudoasymmetric then .r else .R
  | .anticlockwise => if pseudoasymmetric then .s else .S

inductive AxialDescriptor where
  | Ra | Sa
  deriving DecidableEq, Repr

/-- Elongated-tetrahedron chirality after the senior ligand at each end has been selected. -/
def axialDescriptor : TurnSense → AxialDescriptor
  | .clockwise => .Ra
  | .anticlockwise => .Sa

inductive PlanarDescriptor where
  | Rp | Sp
  deriving DecidableEq, Repr

/-- P-92.1.2.1.3 uses the ordinary tetrahedral chirality rule on its derived tetrahedron. -/
def planarDescriptor : TurnSense → PlanarDescriptor
  | .clockwise => .Rp
  | .anticlockwise => .Sp

inductive Helicity where
  | M | P
  deriving DecidableEq, Repr

inductive HelixHandedness where
  | leftHanded
  | rightHanded
  deriving DecidableEq, Repr

def helicityDescriptor : HelixHandedness → Helicity
  | .leftHanded => .M
  | .rightHanded => .P

/-- Looking along an axis, turn from the nearer senior ligand to the farther senior ligand. -/
def axialHelicityDescriptor : TurnSense → Helicity
  | .anticlockwise => .M
  | .clockwise => .P

inductive SignedTorsion where
  | negative
  | zero
  | positive
  deriving DecidableEq, Repr

/-- P-92 assigns `M` to the stated negative planar torsion and `P` to its mirror-positive case.
Zero torsion is planar/achiral and therefore has no helicity descriptor. -/
def planarHelicityDescriptor? : SignedTorsion → Option Helicity
  | .negative => some .M
  | .positive => some .P
  | .zero => none

inductive RSDescriptor where
  | R | S
  deriving DecidableEq, Repr

inductive HelicityApplication where
  | axis
  | plane
  deriving DecidableEq, Repr

/-- P-92.1.2.2.3: the `R/S` correspondence reverses between axes and planes. -/
def correspondingRS : HelicityApplication → Helicity → RSDescriptor
  | .axis, .M => .R
  | .axis, .P => .S
  | .plane, .M => .S
  | .plane, .P => .R

theorem no_general_M_to_RS_correspondence :
    correspondingRS .axis .M ≠ correspondingRS .plane .M := by
  decide

theorem no_general_P_to_RS_correspondence :
    correspondingRS .axis .P ≠ correspondingRS .plane .P := by
  decide

/-! ## Pseudoasymmetric mirror and exchange behaviour -/

inductive PseudoDescriptor where
  | r | s | m | p
  deriving DecidableEq, Repr

namespace PseudoDescriptor

/-- Lowercase descriptors are invariant on whole-object mirror reflection. -/
def reflected (descriptor : PseudoDescriptor) : PseudoDescriptor := descriptor

/-- Exchanging any two ligands reverses the descriptor within its family. -/
def afterLigandExchange : PseudoDescriptor → PseudoDescriptor
  | .r => .s | .s => .r | .m => .p | .p => .m

@[simp] theorem reflected_invariant (descriptor : PseudoDescriptor) :
    descriptor.reflected = descriptor :=
  rfl

@[simp] theorem ligand_exchange_involutive (descriptor : PseudoDescriptor) :
    descriptor.afterLigandExchange.afterLigandExchange = descriptor := by
  cases descriptor <;> rfl

@[simp] theorem ligand_exchange_changes (descriptor : PseudoDescriptor) :
    descriptor.afterLigandExchange ≠ descriptor := by
  cases descriptor <;> decide

end PseudoDescriptor

/-! ## P-92.1.3: hierarchy, property classes, and denticity -/

inductive RulePropertyClass where
  | materialOrTopological
  | geometrical
  | topographical
  deriving DecidableEq, Repr

def propertyClass : SequenceRule → RulePropertyClass
  | .rule1a | .rule1b | .rule2 => .materialOrTopological
  | .rule3 | .rule4a | .rule4b | .rule4c => .geometrical
  | .rule5 => .topographical

inductive ReflectionBehaviour where
  | invariant
  | variant
  deriving DecidableEq, Repr

def reflectionBehaviour : SequenceRule → ReflectionBehaviour
  | .rule5 => .variant
  | _ => .invariant

theorem only_rule5_is_reflection_variant (rule : SequenceRule) :
    reflectionBehaviour rule = .variant ↔ rule = .rule5 := by
  cases rule <;> decide

inductive Denticity where
  | monodentate
  | nDentate (n : ℕ) (atLeastTwo : 2 ≤ n)
  deriving Repr

/-- Apply one rule at one hierarchy position; equality continues and a strict result stops. -/
def firstStrictDecision :
    List SequenceRule → (SequenceRule → Ordering) → Option (SequenceRule × Ordering)
  | [], _ => none
  | rule :: remaining, outcome =>
      match outcome rule with
      | .eq => firstStrictDecision remaining outcome
      | strict => some (rule, strict)

@[simp] theorem first_rule_decides_when_strict
    (outcome : SequenceRule → Ordering) (strict : outcome .rule1a ≠ .eq) :
    firstStrictDecision ruleOrder outcome = some (.rule1a, outcome .rule1a) := by
  cases result : outcome .rule1a with
  | lt => simp [ruleOrder, firstStrictDecision, result]
  | eq => exact (strict result).elim
  | gt => simp [ruleOrder, firstStrictDecision, result]

theorem later_rules_do_not_affect_first_strict
    (first second : SequenceRule → Ordering)
    (sameRule1a : first .rule1a = second .rule1a)
    (strict : first .rule1a ≠ .eq) :
    firstStrictDecision ruleOrder first = firstStrictDecision ruleOrder second := by
  cases firstResult : first .rule1a with
  | lt =>
      have secondResult : second .rule1a = .lt := by
        rw [← sameRule1a]
        exact firstResult
      simp [ruleOrder, firstStrictDecision, firstResult, secondResult]
  | eq => exact (strict firstResult).elim
  | gt =>
      have secondResult : second .rule1a = .gt := by
        rw [← sameRule1a]
        exact firstResult
      simp [ruleOrder, firstStrictDecision, firstResult, secondResult]

namespace Perception

/-- Element scope independently enumerated for the legacy connectivity-only ordinary
tetrahedral detector.  This is intentionally a proposition rather than an alias for production's
Boolean whitelist. -/
def ConnectivityOnlyTetrahedralElement : Element → Prop
  | .B | .C | .N | .O | .P | .S | .Si | .Ge
  | .As | .Se | .Sn | .Sb | .Te | .Pb | .Bi => True
  | _ => False

instance (element : Element) : Decidable (ConnectivityOnlyTetrahedralElement element) := by
  cases element <;> simp only [ConnectivityOnlyTetrahedralElement]
  all_goals first | exact isTrue trivial | exact isFalse id

/-- Independent applicability boundary for descriptor-free graph perception.

The four positions must be four materialized atom neighbours.  A lone pair may be used as a
phantom fourth position only after a trigonal-pyramidal configuration or geometry observation has
been supplied; graph connectivity by itself does not establish that observation. -/
def ConnectivityOnlyTetrahedralFrame
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (center : Nat) : Prop :=
  ∃ spec,
    result.parsed.atomAt? center = some spec ∧
      ConnectivityOnlyTetrahedralElement spec.element ∧
      mol.isExtendedTetrahedralParityCarrier center = false ∧
      (mol.writtenNeighbors center).length = 4

instance (result : ChemistryNormalizationResult) (mol : RawMolecule) (center : Nat) :
    Decidable (ConnectivityOnlyTetrahedralFrame result mol center) := by
  unfold ConnectivityOnlyTetrahedralFrame
  infer_instance

end Perception

end BlueBookP92

end TetraStereo.OneCenter
