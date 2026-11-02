import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

/-!
# Authority carrier for fused and bridged-fused P-93 rows

The fused skeleton is represented by its exact atom set and identified fusion edges.  A separate
fused-axis constructor is necessary because the generic P-93 axis constructor is deliberately
restricted to perceived cumulenes.  Nearest fusion-pair selection retains physical atom identity,
graph distance, and the source locant tie-break instead of reducing candidates to two numbers.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Cyclic

structure P93AuthorityFusionEdge where
  first : Nat
  second : Nat
  deriving DecidableEq, Repr

def P93AuthorityFusionEdge.ValidFor
    (source : AuthoritativeChemicalInput) (atoms : List Nat)
    (edge : P93AuthorityFusionEdge) : Prop :=
  edge.first < edge.second ∧
    edge.first ∈ atoms ∧ edge.second ∈ atoms ∧
    P93AuthorityBinaryBond source edge.first edge.second

/-- Exact printed fused-system locant.  `suffixRank = 0` means no alphabetic suffix;
`1..26` mean `a..z`.  Thus `4a` is represented without conflating its numeric part with a
molecular graph index. -/
structure P93FusedLocant where
  numericPart : Nat
  suffixRank : Fin 27
  deriving DecidableEq, Repr

namespace P93FusedLocant

def Valid (locant : P93FusedLocant) : Prop :=
  0 < locant.numericPart

def key (locant : P93FusedLocant) : List Nat :=
  [locant.numericPart, locant.suffixRank]

def LE (left right : P93FusedLocant) : Prop :=
  left.numericPart < right.numericPart ∨
    (left.numericPart = right.numericPart ∧ left.suffixRank ≤ right.suffixRank)

instance (left right : P93FusedLocant) : Decidable (LE left right) := by
  unfold LE
  infer_instance

theorem le_refl (locant : P93FusedLocant) : LE locant locant := by
  simp [LE]

theorem le_antisymm {left right : P93FusedLocant}
    (leftRight : LE left right) (rightLeft : LE right left) : left = right := by
  rcases left with ⟨leftNumeric, leftSuffix⟩
  rcases right with ⟨rightNumeric, rightSuffix⟩
  simp [LE] at leftRight rightLeft
  have numericEq : leftNumeric = rightNumeric := by omega
  have suffixEq : leftSuffix = rightSuffix := Fin.ext (by omega)
  subst rightNumeric
  subst rightSuffix
  rfl

theorem le_trans {first second third : P93FusedLocant}
    (firstSecond : LE first second) (secondThird : LE second third) : LE first third := by
  rcases first with ⟨firstNumeric, firstSuffix⟩
  rcases second with ⟨secondNumeric, secondSuffix⟩
  rcases third with ⟨thirdNumeric, thirdSuffix⟩
  simp [LE] at firstSecond secondThird ⊢
  omega

theorem le_total (left right : P93FusedLocant) : LE left right ∨ LE right left := by
  rcases left with ⟨leftNumeric, leftSuffix⟩
  rcases right with ⟨rightNumeric, rightSuffix⟩
  simp [LE]
  omega

def min (left right : P93FusedLocant) : P93FusedLocant :=
  if LE left right then left else right

end P93FusedLocant

structure P93AuthorityFusedSystem where
  atoms : List Nat
  fusionEdges : List P93AuthorityFusionEdge
  /-- Exact source locant for every fusion atom. -/
  fusionLocants : List (Nat × P93FusedLocant)
  deriving DecidableEq, Repr

def P93AuthorityFusedSystem.MechanicallyValidFor
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityFusedSystem) : Prop :=
  3 ≤ system.atoms.length ∧ system.atoms.Nodup ∧
    P93AuthorityAtomsBounded source system.atoms ∧
    system.fusionEdges ≠ [] ∧ system.fusionEdges.Nodup ∧
    (∀ edge ∈ system.fusionEdges, edge.ValidFor source system.atoms) ∧
    system.fusionLocants ≠ [] ∧
    (system.fusionLocants.map Prod.fst).Nodup ∧
    (system.fusionLocants.map Prod.snd).Nodup ∧
    (∀ mapping ∈ system.fusionLocants, mapping.1 ∈ system.atoms) ∧
    ∀ edge ∈ system.fusionEdges,
      (∃ locant, (edge.first, locant) ∈ system.fusionLocants) ∧
        ∃ locant, (edge.second, locant) ∈ system.fusionLocants

inductive P93FusedAuthorityUnit where
  | physical (unit : P93AuthorityPhysicalUnit)
  | fusedAxis (path : List Nat)
  deriving DecidableEq

structure P93FusedAuthorityPolicy where
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  SystemObserved :
    AuthoritativeChemicalInput → P93AuthorityFusedSystem → Prop
  UnitInSystemObserved :
    AuthoritativeChemicalInput → P93AuthorityFusedSystem →
      P93FusedAuthorityUnit → Prop
  CitationAuthorized :
    AuthoritativeChemicalInput → P93FusedLocant →
      P93FusedAuthorityUnit → Prop
  FusedAxisObserved :
    AuthoritativeChemicalInput → P93AuthorityFusedSystem → List Nat → Prop
  UnitDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityFusedSystem →
      P93FusedAuthorityUnit → FusedUnitDescriptor → Prop
  FusionPairEligible :
    AuthoritativeChemicalInput → P93AuthorityFusedSystem →
      Nat → Nat → Prop
  FusionPairCandidateObserved :
    AuthoritativeChemicalInput → P93AuthorityFusedSystem →
      Nat → Nat → Nat → P93FusedLocant → Prop
  FusionPairCitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityFusedSystem →
      Nat → Nat → P93FusedLocant → Prop
  FusionRelationObserved :
    AuthoritativeChemicalInput → P93AuthorityFusedSystem →
      Nat → Nat → CisTrans → CisTrans →
        FusionRelationDescriptor → Prop

def P93AuthorityFusedSystem.ValidFor
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityFusedSystem) : Prop :=
  system.MechanicallyValidFor source ∧
    policy.SystemObserved source system

def P93FusedPhysicalUnitSupported
    (system : P93AuthorityFusedSystem) : P93AuthorityPhysicalUnit → Prop
  | .atomCenter center => center ∈ system.atoms
  | .bond first second => first ∈ system.atoms ∧ second ∈ system.atoms
  | .axis path | .helix path => ∀ atom ∈ path, atom ∈ system.atoms
  | .plane members => ∀ atom ∈ members, atom ∈ system.atoms
  | .polyhedron _ _ => False

def P93FusedAuthorityUnit.ValidFor
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityFusedSystem) : P93FusedAuthorityUnit → Prop
  | .physical unit =>
      unit.ValidFor policy.physicalObservation source ∧
        P93FusedPhysicalUnitSupported system unit
  | .fusedAxis path =>
      2 ≤ path.length ∧ path.Nodup ∧
        P93AuthorityAtomsBounded source path ∧
        P93AuthorityCanonicalDirectedPath path ∧
        P93AuthorityConnectedPath source path ∧
        (∀ atom ∈ path, atom ∈ system.atoms) ∧
        policy.FusedAxisObserved source system path

def P93FusedUnitDescriptorMatches
    (unit : P93FusedAuthorityUnit) (descriptor : FusedUnitDescriptor) : Prop :=
  match descriptor, unit with
  | .R, .physical (.atomCenter _)
  | .S, .physical (.atomCenter _)
  | .r, .physical (.atomCenter _)
  | .s, .physical (.atomCenter _)
  | .M, .fusedAxis _
  | .P, .fusedAxis _
  | .M, .physical (.axis _)
  | .P, .physical (.axis _)
  | .M, .physical (.plane _)
  | .P, .physical (.plane _)
  | .M, .physical (.helix _)
  | .P, .physical (.helix _) => True
  | _, _ => False

def P93FusedPhysicalUnitContainsAtom
    (unit : P93AuthorityPhysicalUnit) (atom : Nat) : Prop :=
  match unit with
  | .atomCenter center => atom = center
  | .bond first second => atom = first ∨ atom = second
  | .axis path | .helix path | .plane path => atom ∈ path
  | .polyhedron center positions => atom = center ∨ atom ∈ positions.toList

def P93FusedAuthorityUnit.ContainsAtom
    (unit : P93FusedAuthorityUnit) (atom : Nat) : Prop :=
  match unit with
  | .physical physicalUnit => P93FusedPhysicalUnitContainsAtom physicalUnit atom
  | .fusedAxis path => atom ∈ path

/-- The printed fused locant cites this unit only when the fused-system locant table maps it to
an atom carried by the unit.  This prevents erasing `3a` to the unrelated numeric token `3`. -/
def P93FusedLocant.CitesUnit
    (system : P93AuthorityFusedSystem) (locant : P93FusedLocant)
    (unit : P93FusedAuthorityUnit) : Prop :=
  ∃ atom, (atom, locant) ∈ system.fusionLocants ∧ unit.ContainsAtom atom

structure P93FusedCIPAuthorityObservation
    (policy : P93FusedAuthorityPolicy) where
  system : P93AuthorityFusedSystem
  unit : P93FusedAuthorityUnit
  citation : P93FusedLocant
  descriptor : FusedUnitDescriptor

def P93FusedCIPAuthorityObservation.ValidFor
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93FusedCIPAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    observation.unit.ValidFor policy source observation.system ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    P93FusedUnitDescriptorMatches observation.unit observation.descriptor ∧
    policy.UnitDescriptorAuthorized source observation.system observation.unit
      observation.descriptor ∧
    observation.citation.Valid ∧
    observation.citation.CitesUnit observation.system observation.unit ∧
    policy.CitationAuthorized source observation.citation observation.unit

def P93AuthorityFusionAtom
    (system : P93AuthorityFusedSystem) (atom : Nat) : Prop :=
  ∃ edge ∈ system.fusionEdges, atom = edge.first ∨ atom = edge.second

structure P93FusedNearestPairCandidate where
  firstFusionAtom : Nat
  secondFusionAtom : Nat
  firstFusionLocant : P93FusedLocant
  secondFusionLocant : P93FusedLocant
  graphDistance : Nat
  lowerAtomLocant : P93FusedLocant
  deriving DecidableEq, Repr

def P93FusedNearestPairCandidate.selectionKey
    (candidate : P93FusedNearestPairCandidate) : List Nat :=
  [candidate.graphDistance] ++ candidate.lowerAtomLocant.key

def P93FusedNearestPairCandidate.StrictlyPrecedes
    (left right : P93FusedNearestPairCandidate) : Prop :=
  P93AuthorityNatListLexLE left.selectionKey right.selectionKey ∧
    ¬P93AuthorityNatListLexLE right.selectionKey left.selectionKey

def P93FusedIsUniqueSelectedNearestPair
    (candidates : List P93FusedNearestPairCandidate)
    (selected : P93FusedNearestPairCandidate) : Prop :=
  selected ∈ candidates ∧
    ∀ other ∈ candidates,
      other = selected ∨ selected.StrictlyPrecedes other

def P93FusedNearestPairCandidate.ValidFor
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityFusedSystem)
    (candidate : P93FusedNearestPairCandidate) : Prop :=
  candidate.firstFusionAtom < candidate.secondFusionAtom ∧
    P93AuthorityFusionAtom system candidate.firstFusionAtom ∧
    P93AuthorityFusionAtom system candidate.secondFusionAtom ∧
    (candidate.firstFusionAtom, candidate.firstFusionLocant) ∈ system.fusionLocants ∧
    (candidate.secondFusionAtom, candidate.secondFusionLocant) ∈ system.fusionLocants ∧
    candidate.lowerAtomLocant =
      P93FusedLocant.min candidate.firstFusionLocant candidate.secondFusionLocant ∧
    policy.FusionPairEligible source system
      candidate.firstFusionAtom candidate.secondFusionAtom ∧
    0 < candidate.graphDistance ∧
    policy.FusionPairCandidateObserved source system
      candidate.firstFusionAtom candidate.secondFusionAtom
      candidate.graphDistance candidate.lowerAtomLocant

structure P93FusedRelationAuthorityObservation
    (policy : P93FusedAuthorityPolicy) where
  system : P93AuthorityFusedSystem
  candidates : List P93FusedNearestPairCandidate
  selected : P93FusedNearestPairCandidate
  selectedCitation : P93FusedLocant
  firstJunction : CisTrans
  secondJunction : CisTrans
  legacyDescriptor : FusionRelationDescriptor
  preferredDescriptor : FusionRelationDescriptor

def P93FusedRelationAuthorityObservation.ValidFor
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93FusedRelationAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
    observation.candidates ≠ [] ∧
    (observation.candidates.map fun candidate =>
      (candidate.firstFusionAtom, candidate.secondFusionAtom)).Nodup ∧
    (∀ candidate ∈ observation.candidates,
      candidate.ValidFor policy source observation.system) ∧
    (∀ first second,
      policy.FusionPairEligible source observation.system first second →
        ∃ candidate ∈ observation.candidates,
          candidate.firstFusionAtom = first ∧
            candidate.secondFusionAtom = second) ∧
    P93FusedIsUniqueSelectedNearestPair observation.candidates
      observation.selected ∧
    (observation.legacyDescriptor = .cisoid ∨
      observation.legacyDescriptor = .transoid) ∧
    observation.preferredDescriptor = .relCIP ∧
    PreferredFusionDescription observation.preferredDescriptor ∧
    policy.FusionRelationObserved source observation.system
      observation.selected.firstFusionAtom observation.selected.secondFusionAtom
      observation.firstJunction observation.secondJunction
      observation.legacyDescriptor ∧
    observation.selectedCitation.Valid ∧
    observation.selectedCitation = observation.selected.lowerAtomLocant ∧
    policy.FusionPairCitationAuthorized source observation.system
      observation.selected.firstFusionAtom observation.selected.secondFusionAtom
      observation.selectedCitation

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93AuthorityFusedSystem.MechanicallyValidFor
assert_kernel_only TetraStereo.OneCenter.P93FusedCIPAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93FusedRelationAuthorityObservation.ValidFor
