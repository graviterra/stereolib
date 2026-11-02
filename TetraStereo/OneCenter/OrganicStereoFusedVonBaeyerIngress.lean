/-
# V-native ingress for the fused and von Baeyer P-93 authority carriers

This module supplies the missing lossless codec between the two existing authority carriers
`IUPACP93FusedAuthorityCarrier` and `IUPACP93VonBaeyerAuthorityCarrier` and an arbitrary finite
atom label type `V`.  It follows the accepted pattern of `OrganicStereoSuppliedCitationIngress`
and `OrganicStereoP93AcyclicIngress`: atom references are relabelled through one explicit
enumeration `V ≃ Fin n`; every other field is copied literally.

## What is relabelled and what is copied

The fused carrier stores three kinds of atom reference:

* the exact atom list `P93AuthorityFusedSystem.atoms`;
* the identified fusion edges `fusionEdges : List P93AuthorityFusionEdge`, whose `first`/`second`
  are atom indices (not locants);
* the ordered `(atom, P93FusedLocant)` association list `fusionLocants`, whose first component is
  an atom index and whose second component is the printed fused locant.

All three are relabelled atom-wise.  The order and multiplicity of `atoms`, `fusionEdges` and
`fusionLocants` are preserved by the codec; the `P93FusedLocant` values, including
`numericPart`/`suffixRank`, are naming data and are copied literally.

The von Baeyer carrier stores two bridgeheads and the three separately named ordered internal
paths `xBridgeInternal`, `yBridgeInternal`, `zBridgeInternal`.  Each is relabelled separately and
in order.  The codec never merges the three paths into a generic ring path: the constructor and
field distinction carries the bridge-role information and is preserved field-by-field.

Fused units distinguish the tagged `.physical` and `.fusedAxis` constructors; von Baeyer
observations use the six existing `P93AuthorityPhysicalUnit` constructors.  The accepted
`relabelUnit`/`unrelabelUnit` codec is reused, so the physical-unit constructor distinction is
preserved exactly, including `axis`/`helix`/`plane`/`polyhedron`.

Citations (`P93AuthorityCitationToken`), fused locants, descriptors, junctions, ring sides,
configuration knowledge, notations, `contextIsPIN`, bridge attachments and the
`P93VonBaeyerUnsaturationSpecification` tagged data are source nomenclature/metadata and are
copied literally, never relabelled.

## Explicit unresolved source references

`P93VonBaeyerBridgeOrientationAuthorityObservation.substituent` and the two
`P93VonBaeyerBridgeheadRelativeAuthorityObservation` ligands are atom indices that the
observation's own `ValidFor` does **not** bound: the predicate only states that they occur in a
`P93AuthorityBinaryBond`, and `P93AuthorityBinaryBond` does not itself carry participant bounds.
Adding a bound hypothesis to the codec would be a new restriction on valid observations.  The
native mirrors therefore carry these three fields as explicit raw source references
(`substituentSourceIndex`, `firstLigandSourceIndex`, `secondLigandSourceIndex`) whose numeric value
is preserved exactly.  Under a `PhysicalFrameSourceBinding` they are nevertheless provably
in range, because the binding's graph equality yields structural well-formedness of the source
molecule; those honest bounds are proved in the final section
(`bridgeOrientation_substituent_atomCount`, `bridgeheadRelative_*_atomCount`, and the
`Fintype.card` versions).

## Bounds

Bounds are derived from the actual mechanical/source validity predicates:

* fused system fields from `P93AuthorityFusedSystem.MechanicallyValidFor`;
* fused physical units from `P93FusedPhysicalUnitSupported` (the polyhedron constructor is
  `False` there), fused axes from their own `P93AuthorityAtomsBounded`;
* fused nearest-pair candidates from `P93AuthorityFusionAtom` and the fusion edge bounds;
* von Baeyer systems from `P93AuthorityVonBaeyerSystem.MechanicallyValidFor`;
* von Baeyer units from `P93VonBaeyerUnitSupported` (plane/helix/polyhedron are `False` there).

Consequently `SourceFusedVonBaeyerObservation.boundedIn_of_validFor` needs no spatial
well-formedness hypothesis: every supported unit is already an atom of the bounded system.

## Exact results

For every native system, every one of the six source observation variants, the tagged sum, and
ordered lists and correlated sets of observations, both inverse directions are proved:

* `unrelabel..._relabel...` on source records (exact record recovery, field-for-field);
* `relabel..._unrelabel...` on native records (exact native recovery).

`validFor_unrelabelObservation_relabelObservation_iff` states validity at the **same** decoded
source and policy; no arbitrary-policy or arbitrary-renumbering invariance is claimed.  The
ordered list inverse preserves order and repetitions.  The set inverse is the correlated one
(the exact codec, not an atom-count quotient).  There is no original whole observation or
`AuthoritativeChemicalInput` stored anywhere in the satellite: the source is re-encoded from the
shared finite graph/spatial/diagram source through the existing binding, and every native
system/observation field is read by the decoder.
-/

import TetraStereo.OneCenter.IUPACP93FusedAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93VonBaeyerAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace OrganicStereoFusedVonBaeyerIngress

open BlueBookP93 BlueBookP93.Cyclic
open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress

variable {V : Type*} {n : ℕ}

/-! ## Atom bounds read from the existing validity predicates -/

/-- Explicit bound predicate on a physical unit, re-exported under the same name as in the
accepted acyclic ingress. -/
abbrev UnitBoundedIn (n : ℕ) (unit : P93AuthorityPhysicalUnit) : Prop :=
  TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
    n unit

/-- Bounds of every atom reference in a fused authority system.  The three fields correspond to
the three atom-bearing lists: the atom set, the exact fusion edges and the ordered
atom/locant associations. -/
structure FusedSystemBoundedIn (n : ℕ) (system : P93AuthorityFusedSystem) : Prop where
  atomsBounded : ∀ atom ∈ system.atoms, atom < n
  edgesBounded : ∀ edge ∈ system.fusionEdges, edge.first < n ∧ edge.second < n
  locantsBounded : ∀ mapping ∈ system.fusionLocants, mapping.1 < n

/-- Bounds of a fused authority unit. -/
def FusedUnitBoundedIn (n : ℕ) : P93FusedAuthorityUnit → Prop
  | .physical unit => UnitBoundedIn n unit
  | .fusedAxis path => ∀ atom ∈ path, atom < n

/-- Bounds of a nearest fusion-pair candidate.  The locants and the graph distance are metadata,
so only the two fusion atoms are bounded. -/
structure FusedCandidateBoundedIn (n : ℕ)
    (candidate : P93FusedNearestPairCandidate) : Prop where
  firstFusionAtom : candidate.firstFusionAtom < n
  secondFusionAtom : candidate.secondFusionAtom < n

/-- Bounds of a fused CIP observation. -/
structure FusedCIPBoundedIn {policy : P93FusedAuthorityPolicy} (n : ℕ)
    (observation : P93FusedCIPAuthorityObservation policy) : Prop where
  system : FusedSystemBoundedIn n observation.system
  unit : FusedUnitBoundedIn n observation.unit

/-- Bounds of a fused relation observation.  Every candidate and the selected candidate are
bounded; the selected candidate is not assumed to be a member here (membership is derived from
the relation validity when needed). -/
structure FusedRelationBoundedIn {policy : P93FusedAuthorityPolicy} (n : ℕ)
    (observation : P93FusedRelationAuthorityObservation policy) : Prop where
  system : FusedSystemBoundedIn n observation.system
  candidates : ∀ candidate ∈ observation.candidates, FusedCandidateBoundedIn n candidate
  selected : FusedCandidateBoundedIn n observation.selected

/-- Bounds of every atom reference in a von Baeyer authority system.  The three bridge paths are
kept separate so that a change of role is visible in the bound predicate as well. -/
structure VonBaeyerSystemBoundedIn (n : ℕ)
    (system : P93AuthorityVonBaeyerSystem) : Prop where
  firstBridgehead : system.firstBridgehead < n
  secondBridgehead : system.secondBridgehead < n
  xBridgeInternal : ∀ atom ∈ system.xBridgeInternal, atom < n
  yBridgeInternal : ∀ atom ∈ system.yBridgeInternal, atom < n
  zBridgeInternal : ∀ atom ∈ system.zBridgeInternal, atom < n

/-- Every atom of the concatenated von Baeyer atom list is bounded. -/
theorem VonBaeyerSystemBoundedIn.atomsBounded {n : ℕ}
    {system : P93AuthorityVonBaeyerSystem}
    (bounded : VonBaeyerSystemBoundedIn n system) :
    ∀ atom ∈ system.atoms, atom < n := by
  intro atom member
  rw [P93AuthorityVonBaeyerSystem.atoms] at member
  rw [List.mem_append] at member
  rcases member with memberXYZ | memberZ
  · rw [List.mem_append] at memberXYZ
    rcases memberXYZ with memberXY | memberY
    · rw [List.mem_append] at memberXY
      rcases memberXY with memberFirstSecond | memberX
      · rcases List.mem_cons.mp memberFirstSecond with rfl | memberSecond
        · exact bounded.firstBridgehead
        · rcases List.mem_cons.mp memberSecond with rfl | memberNil
          · exact bounded.secondBridgehead
          · simp at memberNil
      · exact bounded.xBridgeInternal atom memberX
    · exact bounded.yBridgeInternal atom memberY
  · exact bounded.zBridgeInternal atom memberZ

/-- Bounds of a von Baeyer center observation. -/
structure VonBaeyerCenterBoundedIn {policy : P93VonBaeyerAuthorityPolicy} (n : ℕ)
    (observation : P93VonBaeyerCenterAuthorityObservation policy) : Prop where
  system : VonBaeyerSystemBoundedIn n observation.system
  unit : UnitBoundedIn n observation.unit

/-- Bounds of a bridge-orientation observation.  The `substituent` is deliberately absent: it is
carried as an explicit raw source reference and is only bounded under an actual source binding. -/
structure VonBaeyerBridgeOrientationBoundedIn {policy : P93VonBaeyerAuthorityPolicy} (n : ℕ)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy) : Prop where
  system : VonBaeyerSystemBoundedIn n observation.system
  attachmentAtom : observation.attachmentAtom < n

/-- Bounds of a bridgehead-relative observation.  The two ligands are deliberately absent for the
same reason as the bridge-orientation substituent. -/
structure VonBaeyerBridgeheadRelativeBoundedIn {policy : P93VonBaeyerAuthorityPolicy} (n : ℕ)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy) : Prop where
  system : VonBaeyerSystemBoundedIn n observation.system

/-- Bounds of an unsaturation observation. -/
structure VonBaeyerUnsaturationBoundedIn {policy : P93VonBaeyerAuthorityPolicy} (n : ℕ)
    (observation : P93VonBaeyerUnsaturationAuthorityObservation policy) : Prop where
  system : VonBaeyerSystemBoundedIn n observation.system
  unit : UnitBoundedIn n observation.unit

/-! ## Supplied mirror records -/

/-- A fusion edge over atom labels of `V`.  The `first`/`second` distinction is retained; it is a
constitutional edge, not a locant pair. -/
structure SuppliedFusionEdge (V : Type*) where
  first : V
  second : V

/-- The exact fused-system data over `V`: atom list, ordered fusion edges and ordered
`(atom, printed locant)` associations. -/
structure SuppliedFusedSystem (V : Type*) where
  atoms : List V
  fusionEdges : List (SuppliedFusionEdge V)
  fusionLocants : List (V × P93FusedLocant)

/-- A fused authority unit over `V`.  The two source constructors are retained one-for-one. -/
inductive SuppliedFusedAuthorityUnit (V : Type*) where
  | physical (unit : SuppliedPhysicalUnit V)
  | fusedAxis (path : List V)

/-- Mirror of `P93FusedCIPAuthorityObservation`.  The fused locant citation and the
`FusedUnitDescriptor` are copied literally. -/
structure SuppliedFusedCIPAuthorityObservation (V : Type*) where
  system : SuppliedFusedSystem V
  unit : SuppliedFusedAuthorityUnit V
  citation : P93FusedLocant
  descriptor : FusedUnitDescriptor

/-- Mirror of `P93FusedNearestPairCandidate`.  Physical atom identity is relabelled; the graph
distance and the three locants are copied literally. -/
structure SuppliedFusedNearestPairCandidate (V : Type*) where
  firstFusionAtom : V
  secondFusionAtom : V
  firstFusionLocant : P93FusedLocant
  secondFusionLocant : P93FusedLocant
  graphDistance : Nat
  lowerAtomLocant : P93FusedLocant

/-- Mirror of `P93FusedRelationAuthorityObservation`.  Junctions, descriptors and the selected
citation are naming data and are copied literally. -/
structure SuppliedFusedRelationAuthorityObservation (V : Type*) where
  system : SuppliedFusedSystem V
  candidates : List (SuppliedFusedNearestPairCandidate V)
  selected : SuppliedFusedNearestPairCandidate V
  selectedCitation : P93FusedLocant
  firstJunction : CisTrans
  secondJunction : CisTrans
  legacyDescriptor : FusionRelationDescriptor
  preferredDescriptor : FusionRelationDescriptor

/-- The exact von Baeyer system over `V`: both bridgeheads and the three separately named ordered
internal bridge paths. -/
structure SuppliedVonBaeyerSystem (V : Type*) where
  firstBridgehead : V
  secondBridgehead : V
  xBridgeInternal : List V
  yBridgeInternal : List V
  zBridgeInternal : List V

/-- Mirror of `P93VonBaeyerCenterAuthorityObservation`.  The citation, kind, descriptor,
configuration knowledge and notation are copied literally. -/
structure SuppliedVonBaeyerCenterAuthorityObservation (V : Type*) where
  system : SuppliedVonBaeyerSystem V
  unit : SuppliedPhysicalUnit V
  citation : P93AuthorityCitationToken
  kind : BlueBookP93.Acyclic.UnitKind
  descriptor : BlueBookP93.Acyclic.Descriptor
  knowledge : ConfigurationKnowledge
  «notation» : MonocycleNotation

/-- Mirror of `P93VonBaeyerBridgeOrientationAuthorityObservation`.  The `attachmentAtom` is a
relabelled atom; the `substituent` is retained as an explicit raw source reference (see the
module header), and the citation, attachment and descriptor are copied literally. -/
structure SuppliedVonBaeyerBridgeOrientationAuthorityObservation (V : Type*) where
  system : SuppliedVonBaeyerSystem V
  attachmentAtom : V
  substituentSourceIndex : Nat
  citation : P93AuthorityCitationToken
  attachment : BridgeAttachment
  descriptor : BridgeDescriptor

/-- Mirror of `P93VonBaeyerBridgeheadRelativeAuthorityObservation`.  The two ligands are retained
as explicit raw source references; both optional citations, sides, descriptor, `contextIsPIN` and
notation are copied literally. -/
structure SuppliedVonBaeyerBridgeheadRelativeAuthorityObservation (V : Type*) where
  system : SuppliedVonBaeyerSystem V
  firstLigandSourceIndex : Nat
  secondLigandSourceIndex : Nat
  firstCitation? : Option P93AuthorityCitationToken
  secondCitation? : Option P93AuthorityCitationToken
  firstSide : RingSide
  secondSide : RingSide
  descriptor : CisTrans
  contextIsPIN : Bool
  «notation» : BridgeheadRelativeNotation

/-- Mirror of `P93VonBaeyerUnsaturationAuthorityObservation`.  The unit is relabelled; the
citation and the complete tagged specification are copied literally. -/
structure SuppliedVonBaeyerUnsaturationAuthorityObservation (V : Type*) where
  system : SuppliedVonBaeyerSystem V
  unit : SuppliedPhysicalUnit V
  citation : P93AuthorityCitationToken
  specification : P93VonBaeyerUnsaturationSpecification

/-! ## Fused system codec -/

/-- Relabel every atom reference of a fused authority system.  Fusion edges and atom/locant
associations keep their order, multiplicity and second (locant) component. -/
def relabelFusedSystem [DecidableEq V] (enumeration : V ≃ Fin n)
    (system : P93AuthorityFusedSystem)
    (bounded : FusedSystemBoundedIn n system) : SuppliedFusedSystem V where
  atoms := relabelList enumeration system.atoms bounded.atomsBounded
  fusionEdges := system.fusionEdges.attach.map fun edge =>
    { first := decodeAtom enumeration edge.1.first
        (bounded.edgesBounded edge.1 edge.2).1
      second := decodeAtom enumeration edge.1.second
        (bounded.edgesBounded edge.1 edge.2).2 }
  fusionLocants := system.fusionLocants.attach.map fun mapping =>
    (decodeAtom enumeration mapping.1.1
      (bounded.locantsBounded mapping.1 mapping.2), mapping.1.2)

/-- Decode a supplied fused authority system to raw atom indices. -/
def unrelabelFusedSystem (enumeration : V ≃ Fin n)
    (system : SuppliedFusedSystem V) : P93AuthorityFusedSystem where
  atoms := unrelabelList enumeration system.atoms
  fusionEdges := system.fusionEdges.map fun edge =>
    { first := encodeAtom enumeration edge.first
      second := encodeAtom enumeration edge.second }
  fusionLocants := system.fusionLocants.map fun mapping =>
    (encodeAtom enumeration mapping.1, mapping.2)

/-- Every decoded fused system satisfies the explicit bounds. -/
def unrelabelFusedSystemBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    (system : SuppliedFusedSystem V) :
    FusedSystemBoundedIn n (unrelabelFusedSystem enumeration system) where
  atomsBounded := unrelabelList_bounded enumeration system.atoms
  edgesBounded := by
    intro edge member
    rw [unrelabelFusedSystem, List.mem_map] at member
    rcases member with ⟨supplied, _suppliedMember, rfl⟩
    exact ⟨encodeAtom_lt enumeration supplied.first,
      encodeAtom_lt enumeration supplied.second⟩
  locantsBounded := by
    intro mapping member
    rw [unrelabelFusedSystem, List.mem_map] at member
    rcases member with ⟨supplied, _suppliedMember, rfl⟩
    exact encodeAtom_lt enumeration supplied.1

/-- Exact recovery of a fused authority system, including the atom list, edge orientation/order
and the ordered atom/locant associations. -/
theorem unrelabelFusedSystem_relabelFusedSystem [DecidableEq V] (enumeration : V ≃ Fin n)
    (system : P93AuthorityFusedSystem) (bounded : FusedSystemBoundedIn n system) :
    unrelabelFusedSystem enumeration (relabelFusedSystem enumeration system bounded) =
      system := by
  rcases system with ⟨atoms, fusionEdges, fusionLocants⟩
  simp only [relabelFusedSystem, unrelabelFusedSystem]
  rw [P93AuthorityFusedSystem.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp [unrelabelList_relabelList]
  · rw [List.map_map]
    trans fusionEdges.attach.map Subtype.val
    · apply List.map_congr_left
      intro edge _
      rcases edge with ⟨⟨first, second⟩, _member⟩
      simp [Function.comp_apply, encodeAtom_decodeAtom]
    · exact List.attach_map_subtype_val fusionEdges
  · rw [List.map_map]
    trans fusionLocants.attach.map Subtype.val
    · apply List.map_congr_left
      intro mapping _
      rcases mapping with ⟨⟨atom, locant⟩, _member⟩
      simp [Function.comp_apply, encodeAtom_decodeAtom]
    · exact List.attach_map_subtype_val fusionLocants

/-- Relabelling a decoded fused authority system returns the supplied system. -/
theorem relabelFusedSystem_unrelabelFusedSystem [DecidableEq V] (enumeration : V ≃ Fin n)
    (system : SuppliedFusedSystem V) :
    relabelFusedSystem enumeration (unrelabelFusedSystem enumeration system)
        (unrelabelFusedSystemBounded enumeration system) = system := by
  rcases system with ⟨atoms, fusionEdges, fusionLocants⟩
  simp only [relabelFusedSystem, unrelabelFusedSystem]
  rw [SuppliedFusedSystem.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp [relabelList_unrelabelList]
  · rw [List.attach_map, List.map_map]
    trans fusionEdges.attach.map Subtype.val
    · apply List.map_congr_left
      intro edge _
      rcases edge with ⟨edge, _member⟩
      cases edge
      simp [Function.comp_apply, decodeAtom_encodeAtom]
    · exact List.attach_map_subtype_val fusionEdges
  · rw [List.attach_map, List.map_map]
    trans fusionLocants.attach.map Subtype.val
    · apply List.map_congr_left
      intro mapping _
      rcases mapping with ⟨mapping, _member⟩
      rcases mapping with ⟨atom, locant⟩
      simp [Function.comp_apply, decodeAtom_encodeAtom]
    · exact List.attach_map_subtype_val fusionLocants

/-! ## Fused authority unit codec -/

/-- Relabel a fused authority unit.  The `.physical` and `.fusedAxis` constructor distinction is
preserved exactly. -/
def relabelFusedUnit [DecidableEq V] (enumeration : V ≃ Fin n) :
    (unit : P93FusedAuthorityUnit) → FusedUnitBoundedIn n unit →
      SuppliedFusedAuthorityUnit V
  | .physical unit, bounded => .physical (relabelUnit enumeration unit bounded)
  | .fusedAxis path, bounded => .fusedAxis (relabelList enumeration path bounded)

/-- Decode a supplied fused authority unit. -/
def unrelabelFusedUnit (enumeration : V ≃ Fin n) :
    SuppliedFusedAuthorityUnit V → P93FusedAuthorityUnit
  | .physical unit => .physical (unrelabelUnit enumeration unit)
  | .fusedAxis path => .fusedAxis (unrelabelList enumeration path)

/-- Every decoded fused unit satisfies the explicit bounds. -/
def unrelabelFusedUnitBounded (enumeration : V ≃ Fin n) :
    (unit : SuppliedFusedAuthorityUnit V) →
      FusedUnitBoundedIn n (unrelabelFusedUnit enumeration unit)
  | .physical unit => unrelabelUnitBounded enumeration unit
  | .fusedAxis path => unrelabelList_bounded enumeration path

/-- Exact recovery of a fused authority unit. -/
theorem unrelabelFusedUnit_relabelFusedUnit [DecidableEq V] (enumeration : V ≃ Fin n)
    (unit : P93FusedAuthorityUnit) (bounded : FusedUnitBoundedIn n unit) :
    unrelabelFusedUnit enumeration (relabelFusedUnit enumeration unit bounded) = unit := by
  cases unit with
  | physical unit =>
      simp [relabelFusedUnit, unrelabelFusedUnit, unrelabelUnit_relabelUnit]
  | fusedAxis path =>
      simp [relabelFusedUnit, unrelabelFusedUnit, unrelabelList_relabelList]

/-- Relabelling a decoded fused authority unit returns the supplied unit. -/
theorem relabelFusedUnit_unrelabelFusedUnit [DecidableEq V] (enumeration : V ≃ Fin n)
    (unit : SuppliedFusedAuthorityUnit V) :
    relabelFusedUnit enumeration (unrelabelFusedUnit enumeration unit)
        (unrelabelFusedUnitBounded enumeration unit) = unit := by
  cases unit with
  | physical unit =>
      simp [relabelFusedUnit, unrelabelFusedUnit, relabelUnit_unrelabelUnit]
  | fusedAxis path =>
      simp [relabelFusedUnit, unrelabelFusedUnit, relabelList_unrelabelList]

/-! ## Fused nearest-pair candidate codec -/

/-- Relabel the two fusion atoms of a candidate, copying its locants and distance literally. -/
def relabelFusedCandidate [DecidableEq V] (enumeration : V ≃ Fin n)
    (candidate : P93FusedNearestPairCandidate)
    (bounded : FusedCandidateBoundedIn n candidate) :
    SuppliedFusedNearestPairCandidate V where
  firstFusionAtom := decodeAtom enumeration candidate.firstFusionAtom
    bounded.firstFusionAtom
  secondFusionAtom := decodeAtom enumeration candidate.secondFusionAtom
    bounded.secondFusionAtom
  firstFusionLocant := candidate.firstFusionLocant
  secondFusionLocant := candidate.secondFusionLocant
  graphDistance := candidate.graphDistance
  lowerAtomLocant := candidate.lowerAtomLocant

/-- Decode a supplied nearest-pair candidate. -/
def unrelabelFusedCandidate (enumeration : V ≃ Fin n)
    (candidate : SuppliedFusedNearestPairCandidate V) :
    P93FusedNearestPairCandidate where
  firstFusionAtom := encodeAtom enumeration candidate.firstFusionAtom
  secondFusionAtom := encodeAtom enumeration candidate.secondFusionAtom
  firstFusionLocant := candidate.firstFusionLocant
  secondFusionLocant := candidate.secondFusionLocant
  graphDistance := candidate.graphDistance
  lowerAtomLocant := candidate.lowerAtomLocant

/-- Every decoded candidate satisfies the explicit bounds. -/
def unrelabelFusedCandidateBounded (enumeration : V ≃ Fin n)
    (candidate : SuppliedFusedNearestPairCandidate V) :
    FusedCandidateBoundedIn n (unrelabelFusedCandidate enumeration candidate) where
  firstFusionAtom := encodeAtom_lt enumeration candidate.firstFusionAtom
  secondFusionAtom := encodeAtom_lt enumeration candidate.secondFusionAtom

/-- Exact recovery of a nearest-pair candidate. -/
theorem unrelabelFusedCandidate_relabelFusedCandidate [DecidableEq V]
    (enumeration : V ≃ Fin n) (candidate : P93FusedNearestPairCandidate)
    (bounded : FusedCandidateBoundedIn n candidate) :
    unrelabelFusedCandidate enumeration
        (relabelFusedCandidate enumeration candidate bounded) = candidate := by
  rcases candidate with ⟨firstAtom, secondAtom, firstLocant, secondLocant,
    distance, lowerLocant⟩
  simp [relabelFusedCandidate, unrelabelFusedCandidate, encodeAtom_decodeAtom]

/-- Relabelling a decoded nearest-pair candidate returns the supplied candidate. -/
theorem relabelFusedCandidate_unrelabelFusedCandidate [DecidableEq V]
    (enumeration : V ≃ Fin n) (candidate : SuppliedFusedNearestPairCandidate V) :
    relabelFusedCandidate enumeration (unrelabelFusedCandidate enumeration candidate)
        (unrelabelFusedCandidateBounded enumeration candidate) = candidate := by
  rcases candidate with ⟨firstAtom, secondAtom, firstLocant, secondLocant,
    distance, lowerLocant⟩
  simp [relabelFusedCandidate, unrelabelFusedCandidate, decodeAtom_encodeAtom]

/-- Ordered list of bounded nearest-pair candidates. -/
def relabelFusedCandidates [DecidableEq V] (enumeration : V ≃ Fin n)
    (candidates : List P93FusedNearestPairCandidate)
    (bounded : ∀ candidate ∈ candidates, FusedCandidateBoundedIn n candidate) :
    List (SuppliedFusedNearestPairCandidate V) :=
  candidates.attach.map fun candidate =>
    relabelFusedCandidate enumeration candidate.1
      (bounded candidate.1 candidate.2)

/-- Decode an ordered list of supplied nearest-pair candidates. -/
def unrelabelFusedCandidates (enumeration : V ≃ Fin n)
    (candidates : List (SuppliedFusedNearestPairCandidate V)) :
    List P93FusedNearestPairCandidate :=
  candidates.map (unrelabelFusedCandidate enumeration)

/-- Every decoded candidate in a list satisfies the explicit bounds. -/
def unrelabelFusedCandidatesBounded (enumeration : V ≃ Fin n)
    (candidates : List (SuppliedFusedNearestPairCandidate V)) :
    ∀ candidate ∈ unrelabelFusedCandidates enumeration candidates,
      FusedCandidateBoundedIn n candidate := by
  intro candidate member
  rw [unrelabelFusedCandidates, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact unrelabelFusedCandidateBounded enumeration supplied

@[simp] theorem relabelFusedCandidates_length [DecidableEq V] (enumeration : V ≃ Fin n)
    (candidates : List P93FusedNearestPairCandidate)
    (bounded : ∀ candidate ∈ candidates, FusedCandidateBoundedIn n candidate) :
    (relabelFusedCandidates enumeration candidates bounded).length =
      candidates.length := by
  simp [relabelFusedCandidates]

@[simp] theorem unrelabelFusedCandidates_length (enumeration : V ≃ Fin n)
    (candidates : List (SuppliedFusedNearestPairCandidate V)) :
    (unrelabelFusedCandidates enumeration candidates).length = candidates.length := by
  simp [unrelabelFusedCandidates]

/-- Exact recovery of the ordered candidate list, including order and repetitions. -/
theorem unrelabelFusedCandidates_relabelFusedCandidates [DecidableEq V]
    (enumeration : V ≃ Fin n) (candidates : List P93FusedNearestPairCandidate)
    (bounded : ∀ candidate ∈ candidates, FusedCandidateBoundedIn n candidate) :
    unrelabelFusedCandidates enumeration
        (relabelFusedCandidates enumeration candidates bounded) = candidates := by
  unfold unrelabelFusedCandidates relabelFusedCandidates
  rw [List.map_map]
  trans candidates.attach.map Subtype.val
  · apply List.map_congr_left
    intro candidate _
    exact unrelabelFusedCandidate_relabelFusedCandidate enumeration candidate.1
      (bounded candidate.1 candidate.2)
  · exact List.attach_map_subtype_val candidates

/-- Relabelling a decoded candidate list returns the supplied list. -/
theorem relabelFusedCandidates_unrelabelFusedCandidates [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (candidates : List (SuppliedFusedNearestPairCandidate V)) :
    relabelFusedCandidates enumeration (unrelabelFusedCandidates enumeration candidates)
        (unrelabelFusedCandidatesBounded enumeration candidates) = candidates := by
  unfold relabelFusedCandidates unrelabelFusedCandidates
  rw [List.attach_map, List.map_map]
  trans candidates.attach.map Subtype.val
  · apply List.map_congr_left
    intro candidate _
    exact relabelFusedCandidate_unrelabelFusedCandidate enumeration candidate.1
  · exact List.attach_map_subtype_val candidates

/-! ## Von Baeyer system codec -/

/-- Relabel a von Baeyer system.  Bridgeheads and each named internal bridge path are relabelled
separately; the three paths are never merged. -/
def relabelVonBaeyerSystem [DecidableEq V] (enumeration : V ≃ Fin n)
    (system : P93AuthorityVonBaeyerSystem)
    (bounded : VonBaeyerSystemBoundedIn n system) : SuppliedVonBaeyerSystem V where
  firstBridgehead := decodeAtom enumeration system.firstBridgehead
    bounded.firstBridgehead
  secondBridgehead := decodeAtom enumeration system.secondBridgehead
    bounded.secondBridgehead
  xBridgeInternal := relabelList enumeration system.xBridgeInternal
    bounded.xBridgeInternal
  yBridgeInternal := relabelList enumeration system.yBridgeInternal
    bounded.yBridgeInternal
  zBridgeInternal := relabelList enumeration system.zBridgeInternal
    bounded.zBridgeInternal

/-- Decode a supplied von Baeyer system. -/
def unrelabelVonBaeyerSystem (enumeration : V ≃ Fin n)
    (system : SuppliedVonBaeyerSystem V) : P93AuthorityVonBaeyerSystem where
  firstBridgehead := encodeAtom enumeration system.firstBridgehead
  secondBridgehead := encodeAtom enumeration system.secondBridgehead
  xBridgeInternal := unrelabelList enumeration system.xBridgeInternal
  yBridgeInternal := unrelabelList enumeration system.yBridgeInternal
  zBridgeInternal := unrelabelList enumeration system.zBridgeInternal

/-- Every decoded von Baeyer system satisfies the explicit bounds. -/
def unrelabelVonBaeyerSystemBounded (enumeration : V ≃ Fin n)
    (system : SuppliedVonBaeyerSystem V) :
    VonBaeyerSystemBoundedIn n (unrelabelVonBaeyerSystem enumeration system) where
  firstBridgehead := encodeAtom_lt enumeration system.firstBridgehead
  secondBridgehead := encodeAtom_lt enumeration system.secondBridgehead
  xBridgeInternal := unrelabelList_bounded enumeration system.xBridgeInternal
  yBridgeInternal := unrelabelList_bounded enumeration system.yBridgeInternal
  zBridgeInternal := unrelabelList_bounded enumeration system.zBridgeInternal

/-- The three named internal bridge paths are independent fields of the relabelled system. -/
@[simp] theorem relabelVonBaeyerSystem_xBridgeInternal [DecidableEq V]
    (enumeration : V ≃ Fin n) (system : P93AuthorityVonBaeyerSystem)
    (bounded : VonBaeyerSystemBoundedIn n system) :
    (relabelVonBaeyerSystem enumeration system bounded).xBridgeInternal =
      relabelList enumeration system.xBridgeInternal bounded.xBridgeInternal := rfl

@[simp] theorem relabelVonBaeyerSystem_yBridgeInternal [DecidableEq V]
    (enumeration : V ≃ Fin n) (system : P93AuthorityVonBaeyerSystem)
    (bounded : VonBaeyerSystemBoundedIn n system) :
    (relabelVonBaeyerSystem enumeration system bounded).yBridgeInternal =
      relabelList enumeration system.yBridgeInternal bounded.yBridgeInternal := rfl

@[simp] theorem relabelVonBaeyerSystem_zBridgeInternal [DecidableEq V]
    (enumeration : V ≃ Fin n) (system : P93AuthorityVonBaeyerSystem)
    (bounded : VonBaeyerSystemBoundedIn n system) :
    (relabelVonBaeyerSystem enumeration system bounded).zBridgeInternal =
      relabelList enumeration system.zBridgeInternal bounded.zBridgeInternal := rfl

/-- Exact recovery of a von Baeyer system, including both bridgeheads and the order, repetition
and role of all three internal paths. -/
theorem unrelabelVonBaeyerSystem_relabelVonBaeyerSystem [DecidableEq V]
    (enumeration : V ≃ Fin n) (system : P93AuthorityVonBaeyerSystem)
    (bounded : VonBaeyerSystemBoundedIn n system) :
    unrelabelVonBaeyerSystem enumeration
        (relabelVonBaeyerSystem enumeration system bounded) = system := by
  rcases system with ⟨firstBridgehead, secondBridgehead, xBridge, yBridge, zBridge⟩
  simp only [relabelVonBaeyerSystem, unrelabelVonBaeyerSystem]
  rw [P93AuthorityVonBaeyerSystem.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [encodeAtom_decodeAtom]
  · simp [encodeAtom_decodeAtom]
  · simp [unrelabelList_relabelList]
  · simp [unrelabelList_relabelList]
  · simp [unrelabelList_relabelList]

/-- Relabelling a decoded von Baeyer system returns the supplied system. -/
theorem relabelVonBaeyerSystem_unrelabelVonBaeyerSystem [DecidableEq V]
    (enumeration : V ≃ Fin n) (system : SuppliedVonBaeyerSystem V) :
    relabelVonBaeyerSystem enumeration (unrelabelVonBaeyerSystem enumeration system)
        (unrelabelVonBaeyerSystemBounded enumeration system) = system := by
  rcases system with ⟨firstBridgehead, secondBridgehead, xBridge, yBridge, zBridge⟩
  simp only [relabelVonBaeyerSystem, unrelabelVonBaeyerSystem]
  rw [SuppliedVonBaeyerSystem.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [decodeAtom_encodeAtom]
  · simp [decodeAtom_encodeAtom]
  · simp [relabelList_unrelabelList]
  · simp [relabelList_unrelabelList]
  · simp [relabelList_unrelabelList]

/-! ## Fused CIP observation codec -/

/-- Relabel a fused CIP observation.  The fused locant citation and descriptor are copied
literally. -/
def relabelFusedCIPObservation [DecidableEq V] {policy : P93FusedAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (observation : P93FusedCIPAuthorityObservation policy)
    (bounded : FusedCIPBoundedIn n observation) :
    SuppliedFusedCIPAuthorityObservation V where
  system := relabelFusedSystem enumeration observation.system bounded.system
  unit := relabelFusedUnit enumeration observation.unit bounded.unit
  citation := observation.citation
  descriptor := observation.descriptor

/-- Decode a supplied fused CIP observation at the given fused policy. -/
def unrelabelFusedCIPObservation (policy : P93FusedAuthorityPolicy)
    (enumeration : V ≃ Fin n)
    (observation : SuppliedFusedCIPAuthorityObservation V) :
    P93FusedCIPAuthorityObservation policy where
  system := unrelabelFusedSystem enumeration observation.system
  unit := unrelabelFusedUnit enumeration observation.unit
  citation := observation.citation
  descriptor := observation.descriptor

/-- Every decoded fused CIP observation satisfies the explicit bounds. -/
def unrelabelFusedCIPObservationBounded [DecidableEq V]
    (policy : P93FusedAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedFusedCIPAuthorityObservation V) :
    FusedCIPBoundedIn n
      (unrelabelFusedCIPObservation policy enumeration observation) where
  system := unrelabelFusedSystemBounded enumeration observation.system
  unit := unrelabelFusedUnitBounded enumeration observation.unit

/-- Exact recovery of a fused CIP observation. -/
theorem unrelabelFusedCIPObservation_relabelFusedCIPObservation [DecidableEq V]
    {policy : P93FusedAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93FusedCIPAuthorityObservation policy)
    (bounded : FusedCIPBoundedIn n observation) :
    unrelabelFusedCIPObservation policy enumeration
        (relabelFusedCIPObservation enumeration observation bounded) = observation := by
  rcases observation with ⟨system, unit, citation, descriptor⟩
  simp [relabelFusedCIPObservation, unrelabelFusedCIPObservation,
    unrelabelFusedSystem_relabelFusedSystem,
    unrelabelFusedUnit_relabelFusedUnit]

/-- Relabelling a decoded fused CIP observation returns the supplied observation. -/
theorem relabelFusedCIPObservation_unrelabelFusedCIPObservation [DecidableEq V]
    (policy : P93FusedAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedFusedCIPAuthorityObservation V) :
    relabelFusedCIPObservation enumeration
        (unrelabelFusedCIPObservation policy enumeration observation)
        (unrelabelFusedCIPObservationBounded policy enumeration observation) =
      observation := by
  rcases observation with ⟨system, unit, citation, descriptor⟩
  simp [relabelFusedCIPObservation, unrelabelFusedCIPObservation,
    relabelFusedSystem_unrelabelFusedSystem,
    relabelFusedUnit_unrelabelFusedUnit]

/-! ## Fused relation observation codec -/

/-- Relabel a fused relation observation.  Every candidate's fusion atoms are relabelled; all
locants, junctions, descriptors and the selected citation are copied literally. -/
def relabelFusedRelationObservation [DecidableEq V] {policy : P93FusedAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (observation : P93FusedRelationAuthorityObservation policy)
    (bounded : FusedRelationBoundedIn n observation) :
    SuppliedFusedRelationAuthorityObservation V where
  system := relabelFusedSystem enumeration observation.system bounded.system
  candidates := relabelFusedCandidates enumeration observation.candidates
    bounded.candidates
  selected := relabelFusedCandidate enumeration observation.selected bounded.selected
  selectedCitation := observation.selectedCitation
  firstJunction := observation.firstJunction
  secondJunction := observation.secondJunction
  legacyDescriptor := observation.legacyDescriptor
  preferredDescriptor := observation.preferredDescriptor

/-- Decode a supplied fused relation observation at the given fused policy. -/
def unrelabelFusedRelationObservation (policy : P93FusedAuthorityPolicy)
    (enumeration : V ≃ Fin n)
    (observation : SuppliedFusedRelationAuthorityObservation V) :
    P93FusedRelationAuthorityObservation policy where
  system := unrelabelFusedSystem enumeration observation.system
  candidates := unrelabelFusedCandidates enumeration observation.candidates
  selected := unrelabelFusedCandidate enumeration observation.selected
  selectedCitation := observation.selectedCitation
  firstJunction := observation.firstJunction
  secondJunction := observation.secondJunction
  legacyDescriptor := observation.legacyDescriptor
  preferredDescriptor := observation.preferredDescriptor

/-- Every decoded fused relation observation satisfies the explicit bounds. -/
def unrelabelFusedRelationObservationBounded [DecidableEq V]
    (policy : P93FusedAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedFusedRelationAuthorityObservation V) :
    FusedRelationBoundedIn n
      (unrelabelFusedRelationObservation policy enumeration observation) where
  system := unrelabelFusedSystemBounded enumeration observation.system
  candidates := unrelabelFusedCandidatesBounded enumeration observation.candidates
  selected := unrelabelFusedCandidateBounded enumeration observation.selected

/-- Exact recovery of a fused relation observation. -/
theorem unrelabelFusedRelationObservation_relabelFusedRelationObservation [DecidableEq V]
    {policy : P93FusedAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93FusedRelationAuthorityObservation policy)
    (bounded : FusedRelationBoundedIn n observation) :
    unrelabelFusedRelationObservation policy enumeration
        (relabelFusedRelationObservation enumeration observation bounded) =
      observation := by
  rcases observation with ⟨system, candidates, selected, selectedCitation,
    firstJunction, secondJunction, legacyDescriptor, preferredDescriptor⟩
  simp [relabelFusedRelationObservation, unrelabelFusedRelationObservation,
    unrelabelFusedSystem_relabelFusedSystem,
    unrelabelFusedCandidates_relabelFusedCandidates,
    unrelabelFusedCandidate_relabelFusedCandidate]

/-- Relabelling a decoded fused relation observation returns the supplied observation. -/
theorem relabelFusedRelationObservation_unrelabelFusedRelationObservation [DecidableEq V]
    (policy : P93FusedAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedFusedRelationAuthorityObservation V) :
    relabelFusedRelationObservation enumeration
        (unrelabelFusedRelationObservation policy enumeration observation)
        (unrelabelFusedRelationObservationBounded policy enumeration observation) =
      observation := by
  rcases observation with ⟨system, candidates, selected, selectedCitation,
    firstJunction, secondJunction, legacyDescriptor, preferredDescriptor⟩
  simp [relabelFusedRelationObservation, unrelabelFusedRelationObservation,
    relabelFusedSystem_unrelabelFusedSystem,
    relabelFusedCandidates_unrelabelFusedCandidates,
    relabelFusedCandidate_unrelabelFusedCandidate]

/-! ## Von Baeyer center observation codec -/

/-- Relabel a von Baeyer center observation.  The citation, kind, descriptor, configuration
knowledge and notation are copied literally. -/
def relabelVonBaeyerCenterObservation [DecidableEq V]
    {policy : P93VonBaeyerAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93VonBaeyerCenterAuthorityObservation policy)
    (bounded : VonBaeyerCenterBoundedIn n observation) :
    SuppliedVonBaeyerCenterAuthorityObservation V where
  system := relabelVonBaeyerSystem enumeration observation.system bounded.system
  unit := relabelUnit enumeration observation.unit bounded.unit
  citation := observation.citation
  kind := observation.kind
  descriptor := observation.descriptor
  knowledge := observation.knowledge
  «notation» := observation.«notation»

/-- Decode a supplied von Baeyer center observation at the given von Baeyer policy. -/
def unrelabelVonBaeyerCenterObservation (policy : P93VonBaeyerAuthorityPolicy)
    (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerCenterAuthorityObservation V) :
    P93VonBaeyerCenterAuthorityObservation policy where
  system := unrelabelVonBaeyerSystem enumeration observation.system
  unit := unrelabelUnit enumeration observation.unit
  citation := observation.citation
  kind := observation.kind
  descriptor := observation.descriptor
  knowledge := observation.knowledge
  «notation» := observation.«notation»

/-- Every decoded von Baeyer center observation satisfies the explicit bounds. -/
def unrelabelVonBaeyerCenterObservationBounded [DecidableEq V]
    (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerCenterAuthorityObservation V) :
    VonBaeyerCenterBoundedIn n
      (unrelabelVonBaeyerCenterObservation policy enumeration observation) where
  system := unrelabelVonBaeyerSystemBounded enumeration observation.system
  unit := unrelabelUnitBounded enumeration observation.unit

/-- Exact recovery of a von Baeyer center observation. -/
theorem unrelabelVonBaeyerCenterObservation_relabelVonBaeyerCenterObservation
    [DecidableEq V] {policy : P93VonBaeyerAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93VonBaeyerCenterAuthorityObservation policy)
    (bounded : VonBaeyerCenterBoundedIn n observation) :
    unrelabelVonBaeyerCenterObservation policy enumeration
        (relabelVonBaeyerCenterObservation enumeration observation bounded) =
      observation := by
  rcases observation with ⟨system, unit, citation, kind, descriptor, knowledge,
    notationValue⟩
  simp [relabelVonBaeyerCenterObservation, unrelabelVonBaeyerCenterObservation,
    unrelabelVonBaeyerSystem_relabelVonBaeyerSystem,
    unrelabelUnit_relabelUnit]

/-- Relabelling a decoded von Baeyer center observation returns the supplied observation. -/
theorem relabelVonBaeyerCenterObservation_unrelabelVonBaeyerCenterObservation
    [DecidableEq V] (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerCenterAuthorityObservation V) :
    relabelVonBaeyerCenterObservation enumeration
        (unrelabelVonBaeyerCenterObservation policy enumeration observation)
        (unrelabelVonBaeyerCenterObservationBounded policy enumeration observation) =
      observation := by
  rcases observation with ⟨system, unit, citation, kind, descriptor, knowledge,
    notationValue⟩
  simp [relabelVonBaeyerCenterObservation, unrelabelVonBaeyerCenterObservation,
    relabelVonBaeyerSystem_unrelabelVonBaeyerSystem,
    relabelUnit_unrelabelUnit]

/-! ## Von Baeyer bridge-orientation observation codec -/

/-- Relabel a bridge-orientation observation.  The attachment atom is relabelled; the
substituent is an explicit raw source reference and is preserved numerically. -/
def relabelVonBaeyerBridgeOrientationObservation [DecidableEq V]
    {policy : P93VonBaeyerAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy)
    (bounded : VonBaeyerBridgeOrientationBoundedIn n observation) :
    SuppliedVonBaeyerBridgeOrientationAuthorityObservation V where
  system := relabelVonBaeyerSystem enumeration observation.system bounded.system
  attachmentAtom := decodeAtom enumeration observation.attachmentAtom
    bounded.attachmentAtom
  substituentSourceIndex := observation.substituent
  citation := observation.citation
  attachment := observation.attachment
  descriptor := observation.descriptor

/-- Decode a supplied bridge-orientation observation at the given von Baeyer policy. -/
def unrelabelVonBaeyerBridgeOrientationObservation (policy : P93VonBaeyerAuthorityPolicy)
    (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerBridgeOrientationAuthorityObservation V) :
    P93VonBaeyerBridgeOrientationAuthorityObservation policy where
  system := unrelabelVonBaeyerSystem enumeration observation.system
  attachmentAtom := encodeAtom enumeration observation.attachmentAtom
  substituent := observation.substituentSourceIndex
  citation := observation.citation
  attachment := observation.attachment
  descriptor := observation.descriptor

/-- Every decoded bridge-orientation observation satisfies the explicit bounds.  The substituent
is intentionally not bounded here: the source observation's own validity does not bound it. -/
def unrelabelVonBaeyerBridgeOrientationObservationBounded [DecidableEq V]
    (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerBridgeOrientationAuthorityObservation V) :
    VonBaeyerBridgeOrientationBoundedIn n
      (unrelabelVonBaeyerBridgeOrientationObservation policy enumeration observation) where
  system := unrelabelVonBaeyerSystemBounded enumeration observation.system
  attachmentAtom := encodeAtom_lt enumeration observation.attachmentAtom

/-- Exact recovery of a bridge-orientation observation, including the raw substituent index. -/
theorem
    unrelabelVonBaeyerBridgeOrientationObservation_relabelVonBaeyerBridgeOrientationObservation
    [DecidableEq V] {policy : P93VonBaeyerAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy)
    (bounded : VonBaeyerBridgeOrientationBoundedIn n observation) :
    unrelabelVonBaeyerBridgeOrientationObservation policy enumeration
        (relabelVonBaeyerBridgeOrientationObservation enumeration observation bounded) =
      observation := by
  rcases observation with ⟨system, attachmentAtom, substituent, citation, attachment,
    descriptor⟩
  simp [relabelVonBaeyerBridgeOrientationObservation,
    unrelabelVonBaeyerBridgeOrientationObservation,
    unrelabelVonBaeyerSystem_relabelVonBaeyerSystem, encodeAtom_decodeAtom]

/-- Relabelling a decoded bridge-orientation observation returns the supplied observation. -/
theorem
    relabelVonBaeyerBridgeOrientationObservation_unrelabelVonBaeyerBridgeOrientationObservation
    [DecidableEq V] (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerBridgeOrientationAuthorityObservation V) :
    relabelVonBaeyerBridgeOrientationObservation enumeration
        (unrelabelVonBaeyerBridgeOrientationObservation policy enumeration observation)
        (unrelabelVonBaeyerBridgeOrientationObservationBounded policy enumeration
          observation) = observation := by
  rcases observation with ⟨system, attachmentAtom, substituentSourceIndex, citation,
    attachment, descriptor⟩
  simp [relabelVonBaeyerBridgeOrientationObservation,
    unrelabelVonBaeyerBridgeOrientationObservation,
    relabelVonBaeyerSystem_unrelabelVonBaeyerSystem, decodeAtom_encodeAtom]

/-! ## Von Baeyer bridgehead-relative observation codec -/

/-- Relabel a bridgehead-relative observation.  Both ligands are explicit raw source references;
the citations, sides, descriptor, PIN flag and notation are copied literally. -/
def relabelVonBaeyerBridgeheadRelativeObservation [DecidableEq V]
    {policy : P93VonBaeyerAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy)
    (bounded : VonBaeyerBridgeheadRelativeBoundedIn n observation) :
    SuppliedVonBaeyerBridgeheadRelativeAuthorityObservation V where
  system := relabelVonBaeyerSystem enumeration observation.system bounded.system
  firstLigandSourceIndex := observation.firstLigand
  secondLigandSourceIndex := observation.secondLigand
  firstCitation? := observation.firstCitation?
  secondCitation? := observation.secondCitation?
  firstSide := observation.firstSide
  secondSide := observation.secondSide
  descriptor := observation.descriptor
  contextIsPIN := observation.contextIsPIN
  «notation» := observation.«notation»

/-- Decode a supplied bridgehead-relative observation at the given von Baeyer policy. -/
def unrelabelVonBaeyerBridgeheadRelativeObservation
    (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerBridgeheadRelativeAuthorityObservation V) :
    P93VonBaeyerBridgeheadRelativeAuthorityObservation policy where
  system := unrelabelVonBaeyerSystem enumeration observation.system
  firstLigand := observation.firstLigandSourceIndex
  secondLigand := observation.secondLigandSourceIndex
  firstCitation? := observation.firstCitation?
  secondCitation? := observation.secondCitation?
  firstSide := observation.firstSide
  secondSide := observation.secondSide
  descriptor := observation.descriptor
  contextIsPIN := observation.contextIsPIN
  «notation» := observation.«notation»

/-- Every decoded bridgehead-relative observation satisfies the explicit bounds.  The two ligands
are intentionally not bounded here. -/
def unrelabelVonBaeyerBridgeheadRelativeObservationBounded [DecidableEq V]
    (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerBridgeheadRelativeAuthorityObservation V) :
    VonBaeyerBridgeheadRelativeBoundedIn n
      (unrelabelVonBaeyerBridgeheadRelativeObservation policy enumeration observation) where
  system := unrelabelVonBaeyerSystemBounded enumeration observation.system

/-- Exact recovery of a bridgehead-relative observation, including both raw ligand indices. -/
theorem
    unrelabelVonBaeyerBridgeheadRelativeObservation_relabelVonBaeyerBridgeheadRelativeObservation
    [DecidableEq V] {policy : P93VonBaeyerAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy)
    (bounded : VonBaeyerBridgeheadRelativeBoundedIn n observation) :
    unrelabelVonBaeyerBridgeheadRelativeObservation policy enumeration
        (relabelVonBaeyerBridgeheadRelativeObservation enumeration observation bounded) =
      observation := by
  rcases observation with ⟨system, firstLigand, secondLigand, firstCitation,
    secondCitation, firstSide, secondSide, descriptor, contextIsPIN, notationValue⟩
  simp [relabelVonBaeyerBridgeheadRelativeObservation,
    unrelabelVonBaeyerBridgeheadRelativeObservation,
    unrelabelVonBaeyerSystem_relabelVonBaeyerSystem]

/-- Relabelling a decoded bridgehead-relative observation returns the supplied observation. -/
theorem
    relabelVonBaeyerBridgeheadRelativeObservation_unrelabelVonBaeyerBridgeheadRelativeObservation
    [DecidableEq V] (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerBridgeheadRelativeAuthorityObservation V) :
    relabelVonBaeyerBridgeheadRelativeObservation enumeration
        (unrelabelVonBaeyerBridgeheadRelativeObservation policy enumeration observation)
        (unrelabelVonBaeyerBridgeheadRelativeObservationBounded policy enumeration
          observation) = observation := by
  rcases observation with ⟨system, firstLigandSourceIndex, secondLigandSourceIndex,
    firstCitation, secondCitation, firstSide, secondSide, descriptor, contextIsPIN,
    notationValue⟩
  simp [relabelVonBaeyerBridgeheadRelativeObservation,
    unrelabelVonBaeyerBridgeheadRelativeObservation,
    relabelVonBaeyerSystem_unrelabelVonBaeyerSystem]

/-! ## Von Baeyer unsaturation observation codec -/

/-- Relabel an unsaturation observation.  The citation and the tagged specification (including
the `ordinaryDoubleBond`/`includedOpenCumulene` distinction) are copied literally. -/
def relabelVonBaeyerUnsaturationObservation [DecidableEq V]
    {policy : P93VonBaeyerAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93VonBaeyerUnsaturationAuthorityObservation policy)
    (bounded : VonBaeyerUnsaturationBoundedIn n observation) :
    SuppliedVonBaeyerUnsaturationAuthorityObservation V where
  system := relabelVonBaeyerSystem enumeration observation.system bounded.system
  unit := relabelUnit enumeration observation.unit bounded.unit
  citation := observation.citation
  specification := observation.specification

/-- Decode a supplied unsaturation observation at the given von Baeyer policy. -/
def unrelabelVonBaeyerUnsaturationObservation (policy : P93VonBaeyerAuthorityPolicy)
    (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerUnsaturationAuthorityObservation V) :
    P93VonBaeyerUnsaturationAuthorityObservation policy where
  system := unrelabelVonBaeyerSystem enumeration observation.system
  unit := unrelabelUnit enumeration observation.unit
  citation := observation.citation
  specification := observation.specification

/-- Every decoded unsaturation observation satisfies the explicit bounds. -/
def unrelabelVonBaeyerUnsaturationObservationBounded [DecidableEq V]
    (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerUnsaturationAuthorityObservation V) :
    VonBaeyerUnsaturationBoundedIn n
      (unrelabelVonBaeyerUnsaturationObservation policy enumeration observation) where
  system := unrelabelVonBaeyerSystemBounded enumeration observation.system
  unit := unrelabelUnitBounded enumeration observation.unit

/-- Exact recovery of an unsaturation observation. -/
theorem unrelabelVonBaeyerUnsaturationObservation_relabelVonBaeyerUnsaturationObservation
    [DecidableEq V] {policy : P93VonBaeyerAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93VonBaeyerUnsaturationAuthorityObservation policy)
    (bounded : VonBaeyerUnsaturationBoundedIn n observation) :
    unrelabelVonBaeyerUnsaturationObservation policy enumeration
        (relabelVonBaeyerUnsaturationObservation enumeration observation bounded) =
      observation := by
  rcases observation with ⟨system, unit, citation, specification⟩
  simp [relabelVonBaeyerUnsaturationObservation,
    unrelabelVonBaeyerUnsaturationObservation,
    unrelabelVonBaeyerSystem_relabelVonBaeyerSystem,
    unrelabelUnit_relabelUnit]

/-- Relabelling a decoded unsaturation observation returns the supplied observation. -/
theorem relabelVonBaeyerUnsaturationObservation_unrelabelVonBaeyerUnsaturationObservation
    [DecidableEq V] (policy : P93VonBaeyerAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SuppliedVonBaeyerUnsaturationAuthorityObservation V) :
    relabelVonBaeyerUnsaturationObservation enumeration
        (unrelabelVonBaeyerUnsaturationObservation policy enumeration observation)
        (unrelabelVonBaeyerUnsaturationObservationBounded policy enumeration observation) =
      observation := by
  rcases observation with ⟨system, unit, citation, specification⟩
  simp [relabelVonBaeyerUnsaturationObservation,
    unrelabelVonBaeyerUnsaturationObservation,
    relabelVonBaeyerSystem_unrelabelVonBaeyerSystem,
    relabelUnit_unrelabelUnit]

/-! ## Tagged sums over every existing authority observation -/

/-- The source-side tagged sum: exactly the six pre-existing authority observation records. -/
inductive SourceFusedVonBaeyerObservation (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy) where
  | fusedCIP (observation : P93FusedCIPAuthorityObservation fusedPolicy)
  | fusedRelation (observation : P93FusedRelationAuthorityObservation fusedPolicy)
  | vonBaeyerCenter (observation : P93VonBaeyerCenterAuthorityObservation vonBaeyerPolicy)
  | vonBaeyerBridgeOrientation
      (observation : P93VonBaeyerBridgeOrientationAuthorityObservation vonBaeyerPolicy)
  | vonBaeyerBridgeheadRelative
      (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation vonBaeyerPolicy)
  | vonBaeyerUnsaturation
      (observation : P93VonBaeyerUnsaturationAuthorityObservation vonBaeyerPolicy)

/-- The native tagged payload: exactly one of the six supplied observation shapes. -/
inductive SuppliedFusedVonBaeyerObservation (V : Type*)
    (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy) where
  | fusedCIP (observation : SuppliedFusedCIPAuthorityObservation V)
  | fusedRelation (observation : SuppliedFusedRelationAuthorityObservation V)
  | vonBaeyerCenter (observation : SuppliedVonBaeyerCenterAuthorityObservation V)
  | vonBaeyerBridgeOrientation
      (observation : SuppliedVonBaeyerBridgeOrientationAuthorityObservation V)
  | vonBaeyerBridgeheadRelative
      (observation : SuppliedVonBaeyerBridgeheadRelativeAuthorityObservation V)
  | vonBaeyerUnsaturation
      (observation : SuppliedVonBaeyerUnsaturationAuthorityObservation V)

/-- Explicit bounds for a tagged source observation.  Every branch is the bound predicate of the
corresponding pre-existing carrier record. -/
def SourceFusedVonBaeyerObservation.BoundedIn
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (n : ℕ) : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy → Prop
  | .fusedCIP observation => FusedCIPBoundedIn n observation
  | .fusedRelation observation => FusedRelationBoundedIn n observation
  | .vonBaeyerCenter observation => VonBaeyerCenterBoundedIn n observation
  | .vonBaeyerBridgeOrientation observation =>
      VonBaeyerBridgeOrientationBoundedIn n observation
  | .vonBaeyerBridgeheadRelative observation =>
      VonBaeyerBridgeheadRelativeBoundedIn n observation
  | .vonBaeyerUnsaturation observation => VonBaeyerUnsaturationBoundedIn n observation

/-! ## Tagged observation codec -/

/-- Relabel one tagged source observation.  Only atom references are reindexed; every other field
is passed through transparently. -/
def relabelObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy} :
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy) →
      observation.BoundedIn n →
        SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy
  | .fusedCIP observation, bounded =>
      .fusedCIP (relabelFusedCIPObservation enumeration observation bounded)
  | .fusedRelation observation, bounded =>
      .fusedRelation (relabelFusedRelationObservation enumeration observation bounded)
  | .vonBaeyerCenter observation, bounded =>
      .vonBaeyerCenter (relabelVonBaeyerCenterObservation enumeration observation bounded)
  | .vonBaeyerBridgeOrientation observation, bounded =>
      .vonBaeyerBridgeOrientation
        (relabelVonBaeyerBridgeOrientationObservation enumeration observation bounded)
  | .vonBaeyerBridgeheadRelative observation, bounded =>
      .vonBaeyerBridgeheadRelative
        (relabelVonBaeyerBridgeheadRelativeObservation enumeration observation bounded)
  | .vonBaeyerUnsaturation observation, bounded =>
      .vonBaeyerUnsaturation
        (relabelVonBaeyerUnsaturationObservation enumeration observation bounded)

/-- Decode one tagged native observation to the exact pre-existing carrier record. -/
def unrelabelObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy} :
    SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy →
      SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy
  | .fusedCIP observation =>
      .fusedCIP (unrelabelFusedCIPObservation fusedPolicy enumeration observation)
  | .fusedRelation observation =>
      .fusedRelation (unrelabelFusedRelationObservation fusedPolicy enumeration observation)
  | .vonBaeyerCenter observation =>
      .vonBaeyerCenter
        (unrelabelVonBaeyerCenterObservation vonBaeyerPolicy enumeration observation)
  | .vonBaeyerBridgeOrientation observation =>
      .vonBaeyerBridgeOrientation
        (unrelabelVonBaeyerBridgeOrientationObservation vonBaeyerPolicy enumeration
          observation)
  | .vonBaeyerBridgeheadRelative observation =>
      .vonBaeyerBridgeheadRelative
        (unrelabelVonBaeyerBridgeheadRelativeObservation vonBaeyerPolicy enumeration
          observation)
  | .vonBaeyerUnsaturation observation =>
      .vonBaeyerUnsaturation
        (unrelabelVonBaeyerUnsaturationObservation vonBaeyerPolicy enumeration observation)

/-- Bounds of a decoded tagged observation. -/
def unrelabelObservationBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy} :
    (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) →
      (unrelabelObservation enumeration observation).BoundedIn n
  | .fusedCIP observation =>
      unrelabelFusedCIPObservationBounded fusedPolicy enumeration observation
  | .fusedRelation observation =>
      unrelabelFusedRelationObservationBounded fusedPolicy enumeration observation
  | .vonBaeyerCenter observation =>
      unrelabelVonBaeyerCenterObservationBounded vonBaeyerPolicy enumeration observation
  | .vonBaeyerBridgeOrientation observation =>
      unrelabelVonBaeyerBridgeOrientationObservationBounded vonBaeyerPolicy enumeration
        observation
  | .vonBaeyerBridgeheadRelative observation =>
      unrelabelVonBaeyerBridgeheadRelativeObservationBounded vonBaeyerPolicy enumeration
        observation
  | .vonBaeyerUnsaturation observation =>
      unrelabelVonBaeyerUnsaturationObservationBounded vonBaeyerPolicy enumeration
        observation

/-- Exact recovery of every existing authority observation record.  This is the total
constructor-by-constructor claim: no observation shape is rejected or stored as an opaque
payload, and every field is recovered exactly. -/
theorem unrelabelObservation_relabelObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (bounded : observation.BoundedIn n) :
    unrelabelObservation enumeration (relabelObservation enumeration observation bounded) =
      observation := by
  cases observation with
  | fusedCIP observation =>
      rcases observation with ⟨system, unit, citation, descriptor⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelFusedCIPObservation_relabelFusedCIPObservation]
  | fusedRelation observation =>
      rcases observation with ⟨system, candidates, selected, selectedCitation,
        firstJunction, secondJunction, legacyDescriptor, preferredDescriptor⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelFusedRelationObservation_relabelFusedRelationObservation]
  | vonBaeyerCenter observation =>
      rcases observation with ⟨system, unit, citation, kind, descriptor, knowledge,
        notationValue⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelVonBaeyerCenterObservation_relabelVonBaeyerCenterObservation]
  | vonBaeyerBridgeOrientation observation =>
      rcases observation with ⟨system, attachmentAtom, substituent, citation,
        attachment, descriptor⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelVonBaeyerBridgeOrientationObservation_relabelVonBaeyerBridgeOrientationObservation]
  | vonBaeyerBridgeheadRelative observation =>
      rcases observation with ⟨system, firstLigand, secondLigand, firstCitation,
        secondCitation, firstSide, secondSide, descriptor, contextIsPIN, notationValue⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelVonBaeyerBridgeheadRelativeObservation_relabelVonBaeyerBridgeheadRelativeObservation]
  | vonBaeyerUnsaturation observation =>
      rcases observation with ⟨system, unit, citation, specification⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelVonBaeyerUnsaturationObservation_relabelVonBaeyerUnsaturationObservation]

/-- Relabelling a decoded tagged observation returns the supplied observation. -/
theorem relabelObservation_unrelabelObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) :
    relabelObservation enumeration (unrelabelObservation enumeration observation)
        (unrelabelObservationBounded enumeration observation) = observation := by
  cases observation with
  | fusedCIP observation =>
      rcases observation with ⟨system, unit, citation, descriptor⟩
      simp [relabelObservation, unrelabelObservation,
        relabelFusedCIPObservation_unrelabelFusedCIPObservation]
  | fusedRelation observation =>
      rcases observation with ⟨system, candidates, selected, selectedCitation,
        firstJunction, secondJunction, legacyDescriptor, preferredDescriptor⟩
      simp [relabelObservation, unrelabelObservation,
        relabelFusedRelationObservation_unrelabelFusedRelationObservation]
  | vonBaeyerCenter observation =>
      rcases observation with ⟨system, unit, citation, kind, descriptor, knowledge,
        notationValue⟩
      simp [relabelObservation, unrelabelObservation,
        relabelVonBaeyerCenterObservation_unrelabelVonBaeyerCenterObservation]
  | vonBaeyerBridgeOrientation observation =>
      rcases observation with ⟨system, attachmentAtom, substituentSourceIndex, citation,
        attachment, descriptor⟩
      simp [relabelObservation, unrelabelObservation,
        relabelVonBaeyerBridgeOrientationObservation_unrelabelVonBaeyerBridgeOrientationObservation]
  | vonBaeyerBridgeheadRelative observation =>
      rcases observation with ⟨system, firstLigandSourceIndex, secondLigandSourceIndex,
        firstCitation, secondCitation, firstSide, secondSide, descriptor, contextIsPIN,
        notationValue⟩
      simp [relabelObservation, unrelabelObservation,
        relabelVonBaeyerBridgeheadRelativeObservation_unrelabelVonBaeyerBridgeheadRelativeObservation]
  | vonBaeyerUnsaturation observation =>
      rcases observation with ⟨system, unit, citation, specification⟩
      simp [relabelObservation, unrelabelObservation,
        relabelVonBaeyerUnsaturationObservation_unrelabelVonBaeyerUnsaturationObservation]

/-! ## Existing validity predicates, consumed at the same source and policy -/

/-- The existing `ValidFor` of each pre-existing record, dispatched on the tag.  This is only a
dispatch: every branch is the record's own pre-existing predicate, at the same source and policy.
No new validity oracle and no renumbering-invariance claim is introduced. -/
def SourceFusedVonBaeyerObservation.ValidFor
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (source : AuthoritativeChemicalInput) :
    SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy → Prop
  | .fusedCIP observation =>
      P93FusedCIPAuthorityObservation.ValidFor fusedPolicy source observation
  | .fusedRelation observation =>
      P93FusedRelationAuthorityObservation.ValidFor fusedPolicy source observation
  | .vonBaeyerCenter observation =>
      P93VonBaeyerCenterAuthorityObservation.ValidFor vonBaeyerPolicy source observation
  | .vonBaeyerBridgeOrientation observation =>
      P93VonBaeyerBridgeOrientationAuthorityObservation.ValidFor vonBaeyerPolicy source
        observation
  | .vonBaeyerBridgeheadRelative observation =>
      P93VonBaeyerBridgeheadRelativeAuthorityObservation.ValidFor vonBaeyerPolicy source
        observation
  | .vonBaeyerUnsaturation observation =>
      P93VonBaeyerUnsaturationAuthorityObservation.ValidFor vonBaeyerPolicy source
        observation

/-- **Validity transport through the exact decode.**  For every tagged observation, the decoded
record's `ValidFor` at the same `source` and `policy` is equivalent to the original record's
`ValidFor`.  The equivalence is the record equality, not an invariance claim about renumbering. -/
theorem validFor_unrelabelObservation_relabelObservation_iff [DecidableEq V]
    (enumeration : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (bounded : observation.BoundedIn n) :
    (unrelabelObservation enumeration
        (relabelObservation enumeration observation bounded)).ValidFor source ↔
      observation.ValidFor source := by
  rw [unrelabelObservation_relabelObservation]

/-- Forward validity preservation at the same source and policy. -/
theorem validFor_of_relabelObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (bounded : observation.BoundedIn n)
    (valid : observation.ValidFor source) :
    (unrelabelObservation enumeration
        (relabelObservation enumeration observation bounded)).ValidFor source :=
  (validFor_unrelabelObservation_relabelObservation_iff enumeration source observation
    bounded).mpr valid

/-- Validity transport for a decoded native observation through a full native round trip. -/
theorem validFor_unrelabelObservation_roundtrip_iff [DecidableEq V]
    (enumeration : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observation : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) :
    (unrelabelObservation enumeration
        (relabelObservation enumeration (unrelabelObservation enumeration observation)
          (unrelabelObservationBounded enumeration observation))).ValidFor source ↔
      (unrelabelObservation enumeration observation).ValidFor source := by
  rw [relabelObservation_unrelabelObservation]

/-! ## Bounds derived from the actual carrier validity predicates -/

/-- Bounds of a fused authority system follow from its actual mechanical validity. -/
theorem fusedSystemBoundedIn_of_mechanicallyValidFor
    (source : AuthoritativeChemicalInput) (system : P93AuthorityFusedSystem)
    (valid : system.MechanicallyValidFor source) :
    FusedSystemBoundedIn source.molecule.atomCount system := by
  rcases valid with ⟨_length, _nodup, atomsBounded, _edgesNe, _edgesNodup,
    edgesValid, _locantsNe, _locantAtomsNodup, _locantLocantsNodup, locantAtoms,
    _coverage⟩
  refine ⟨atomsBounded, ?_, ?_⟩
  · intro edge member
    have edgeValid := edgesValid edge member
    exact ⟨atomsBounded edge.first edgeValid.2.1,
      atomsBounded edge.second edgeValid.2.2.1⟩
  · intro mapping member
    exact atomsBounded mapping.1 (locantAtoms mapping member)

/-- Bounds of a fused physical unit supported by a bounded fused system.  The polyhedron
constructor is excluded by `P93FusedPhysicalUnitSupported`, so no spatial hypothesis is needed. -/
theorem fusedPhysicalUnitBoundedIn_of_supported {n : ℕ}
    (system : P93AuthorityFusedSystem)
    (systemBounded : FusedSystemBoundedIn n system)
    (unit : P93AuthorityPhysicalUnit)
    (supported : P93FusedPhysicalUnitSupported system unit) :
    UnitBoundedIn n unit := by
  cases unit with
  | atomCenter center => exact systemBounded.atomsBounded center supported
  | bond first second =>
      exact ⟨systemBounded.atomsBounded first supported.1,
        systemBounded.atomsBounded second supported.2⟩
  | axis path =>
      exact fun atom member => systemBounded.atomsBounded atom
        (supported atom member)
  | plane members =>
      exact fun atom member => systemBounded.atomsBounded atom
        (supported atom member)
  | helix path =>
      exact fun atom member => systemBounded.atomsBounded atom
        (supported atom member)
  | polyhedron center positions => exact False.elim supported

/-- Bounds of a fused authority unit from its actual `ValidFor`. -/
theorem fusedUnitBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93FusedAuthorityPolicy)
    (system : P93AuthorityFusedSystem)
    (systemBounded : FusedSystemBoundedIn source.molecule.atomCount system)
    (unit : P93FusedAuthorityUnit)
    (valid : unit.ValidFor policy source system) :
    FusedUnitBoundedIn source.molecule.atomCount unit := by
  cases unit with
  | physical physicalUnit =>
      exact fusedPhysicalUnitBoundedIn_of_supported system systemBounded physicalUnit
        valid.2
  | fusedAxis path =>
      exact valid.2.2.1

/-- Bounds of a nearest fusion-pair candidate from its actual `ValidFor`.  Both fusion atoms are
atoms of a fusion edge, hence atoms of the bounded system. -/
theorem fusedCandidateBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93FusedAuthorityPolicy)
    (system : P93AuthorityFusedSystem)
    (systemBounded : FusedSystemBoundedIn source.molecule.atomCount system)
    (candidate : P93FusedNearestPairCandidate)
    (valid : candidate.ValidFor policy source system) :
    FusedCandidateBoundedIn source.molecule.atomCount candidate := by
  have fusionAtomBounded : ∀ atom, P93AuthorityFusionAtom system atom →
      atom < source.molecule.atomCount := by
    intro atom fusionAtom
    rcases fusionAtom with ⟨edge, member, firstOrSecond⟩
    rcases firstOrSecond with rfl | rfl
    · exact (systemBounded.edgesBounded edge member).1
    · exact (systemBounded.edgesBounded edge member).2
  exact ⟨fusionAtomBounded _ valid.2.1, fusionAtomBounded _ valid.2.2.1⟩

/-- Bounds of a fused CIP observation from its actual `ValidFor`. -/
theorem fusedCIPBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93FusedAuthorityPolicy)
    (observation : P93FusedCIPAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    FusedCIPBoundedIn source.molecule.atomCount observation := by
  have systemBounded := fusedSystemBoundedIn_of_mechanicallyValidFor source
    observation.system valid.1.1
  exact ⟨systemBounded, fusedUnitBoundedIn_of_validFor source policy
    observation.system systemBounded observation.unit valid.2.1⟩

/-- Bounds of a fused relation observation from its actual `ValidFor`. -/
theorem fusedRelationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93FusedAuthorityPolicy)
    (observation : P93FusedRelationAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    FusedRelationBoundedIn source.molecule.atomCount observation := by
  have systemBounded := fusedSystemBoundedIn_of_mechanicallyValidFor source
    observation.system valid.1.1
  refine ⟨systemBounded, ?_, ?_⟩
  · intro candidate member
    exact fusedCandidateBoundedIn_of_validFor source policy observation.system
      systemBounded candidate (valid.2.2.2.1 candidate member)
  · exact fusedCandidateBoundedIn_of_validFor source policy observation.system
      systemBounded observation.selected
      (valid.2.2.2.1 observation.selected valid.2.2.2.2.2.1.1)

/-- Bounds of a von Baeyer system follow from its actual mechanical validity. -/
theorem vonBaeyerSystemBoundedIn_of_mechanicallyValidFor
    (source : AuthoritativeChemicalInput) (system : P93AuthorityVonBaeyerSystem)
    (valid : system.MechanicallyValidFor source) :
    VonBaeyerSystemBoundedIn source.molecule.atomCount system := by
  rcases valid with ⟨_firstLt, _nodup, atomsBounded, _yPositive, _yx, _zy,
    _xPath, _yPath, _zPath⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact atomsBounded _ (by simp [P93AuthorityVonBaeyerSystem.atoms])
  · exact atomsBounded _ (by simp [P93AuthorityVonBaeyerSystem.atoms])
  · intro atom member
    exact atomsBounded atom (by simp [P93AuthorityVonBaeyerSystem.atoms, member])
  · intro atom member
    exact atomsBounded atom (by simp [P93AuthorityVonBaeyerSystem.atoms, member])
  · intro atom member
    exact atomsBounded atom (by simp [P93AuthorityVonBaeyerSystem.atoms, member])

/-- Bounds of a von Baeyer physical unit supported by a bounded system.  Plane, helix and
polyhedron are excluded by `P93VonBaeyerUnitSupported`, so no spatial hypothesis is needed. -/
theorem vonBaeyerPhysicalUnitBoundedIn_of_supported {n : ℕ}
    (system : P93AuthorityVonBaeyerSystem)
    (systemBounded : VonBaeyerSystemBoundedIn n system)
    (unit : P93AuthorityPhysicalUnit)
    (supported : P93VonBaeyerUnitSupported system unit) :
    UnitBoundedIn n unit := by
  cases unit with
  | atomCenter center =>
      exact VonBaeyerSystemBoundedIn.atomsBounded systemBounded center supported
  | bond first second =>
      exact ⟨VonBaeyerSystemBoundedIn.atomsBounded systemBounded first supported.1,
        VonBaeyerSystemBoundedIn.atomsBounded systemBounded second supported.2⟩
  | axis path =>
      exact fun atom member => VonBaeyerSystemBoundedIn.atomsBounded systemBounded
        atom (supported.2 atom member)
  | plane members => exact False.elim supported
  | helix path => exact False.elim supported
  | polyhedron center positions => exact False.elim supported

/-- Bounds of a von Baeyer center observation from its actual `ValidFor`. -/
theorem vonBaeyerCenterBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerCenterAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    VonBaeyerCenterBoundedIn source.molecule.atomCount observation := by
  have systemBounded := vonBaeyerSystemBoundedIn_of_mechanicallyValidFor source
    observation.system valid.1.1
  exact ⟨systemBounded, vonBaeyerPhysicalUnitBoundedIn_of_supported observation.system
    systemBounded observation.unit valid.2.2.1⟩

/-- Bounds of a bridge-orientation observation from its actual `ValidFor`.  The substituent is
not bounded by this predicate and is therefore not part of the bound record. -/
theorem vonBaeyerBridgeOrientationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    VonBaeyerBridgeOrientationBoundedIn source.molecule.atomCount observation := by
  have systemBounded := vonBaeyerSystemBoundedIn_of_mechanicallyValidFor source
    observation.system valid.1.1
  exact ⟨systemBounded, VonBaeyerSystemBoundedIn.atomsBounded systemBounded
    observation.attachmentAtom valid.2.2.1⟩

/-- Bounds of a bridgehead-relative observation from its actual `ValidFor`.  The two ligands are
not bounded by this predicate and are therefore not part of the bound record. -/
theorem vonBaeyerBridgeheadRelativeBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    VonBaeyerBridgeheadRelativeBoundedIn source.molecule.atomCount observation :=
  ⟨vonBaeyerSystemBoundedIn_of_mechanicallyValidFor source observation.system valid.1.1⟩

/-- Bounds of an unsaturation observation from its actual `ValidFor`. -/
theorem vonBaeyerUnsaturationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerUnsaturationAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    VonBaeyerUnsaturationBoundedIn source.molecule.atomCount observation := by
  have systemBounded := vonBaeyerSystemBoundedIn_of_mechanicallyValidFor source
    observation.system valid.1.1
  exact ⟨systemBounded, vonBaeyerPhysicalUnitBoundedIn_of_supported observation.system
    systemBounded observation.unit valid.2.2.1⟩

/-- Bounds derived from the actual `ValidFor` of a tagged source observation. -/
theorem SourceFusedVonBaeyerObservation.boundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (valid : observation.ValidFor source) :
    observation.BoundedIn source.molecule.atomCount := by
  cases observation with
  | fusedCIP observation =>
      exact fusedCIPBoundedIn_of_validFor source fusedPolicy observation valid
  | fusedRelation observation =>
      exact fusedRelationBoundedIn_of_validFor source fusedPolicy observation valid
  | vonBaeyerCenter observation =>
      exact vonBaeyerCenterBoundedIn_of_validFor source vonBaeyerPolicy observation valid
  | vonBaeyerBridgeOrientation observation =>
      exact vonBaeyerBridgeOrientationBoundedIn_of_validFor source vonBaeyerPolicy
        observation valid
  | vonBaeyerBridgeheadRelative observation =>
      exact vonBaeyerBridgeheadRelativeBoundedIn_of_validFor source vonBaeyerPolicy
        observation valid
  | vonBaeyerUnsaturation observation =>
      exact vonBaeyerUnsaturationBoundedIn_of_validFor source vonBaeyerPolicy observation
        valid

/-! ## Ordered heterogeneous lists -/

/-- Relabel an ordered heterogeneous list of source observations. -/
def relabelObservationList [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    List (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) :=
  observations.attach.map fun observation =>
    relabelObservation enumeration observation.1 (bounded observation.1 observation.2)

/-- Decode an ordered heterogeneous list of native observations. -/
def unrelabelObservationList [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)) :
    List (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy) :=
  observations.map (unrelabelObservation enumeration)

/-- Every decoded element of a heterogeneous list satisfies the same explicit bounds. -/
def unrelabelObservationListBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)) :
    ∀ observation ∈ unrelabelObservationList enumeration observations,
      observation.BoundedIn n := by
  intro observation member
  rw [unrelabelObservationList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelObservationBounded enumeration presented

@[simp] theorem relabelObservationList_length [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    (relabelObservationList enumeration observations bounded).length =
      observations.length := by
  simp [relabelObservationList]

@[simp] theorem unrelabelObservationList_length [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)) :
    (unrelabelObservationList enumeration observations).length = observations.length := by
  simp [unrelabelObservationList]

/-- Exact recovery of the ordered heterogeneous observation list, including order, multiplicity
and each concrete record shape. -/
theorem unrelabelObservationList_relabelObservationList [DecidableEq V]
    (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    unrelabelObservationList enumeration
        (relabelObservationList enumeration observations bounded) = observations := by
  unfold unrelabelObservationList relabelObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact unrelabelObservation_relabelObservation enumeration observation.1
      (bounded observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-- Relabelling a decoded heterogeneous list returns the supplied list. -/
theorem relabelObservationList_unrelabelObservationList [DecidableEq V]
    (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)) :
    relabelObservationList enumeration (unrelabelObservationList enumeration observations)
        (unrelabelObservationListBounded enumeration observations) = observations := by
  unfold relabelObservationList unrelabelObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelObservation_unrelabelObservation enumeration observation.1
  · exact List.attach_map_subtype_val observations

/-! ## Correlated sets of observations -/

/-- Image of a set of source observations under the exact codec. -/
def relabelObservationSet [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : Set (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    Set (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelObservation enumeration observation (bounded observation member) = presented

/-- Preimage of a set of native observations under the exact codec. -/
def unrelabelObservationSet [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : Set (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)) :
    Set (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy) :=
  fun recovered =>
    ∃ presented ∈ observations,
      unrelabelObservation enumeration presented = recovered

/-- Every decoded element of the image set satisfies the explicit bounds. -/
def unrelabelObservationSetBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : Set (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)) :
    ∀ observation ∈ unrelabelObservationSet enumeration observations,
      observation.BoundedIn n := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact unrelabelObservationBounded enumeration presented

/-- The correlated-set inverse on the source side. -/
theorem unrelabelObservationSet_relabelObservationSet [DecidableEq V]
    (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : Set (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    unrelabelObservationSet enumeration
        (relabelObservationSet enumeration observations bounded) = observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [unrelabelObservation_relabelObservation] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelObservation enumeration recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      unrelabelObservation_relabelObservation enumeration recovered
        (bounded recovered member)⟩

/-- The relabelling of an observation does not inspect the proof of its boundedness. -/
theorem relabelObservation_bound_irrel [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (first second : observation.BoundedIn n) :
    relabelObservation enumeration observation first =
      relabelObservation enumeration observation second := by
  cases observation <;> rfl

/-- Relabelling respects equality of the underlying source observation, independently of how the
two boundedness proofs were obtained. -/
theorem relabelObservation_congr [DecidableEq V] (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    {first second : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy}
    (h : first = second)
    (firstBounded : first.BoundedIn n) (secondBounded : second.BoundedIn n) :
    relabelObservation enumeration first firstBounded =
      relabelObservation enumeration second secondBounded := by
  cases h
  exact relabelObservation_bound_irrel enumeration _ firstBounded secondBounded

/-- The correlated-set inverse on the native side. -/
theorem relabelObservationSet_unrelabelObservationSet [DecidableEq V]
    (enumeration : V ≃ Fin n)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : Set (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)) :
    relabelObservationSet enumeration (unrelabelObservationSet enumeration observations)
        (unrelabelObservationSetBounded enumeration observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have obsEq : unrelabelObservation enumeration presented = observation := by
      have := congrArg (unrelabelObservation enumeration) relabelEq.symm
      rwa [unrelabelObservation_relabelObservation] at this
    have decodeEq' : unrelabelObservation enumeration presented₀ =
        unrelabelObservation enumeration presented := by
      rw [decodeEq, ← obsEq]
    have key : relabelObservation enumeration
        (unrelabelObservation enumeration presented₀)
        (unrelabelObservationBounded enumeration presented₀) = presented := by
      calc
        relabelObservation enumeration (unrelabelObservation enumeration presented₀)
            (unrelabelObservationBounded enumeration presented₀) =
          relabelObservation enumeration (unrelabelObservation enumeration presented)
            (unrelabelObservationBounded enumeration presented) :=
          relabelObservation_congr enumeration decodeEq' _ _
        _ = presented := relabelObservation_unrelabelObservation enumeration presented
    have presentedEq : presented = presented₀ := by
      rw [← key, relabelObservation_unrelabelObservation]
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨unrelabelObservation enumeration presented,
      ⟨presented, member, rfl⟩,
      relabelObservation_unrelabelObservation enumeration presented⟩

/-- **Correlated validity for a set.**  A native observation belongs to the image of a set exactly
when its decoded record is one of the source observations; consequently its `ValidFor` at the same
source and policy is exactly the validity of that source observation. -/
theorem validFor_mem_relabelObservationSet_iff [DecidableEq V] (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : Set (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (presented : SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)
    (member : presented ∈ relabelObservationSet enumeration observations bounded) :
    (unrelabelObservation enumeration presented).ValidFor source ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelObservation enumeration observation
            (bounded observation observationMember) = presented ∧
          observation.ValidFor source := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rwa [unrelabelObservation_relabelObservation] at valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rwa [unrelabelObservation_relabelObservation]

/-! ## Shared source context and the composable satellite -/

/-- The common source binding: the existing molecule-codec binding from
`OrganicStereoP93PhysicalFrameIngress`.  It ties a shared finite graph, coordinate channel and
diagram channel to the authoritative input by actual equalities. -/
abbrev FusedVonBaeyerSourceBinding (V : Type*) [DecidableEq V] [Fintype V] :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V

/-- Bounds of a tagged observation derived from its validity and the exact source binding. -/
theorem SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding
    [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (binding : FusedVonBaeyerSourceBinding V)
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (valid : observation.ValidFor binding.source) :
    observation.BoundedIn (Fintype.card V) := by
  have bounded := SourceFusedVonBaeyerObservation.boundedIn_of_validFor binding.source
    observation valid
  rwa [binding.atomCount_eq] at bounded

/-- A raw fused/von Baeyer observation source: the exact source binding plus an ordered list of
`Nat`-indexed carrier observations, each valid at the bound source. -/
structure RawFusedVonBaeyerObservationSource (V : Type*) [DecidableEq V] [Fintype V]
    (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy) where
  binding : FusedVonBaeyerSourceBinding V
  observations : List (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
  valid : ∀ observation ∈ observations, observation.ValidFor binding.source

/-- The composable native satellite.  It carries the same graph/spatial/diagram context as the
existing molecule codec and the ordered list of native observations.  No original observation and
no original `AuthoritativeChemicalInput` is stored here. -/
structure FusedVonBaeyerSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (SuppliedFusedVonBaeyerObservation V fusedPolicy vonBaeyerPolicy)

namespace FusedVonBaeyerSatellite

/-- The shared finite source, with observations intentionally excluded. -/
def toFiniteSource {V : Type*} [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (satellite : FusedVonBaeyerSatellite V fusedPolicy vonBaeyerPolicy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end FusedVonBaeyerSatellite

/-- Adapt a raw source into the satellite: keep the exact shared finite source and relabel every
observation, deriving the bounds from its actual `ValidFor` at the bound source. -/
def adapt [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (raw : RawFusedVonBaeyerObservationSource V fusedPolicy vonBaeyerPolicy) :
    FusedVonBaeyerSatellite V fusedPolicy vonBaeyerPolicy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelObservation raw.binding.enumeration observation.1
      (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding raw.binding
        observation.1 (raw.valid observation.1 observation.2))

@[simp] theorem adapt_graph [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (raw : RawFusedVonBaeyerObservationSource V fusedPolicy vonBaeyerPolicy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (raw : RawFusedVonBaeyerObservationSource V fusedPolicy vonBaeyerPolicy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (raw : RawFusedVonBaeyerObservationSource V fusedPolicy vonBaeyerPolicy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

/-- The recovered source record: the exact authoritative input and the decoded observation list. -/
@[ext] structure RecoveredFusedVonBaeyerObservationSource
    (fusedPolicy : P93FusedAuthorityPolicy)
    (vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; observations are decoded with the same enumeration. -/
def suppliedSource [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : FusedVonBaeyerSatellite V fusedPolicy vonBaeyerPolicy) :
    RecoveredFusedVonBaeyerObservationSource fusedPolicy vonBaeyerPolicy where
  source := satellite.toFiniteSource.encode enumeration
  observations := unrelabelObservationList enumeration satellite.observations

/-- **Exact full source recovery.**  Adapting a raw source and decoding it returns the exact
authoritative input (through the binding's actual source equality) and the exact ordered list of
pre-existing fused/von Baeyer observation records. -/
theorem suppliedSource_adapt [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (raw : RawFusedVonBaeyerObservationSource V fusedPolicy vonBaeyerPolicy) :
    suppliedSource raw.binding.enumeration (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredFusedVonBaeyerObservationSource.ext
  · exact raw.binding.encode_shared
  · change unrelabelObservationList raw.binding.enumeration (adapt raw).observations =
      raw.observations
    rw [show (adapt raw).observations = raw.observations.attach.map (fun observation =>
        relabelObservation raw.binding.enumeration observation.1
          (SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding raw.binding
            observation.1 (raw.valid observation.1 observation.2))) from rfl]
    exact unrelabelObservationList_relabelObservationList raw.binding.enumeration
      raw.observations (fun observation member =>
        SourceFusedVonBaeyerObservation.boundedIn_of_validFor_binding raw.binding
          observation (raw.valid observation member))

/-- Validity is preserved for the whole recovered list at the same source and policy. -/
theorem suppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (raw : RawFusedVonBaeyerObservationSource V fusedPolicy vonBaeyerPolicy)
    (observation : SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy)
    (member : observation ∈
      (suppliedSource raw.binding.enumeration (adapt raw)).observations) :
    observation.ValidFor raw.binding.source := by
  have listEq : (suppliedSource raw.binding.enumeration (adapt raw)).observations =
      raw.observations := by
    simpa using congrArg (RecoveredFusedVonBaeyerObservationSource.observations)
      (suppliedSource_adapt raw)
  have sourceMember : observation ∈ raw.observations := by
    rw [← listEq]
    exact member
  exact raw.valid observation sourceMember

/-! ## Concrete certified-source adapter -/

/-- The concrete binding of a certified authoritative input to its exact finite ingress source,
reusing the existing molecule codec's certified binding. -/
def certifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    FusedVonBaeyerSourceBinding (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

/-- Adapt a certified source together with an ordered list of valid carrier observations. -/
def adaptCertified (certified : CertifiedAuthoritativeChemicalInput)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    FusedVonBaeyerSatellite (Fin certified.input.molecule.atomCount)
      fusedPolicy vonBaeyerPolicy :=
  adapt { binding := certifiedBinding certified
          observations := observations
          valid := valid }

/-- **Concrete exact recovery from a certified source.** -/
theorem suppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    {fusedPolicy : P93FusedAuthorityPolicy} {vonBaeyerPolicy : P93VonBaeyerAuthorityPolicy}
    (observations : List (SourceFusedVonBaeyerObservation fusedPolicy vonBaeyerPolicy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified observations valid) =
      { source := certified.input, observations := observations } :=
  suppliedSource_adapt
    { binding := certifiedBinding certified
      observations := observations
      valid := valid }

/-! ## Honest bounds for the explicit raw source references

The three raw indices carried without a `BoundedIn` field (`substituent`, `firstLigand`,
`secondLigand`) are used in `P93AuthorityBinaryBond` hypotheses of the source `ValidFor`.  Under an
actual `PhysicalFrameSourceBinding` the bound source molecule is structurally well-formed, so
those indices are provably in range even though the observation predicate alone does not state it.
This section records that derivation; it does not add a restriction to the codec. -/

/-- The source molecule of a physical-frame binding is structurally well-formed: the binding's
graph equality and the exact encoder turn the finite graph's well-formedness into the stored
source's certificate. -/
theorem sourceMolecule_structurallyWellFormed [DecidableEq V] [Fintype V]
    (binding : FusedVonBaeyerSourceBinding V) :
    binding.source.molecule.StructurallyWellFormed := by
  have encoded := binding.shared.graph.encode_structurallyWellFormed binding.enumeration
  rwa [binding.graph_eq] at encoded

/-- Every stored interaction is well-formed at the source atom count. -/
theorem interaction_wellFormed_of_mem {source : AuthoritativeChemicalInput}
    (wellFormed : source.molecule.StructurallyWellFormed)
    {interaction : SemanticInteraction}
    (member : interaction ∈ source.molecule.interactions) :
    interaction.WellFormed source.molecule.atomCount :=
  (SemanticInteraction.wellFormed?_eq_true_iff _ _).mp
    (List.all_eq_true.mp wellFormed interaction member)

/-- Both participants of an actual binary bond are in range at the source atom count. -/
theorem binaryBond_atomCount {source : AuthoritativeChemicalInput}
    (wellFormed : source.molecule.StructurallyWellFormed)
    {left right : Nat} (bond : P93AuthorityBinaryBond source left right) :
    left < source.molecule.atomCount ∧ right < source.molecule.atomCount := by
  rcases bond with ⟨_distinct, interaction, member, _kind, ordered⟩
  rcases ordered with ordered | ordered
  · have interactionWellFormed := interaction_wellFormed_of_mem wellFormed member
    have leftMember : left ∈ interaction.participants := by
      rw [ordered]
      simp
    have rightMember : right ∈ interaction.participants := by
      rw [ordered]
      simp
    exact ⟨SemanticInteraction.WellFormed_participant_lt interactionWellFormed
        leftMember,
      SemanticInteraction.WellFormed_participant_lt interactionWellFormed rightMember⟩
  · have interactionWellFormed := interaction_wellFormed_of_mem wellFormed member
    have leftMember : left ∈ interaction.participants := by
      rw [ordered]
      simp
    have rightMember : right ∈ interaction.participants := by
      rw [ordered]
      simp
    exact ⟨SemanticInteraction.WellFormed_participant_lt interactionWellFormed
        leftMember,
      SemanticInteraction.WellFormed_participant_lt interactionWellFormed rightMember⟩

/-- The bridge-orientation substituent is a participant of an actual binary bond, so under a
source binding it is in range at the source atom count. -/
theorem bridgeOrientation_substituent_atomCount [DecidableEq V] [Fintype V]
    (binding : FusedVonBaeyerSourceBinding V)
    (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.substituent < binding.source.molecule.atomCount :=
  (binaryBond_atomCount (sourceMolecule_structurallyWellFormed binding)
    valid.2.2.2.2.1).2

/-- The bridge-orientation attachment atom is an atom of the bounded von Baeyer system. -/
theorem bridgeOrientation_attachmentAtom_atomCount [DecidableEq V] [Fintype V]
    (binding : FusedVonBaeyerSourceBinding V)
    (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.attachmentAtom < binding.source.molecule.atomCount :=
  VonBaeyerSystemBoundedIn.atomsBounded
    (vonBaeyerSystemBoundedIn_of_mechanicallyValidFor binding.source
      observation.system valid.1.1)
    observation.attachmentAtom valid.2.2.1

/-- The first bridgehead-relative ligand is a participant of an actual binary bond, so under a
source binding it is in range at the source atom count. -/
theorem bridgeheadRelative_firstLigand_atomCount [DecidableEq V] [Fintype V]
    (binding : FusedVonBaeyerSourceBinding V)
    (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.firstLigand < binding.source.molecule.atomCount :=
  (binaryBond_atomCount (sourceMolecule_structurallyWellFormed binding)
    valid.2.2.2.2.1).2

/-- The second bridgehead-relative ligand is a participant of an actual binary bond, so under a
source binding it is in range at the source atom count. -/
theorem bridgeheadRelative_secondLigand_atomCount [DecidableEq V] [Fintype V]
    (binding : FusedVonBaeyerSourceBinding V)
    (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.secondLigand < binding.source.molecule.atomCount :=
  (binaryBond_atomCount (sourceMolecule_structurallyWellFormed binding)
    valid.2.2.2.2.2.1).2

/-- The substituent is in range at the binding's own label arity. -/
theorem bridgeOrientation_substituent_card [DecidableEq V] [Fintype V]
    (binding : FusedVonBaeyerSourceBinding V)
    (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.substituent < Fintype.card V := by
  rw [← binding.atomCount_eq]
  exact bridgeOrientation_substituent_atomCount binding policy observation valid

/-- The first ligand is in range at the binding's own label arity. -/
theorem bridgeheadRelative_firstLigand_card [DecidableEq V] [Fintype V]
    (binding : FusedVonBaeyerSourceBinding V)
    (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.firstLigand < Fintype.card V := by
  rw [← binding.atomCount_eq]
  exact bridgeheadRelative_firstLigand_atomCount binding policy observation valid

/-- The second ligand is in range at the binding's own label arity. -/
theorem bridgeheadRelative_secondLigand_card [DecidableEq V] [Fintype V]
    (binding : FusedVonBaeyerSourceBinding V)
    (policy : P93VonBaeyerAuthorityPolicy)
    (observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.secondLigand < Fintype.card V := by
  rw [← binding.atomCount_eq]
  exact bridgeheadRelative_secondLigand_atomCount binding policy observation valid

end OrganicStereoFusedVonBaeyerIngress

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.unrelabelFusedSystem_relabelFusedSystem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.relabelFusedSystem_unrelabelFusedSystem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.unrelabelVonBaeyerSystem_relabelVonBaeyerSystem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.relabelVonBaeyerSystem_unrelabelVonBaeyerSystem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.unrelabelObservation_relabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.relabelObservation_unrelabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.validFor_unrelabelObservation_relabelObservation_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.unrelabelObservationList_relabelObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.unrelabelObservationSet_relabelObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.relabelObservationSet_unrelabelObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFusedVonBaeyerIngress.bridgeOrientation_substituent_atomCount
