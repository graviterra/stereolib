import TetraStereo.OneCenter.IUPACP93RingAssemblyAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# V-native ingress for the monocyclic and ring-assembly P-93 authority carriers

This module supplies the missing lossless codecs for the two cyclic P-93 carriers:

* `IUPACP93MonocyclicAuthorityCarrier` — `P93MonocyclicPhysicalUnit` (the closed ring plus a
  physical stereogenic unit), the general/center/cis-trans/RCT/unsaturation/double-bond/exocyclic
  observations;
* `IUPACP93RingAssemblyAuthorityCarrier` — `P93AuthorityRingAssembly` (the ordered ring list and
  the ordered junction list), the axial geometry records, and the axes/centers/double-bonds
  observations.

The existing generic codecs in `OrganicStereoSuppliedCitationIngress` and
`OrganicStereoP93PhysicalFrameIngress` have no representation for

* `P93MonocyclicPhysicalUnit.ringAtoms`;
* the cis/trans ring positions, substituents, plane observation and ring sides;
* the RCT ordered candidate list, the selected candidate, the reference side and the located
  assignments;
* `P93AuthorityRingAssembly.rings` and `.junctions`;
* the indexed axial geometry observation used by the ring-assembly axes row.

## What is relabelled and what is copied

Only genuine atom references are relabelled, with the accepted primitives `relabelList` /
`unrelabelList`, `relabelFinset` / `unrelabelFinset`, `relabelUnit` / `unrelabelUnit`,
`relabelSpatial` / `unrelabelSpatial` (the last pair is defined here for the optional coordinate
channel):

* `ringAtoms` and the assembly `rings` are ordered lists and preserve order and multiplicity;
* cis/trans ring positions and substituents, RCT positions and substituents, junction endpoint
  atoms, axial record endpoints and reference atoms, center atoms and double-bond endpoints are
  single atom references;
* the axes observation's `spatial` configuration is atom-indexed and is encoded as a total
  function `V → CartesianPoint3`, exactly the representation used by
  `OrganicFiniteSource.encodeSpatial?`.

Everything that is not an atom reference is copied literally and never relabelled:

* the **ring-list indices** `leftRingIndex`, `rightRingIndex` and `ringIndex` are positions in the
  ordered ring list, not atom indices, and remain `Nat` in both directions;
* citation components, prime counts and token keys;
* `RingPlaneObservation` (whose fields are propositions), `RingSide`, `CisTrans`, `RCTDescriptor`,
  `ConfigurationKnowledge`, `MonocycleNotation`, the descriptor vocabularies, the axial sense and
  the geometry-role Booleans;
* the raw `RawMolecule` syntax carried by the normalization result of the axes row.

The axes row stores `normalization.parsed` as explicit independent raw source syntax and
recomputes `normalization := normalizeRawMolecule parsed` in the decoder.  Under the source's own
`ValidFor` the carrier proves `normalization = normalizeRawMolecule normalization.parsed`, so the
source-side round trip is exact.  The native-side round trip additionally needs the explicit
hypothesis `parsed.normalizeUnspecifiedBonds = parsed`; it is *not* assumed away and is recorded as
`RingAssemblyObservation.RawSyntaxNormalized`.

## Bounds

Every codec takes an explicit bound predicate.  Where the source `ValidFor` already yields the
bound, this module proves it:

* ring atoms: `P93AuthorityClosedCycle` for the monocyclic row and
  `P93AuthorityRingAssembly.MechanicallyValidFor` for the assembly rows;
* physical units: `physicalUnitBoundedIn_of_validFor` (the polyhedral case uses the certified
  spatial-length fact);
* substituents and binary-bond endpoints: `P93AuthorityBinaryBond` plus the source's
  `SemanticMolecule.StructurallyWellFormed` certificate, via
  `SemanticInteraction.WellFormed_participant_lt`;
* junction endpoints, axial record atoms, center atoms and double-bond endpoints: ring membership
  from the assembly's mechanical validity.

Nothing is assumed about encoding being an inverse: both inverse directions are proved.  No
permutation invariance of any policy predicate is claimed; every validity statement is `ValidFor`
of the exact decoded record at the same source and policy.

## Observations

Each source record is mirrored field-for-field and the mirrors are combined into tagged sums with
one constructor per pre-existing record type.  The sums are handled constructor-by-constructor; no
observation is stored as an opaque payload and no branch rejects a shape.

The shared source context is the accepted `PhysicalFrameSourceBinding`: the graph, coordinate and
diagram channels are tied to the authoritative input by actual equalities, and atom-count
agreement is derived from `encode_atomCount`, never assumed.

## End-to-end and combined tag

Both carriers receive the same end-to-end treatment.  The monocyclic satellite
(`RawMonocyclicSource`, `MonocyclicObservationSatellite`, `adaptMonocyclic`,
`monocyclicSuppliedSource`) recovers the exact authoritative source, its graph/spatial/diagram
channels and the exact ordered observation list, with a concrete
`CertifiedAuthoritativeChemicalInput` adapter.

The eight monocyclic and three ring-assembly rows are then combined into one concrete
eleven-constructor tag (`SourceCyclicObservation` / `CyclicObservation`) whose codecs dispatch,
constructor by constructor, onto the accepted per-record codecs.  The combined satellite
(`RawCyclicSource`, `CyclicObservationSatellite`, `adaptCyclic`, `cyclicSuppliedSource`) uses one
shared source binding and proves the exact whole-source/whole-ordered-list inverse; the lists
and arbitrary correlated `Set`s have both inverse directions, and the set membership validity
statement is `validFor_mem_relabelCyclicObservationSet_iff`.  The axes normalization equality is
derived from the carrier's axes `ValidFor` on the satellite path, while the native-side raw
normalization restriction is an explicit hypothesis of the native round trip only.
-/

namespace OrganicStereoMonocyclicRingAssemblyIngress

open BlueBookP93
open BlueBookP93.Cyclic
open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress

noncomputable section

variable {V : Type*} {n : ℕ} {policy : P93RingAssemblyAuthorityPolicy}

/-! ## Shared list bounds and the spatial channel -/

/-- An explicit bound predicate on an ordered list of raw atom indices. -/
def listBoundedIn (n : ℕ) (values : List Nat) : Prop :=
  ∀ value ∈ values, value < n

/-- Explicit bound predicate on a physical unit, re-exported under a name that cannot be confused
with the tagged-observation bound. -/
abbrev UnitBoundedIn (n : ℕ) (unit : P93AuthorityPhysicalUnit) : Prop :=
  TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
    n unit

/-- Recover a list from a function over an index type of the same length.  This is the
length-cast form of `List.ofFn_get` used for the coordinate list. -/
private theorem ofFn_eq_list_of_get {α : Type*} {m : ℕ} {l : List α} (hlen : m = l.length)
    (f : Fin m → α)
    (h : ∀ index : Fin m, f index = l.get (Fin.cast hlen index)) :
    List.ofFn f = l := by
  rw [List.ofFn_congr hlen]
  have hfun : (fun index : Fin l.length => f (Fin.cast hlen.symm index)) =
      (fun index : Fin l.length => l.get index) := by
    funext index
    have hcast : Fin.cast hlen (Fin.cast hlen.symm index) = index := Fin.ext rfl
    rw [← hcast]
    exact h (Fin.cast hlen.symm index)
  rw [hfun]
  exact List.ofFn_get l

/-- Encode a stored coordinate list as a total function on the atom labels. -/
def relabelSpatial (enumeration : V ≃ Fin n) (spatial : SpatialConfiguration)
    (fits : spatial.positions.length = n) : V → CartesianPoint3 :=
  fun atom => spatial.positions.get (Fin.cast fits.symm (enumeration atom))

/-- Decode a total coordinate function into the stored coordinate list.  This is exactly the
list produced by `OrganicFiniteSource.encodeSpatial?` for a present channel. -/
def unrelabelSpatial (enumeration : V ≃ Fin n) (spatial : V → CartesianPoint3) :
    SpatialConfiguration :=
  { positions := List.ofFn fun index : Fin n => spatial (enumeration.symm index) }

/-- The coordinate list is exactly recovered, including order and every rational coordinate. -/
theorem unrelabelSpatial_relabelSpatial (enumeration : V ≃ Fin n)
    (spatial : SpatialConfiguration) (fits : spatial.positions.length = n) :
    unrelabelSpatial enumeration (relabelSpatial enumeration spatial fits) = spatial := by
  obtain ⟨positions⟩ := spatial
  simp only [unrelabelSpatial, relabelSpatial, Equiv.apply_symm_apply]
  apply congrArg SpatialConfiguration.mk
  trans List.ofFn (fun index : Fin positions.length =>
      positions.get (Fin.cast fits.symm (Fin.cast fits index)))
  · exact List.ofFn_congr (h := fits.symm)
      (f := fun index : Fin n => positions.get (Fin.cast fits.symm index))
  · rw [show (fun index : Fin positions.length =>
        positions.get (Fin.cast fits.symm (Fin.cast fits index))) =
        (fun index : Fin positions.length => positions.get index) from by
      funext index
      exact congrArg positions.get (Fin.ext rfl)]
    exact List.ofFn_get positions

/-- Encoding a decoded coordinate function returns the function. -/
theorem relabelSpatial_unrelabelSpatial (enumeration : V ≃ Fin n)
    (spatial : V → CartesianPoint3) :
    relabelSpatial enumeration (unrelabelSpatial enumeration spatial)
      (by simp [unrelabelSpatial]) = spatial := by
  funext atom
  simp only [relabelSpatial, unrelabelSpatial, List.get_ofFn]
  rw [← Equiv.symm_apply_apply enumeration atom]
  simp only [Equiv.apply_symm_apply]
  exact congrArg (fun index : Fin n => spatial (enumeration.symm index)) (Fin.ext rfl)

/-! ## Bounds from the actual physical-unit source predicate -/

/-- Bounds of a physical unit follow from its actual `ValidFor` at the source's own atom count.
The polyhedral case uses the certified spatial-length fact, supplied by the source binding, and
actual coordinate incidence; nothing is assumed. -/
theorem physicalUnitBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (observationPolicy : P93AuthorityPhysicalObservationPolicy)
    (unit : P93AuthorityPhysicalUnit)
    (valid : unit.ValidFor observationPolicy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    UnitBoundedIn source.molecule.atomCount unit := by
  cases unit with
  | atomCenter center =>
      simpa [UnitBoundedIn] using valid.1
  | bond first second =>
      exact ⟨valid.1, valid.2.1⟩
  | axis path =>
      simpa [UnitBoundedIn, P93AuthorityAtomsBounded] using valid.2.1
  | plane members =>
      rcases valid with ⟨frame, frameValid, _observationPolicy⟩
      rcases frameValid with ⟨setEq, _length, _nodup, bounded, _rest⟩
      intro atom member
      have setMember : atom ∈ frame.record.planeAtoms.toFinset := by
        rwa [setEq]
      have listMember : atom ∈ frame.record.planeAtoms :=
        List.mem_toFinset.mp setMember
      exact bounded atom (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ listMember)))))
  | helix path =>
      rcases valid with ⟨frame, frameValid, _observationPolicy⟩
      rcases frameValid with ⟨_pathEq, _descriptor, _length, bounded, _rest⟩
      intro atom member
      exact bounded atom (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  | polyhedron center positions =>
      rcases valid with ⟨geometry, frame, frameValid, _observationPolicy⟩
      have bounded :=
        OrganicStereoP93PhysicalFrameIngress.polyhedralFrameBoundedIn_of_validFor
          source center positions geometry frame frameValid spatialWellFormed
      refine ⟨?_, ?_⟩
      · simpa [frameValid.1] using bounded.centerBound
      · intro atom member
        have setMember : atom ∈ frame.record.ligands.toFinset := by
          rwa [frameValid.2.1]
        exact bounded.ligandsBound atom (List.mem_toFinset.mp setMember)

/-- Every interaction stored in a structurally well-formed molecule is well formed. -/
theorem interactionWellFormed_of_mem
    (source : AuthoritativeChemicalInput)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed)
    {interaction : SemanticInteraction}
    (member : interaction ∈ source.molecule.interactions) :
    interaction.WellFormed source.molecule.atomCount := by
  have hall : source.molecule.interactions.all
      (fun interaction => interaction.wellFormed? source.molecule.atomCount) = true :=
    structurallyWellFormed
  exact (SemanticInteraction.wellFormed?_eq_true_iff interaction
    source.molecule.atomCount).mp (List.all_eq_true.mp hall interaction member)

/-- Both endpoints of a genuine binary bond are in range of the source atom count.  This is
derived from the source's structural certificate, not assumed. -/
theorem binaryBond_atoms_bounded
    (source : AuthoritativeChemicalInput)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed)
    {left right : Nat} (bond : P93AuthorityBinaryBond source left right) :
    left < source.molecule.atomCount ∧ right < source.molecule.atomCount := by
  rcases bond with ⟨_distinct, interaction, interactionMember, _kind, participantsEq⟩
  have wellFormed :=
    interactionWellFormed_of_mem source structurallyWellFormed interactionMember
  have bound : ∀ atom ∈ interaction.participants, atom < source.molecule.atomCount :=
    fun atom member => SemanticInteraction.WellFormed_participant_lt wellFormed member
  rcases participantsEq with participantsEq | participantsEq
  · rw [participantsEq] at bound
    exact ⟨bound left (by simp), bound right (by simp)⟩
  · rw [participantsEq] at bound
    exact ⟨bound left (by simp), bound right (by simp)⟩

/-! ## The monocyclic physical unit -/

/-- The closed ring together with a physical stereogenic unit.  `ringAtoms` is an ordered cycle
traversal; the unit retains all six physical constructors. -/
structure SuppliedMonocyclicPhysicalUnit (V : Type*) where
  ringAtoms : List V
  unit : SuppliedPhysicalUnit V

/-- Explicit bounds for a monocyclic physical unit. -/
def monocyclicPhysicalUnitBoundedIn (n : ℕ) (observation : P93MonocyclicPhysicalUnit) : Prop :=
  (∀ atom ∈ observation.ringAtoms, atom < n) ∧ UnitBoundedIn n observation.unit

/-- Relabel a bounded monocyclic physical unit. -/
def relabelMonocyclicPhysicalUnit [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : P93MonocyclicPhysicalUnit)
    (bounded : monocyclicPhysicalUnitBoundedIn n observation) :
    SuppliedMonocyclicPhysicalUnit V where
  ringAtoms := relabelList enumeration observation.ringAtoms bounded.1
  unit := relabelUnit enumeration observation.unit bounded.2

/-- Decode a monocyclic physical unit to the raw carrier record. -/
def unrelabelMonocyclicPhysicalUnit (enumeration : V ≃ Fin n)
    (observation : SuppliedMonocyclicPhysicalUnit V) : P93MonocyclicPhysicalUnit where
  ringAtoms := unrelabelList enumeration observation.ringAtoms
  unit := unrelabelUnit enumeration observation.unit

/-- Exact recovery of the monocyclic physical unit, including the ordered ring traversal and the
full physical-unit constructor. -/
theorem unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit [DecidableEq V]
    (enumeration : V ≃ Fin n) (observation : P93MonocyclicPhysicalUnit)
    (bounded : monocyclicPhysicalUnitBoundedIn n observation) :
    unrelabelMonocyclicPhysicalUnit enumeration
        (relabelMonocyclicPhysicalUnit enumeration observation bounded) = observation := by
  rcases observation with ⟨ringAtoms, unit⟩
  simp [unrelabelMonocyclicPhysicalUnit, relabelMonocyclicPhysicalUnit,
    unrelabelList_relabelList, unrelabelUnit_relabelUnit]

/-- Relabelling a decoded monocyclic physical unit returns the supplied record. -/
theorem relabelMonocyclicPhysicalUnit_unrelabelMonocyclicPhysicalUnit [DecidableEq V]
    (enumeration : V ≃ Fin n) (observation : SuppliedMonocyclicPhysicalUnit V) :
    relabelMonocyclicPhysicalUnit enumeration
        (unrelabelMonocyclicPhysicalUnit enumeration observation)
        ⟨unrelabelList_bounded enumeration observation.ringAtoms,
          unrelabelUnitBounded enumeration observation.unit⟩ = observation := by
  rcases observation with ⟨ringAtoms, unit⟩
  simp [unrelabelMonocyclicPhysicalUnit, relabelMonocyclicPhysicalUnit,
    relabelList_unrelabelList, relabelUnit_unrelabelUnit]

/-! ## The monocyclic general assignment -/

/-- Mirror of `P93MonocyclicGeneralAssignment`: the physical unit is relabelled, the citation,
general descriptor, configuration knowledge and notation are copied literally. -/
structure SuppliedMonocyclicGeneralAssignment (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : SuppliedMonocyclicPhysicalUnit V
  citation : P93AuthorityCitationToken
  descriptor : policy.GeneralDescriptor
  knowledge : ConfigurationKnowledge
  «notation» : MonocycleNotation

/-- Explicit bounds for a general assignment: only its physical unit carries atom references. -/
def monocyclicGeneralAssignmentBoundedIn (n : ℕ)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicGeneralAssignment policy) : Prop :=
  monocyclicPhysicalUnitBoundedIn n observation.physical

/-- Relabel the physical unit of a general assignment. -/
def relabelMonocyclicGeneralAssignment [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicGeneralAssignment policy)
    (bounded : monocyclicGeneralAssignmentBoundedIn n policy observation) :
    SuppliedMonocyclicGeneralAssignment V policy where
  physical := relabelMonocyclicPhysicalUnit enumeration observation.physical bounded
  citation := observation.citation
  descriptor := observation.descriptor
  knowledge := observation.knowledge
  «notation» := observation.notation

/-- Decode a general assignment to the raw carrier record. -/
def unrelabelMonocyclicGeneralAssignment (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicGeneralAssignment V policy) :
    P93MonocyclicGeneralAssignment policy where
  physical := unrelabelMonocyclicPhysicalUnit enumeration observation.physical
  citation := observation.citation
  descriptor := observation.descriptor
  knowledge := observation.knowledge
  «notation» := observation.notation

/-- Exact recovery of a general assignment. -/
theorem unrelabelMonocyclicGeneralAssignment_relabelMonocyclicGeneralAssignment
    [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicGeneralAssignment policy)
    (bounded : monocyclicGeneralAssignmentBoundedIn n policy observation) :
    unrelabelMonocyclicGeneralAssignment enumeration policy
        (relabelMonocyclicGeneralAssignment enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨physical, citation, descriptor, knowledge, notationValue⟩
  simp [unrelabelMonocyclicGeneralAssignment, relabelMonocyclicGeneralAssignment,
    unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]

/-- Relabelling a decoded general assignment returns the supplied record. -/
theorem relabelMonocyclicGeneralAssignment_unrelabelMonocyclicGeneralAssignment
    [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicGeneralAssignment V policy) :
    relabelMonocyclicGeneralAssignment enumeration policy
        (unrelabelMonocyclicGeneralAssignment enumeration policy observation)
        ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
          unrelabelUnitBounded enumeration observation.physical.unit⟩ = observation := by
  rcases observation with ⟨physical, citation, descriptor, knowledge, notationValue⟩
  rcases physical with ⟨ringAtoms, unit⟩
  simp [unrelabelMonocyclicGeneralAssignment, relabelMonocyclicGeneralAssignment,
    unrelabelMonocyclicPhysicalUnit, relabelMonocyclicPhysicalUnit,
    relabelList_unrelabelList, relabelUnit_unrelabelUnit]

/-! ## The monocyclic center observation -/

/-- Mirror of `P93MonocyclicCenterAuthorityObservation`. -/
structure SuppliedMonocyclicCenterAuthorityObservation (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : SuppliedMonocyclicPhysicalUnit V
  citation : P93AuthorityCitationToken
  kind : BlueBookP93.Acyclic.UnitKind
  descriptor : BlueBookP93.Acyclic.Descriptor
  knowledge : ConfigurationKnowledge
  «notation» : MonocycleNotation

/-- Explicit bounds for a center observation. -/
def monocyclicCenterObservationBoundedIn (n : ℕ)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicCenterAuthorityObservation policy) : Prop :=
  monocyclicPhysicalUnitBoundedIn n observation.physical

/-- Relabel the physical unit of a center observation. -/
def relabelMonocyclicCenterAuthorityObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicCenterAuthorityObservation policy)
    (bounded : monocyclicCenterObservationBoundedIn n policy observation) :
    SuppliedMonocyclicCenterAuthorityObservation V policy where
  physical := relabelMonocyclicPhysicalUnit enumeration observation.physical bounded
  citation := observation.citation
  kind := observation.kind
  descriptor := observation.descriptor
  knowledge := observation.knowledge
  «notation» := observation.notation

/-- Decode a center observation to the raw carrier record. -/
def unrelabelMonocyclicCenterAuthorityObservation (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicCenterAuthorityObservation V policy) :
    P93MonocyclicCenterAuthorityObservation policy where
  physical := unrelabelMonocyclicPhysicalUnit enumeration observation.physical
  citation := observation.citation
  kind := observation.kind
  descriptor := observation.descriptor
  knowledge := observation.knowledge
  «notation» := observation.notation

/-- Exact recovery of a center observation, including the center kind and descriptor. -/
theorem unrelabelMonocyclicCenterAuthorityObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicCenterAuthorityObservation policy)
    (bounded : monocyclicCenterObservationBoundedIn n policy observation) :
    unrelabelMonocyclicCenterAuthorityObservation enumeration policy
        (relabelMonocyclicCenterAuthorityObservation enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨physical, citation, kind, descriptor, knowledge, notationValue⟩
  simp [unrelabelMonocyclicCenterAuthorityObservation,
    relabelMonocyclicCenterAuthorityObservation,
    unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]

/-- Relabelling a decoded center observation returns the supplied record. -/
theorem relabelMonocyclicCenterAuthorityObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicCenterAuthorityObservation V policy) :
    relabelMonocyclicCenterAuthorityObservation enumeration policy
        (unrelabelMonocyclicCenterAuthorityObservation enumeration policy observation)
        ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
          unrelabelUnitBounded enumeration observation.physical.unit⟩ = observation := by
  rcases observation with ⟨physical, citation, kind, descriptor, knowledge, notationValue⟩
  rcases physical with ⟨ringAtoms, unit⟩
  simp [unrelabelMonocyclicCenterAuthorityObservation,
    relabelMonocyclicCenterAuthorityObservation,
    unrelabelMonocyclicPhysicalUnit, relabelMonocyclicPhysicalUnit,
    relabelList_unrelabelList, relabelUnit_unrelabelUnit]

/-! ## The monocyclic cis/trans observation -/

/-- Mirror of `P93MonocyclicCisTransAuthorityObservation`.  The mean-plane observation (whose
fields are propositions), the two ring sides and the relative descriptor are copied literally. -/
structure SuppliedMonocyclicCisTransAuthorityObservation (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  ringAtoms : List V
  firstRingPosition : V
  secondRingPosition : V
  firstSubstituent : V
  secondSubstituent : V
  plane : RingPlaneObservation
  firstSide : RingSide
  secondSide : RingSide
  descriptor : CisTrans

/-- Explicit bounds for a cis/trans observation: the ring traversal and the four atom positions. -/
def cisTransObservationBoundedIn (n : ℕ)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicCisTransAuthorityObservation policy) : Prop :=
  (∀ atom ∈ observation.ringAtoms, atom < n) ∧
    observation.firstRingPosition < n ∧ observation.secondRingPosition < n ∧
      observation.firstSubstituent < n ∧ observation.secondSubstituent < n

/-- Relabel a bounded cis/trans observation. -/
def relabelMonocyclicCisTransAuthorityObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicCisTransAuthorityObservation policy)
    (bounded : cisTransObservationBoundedIn n policy observation) :
    SuppliedMonocyclicCisTransAuthorityObservation V policy where
  ringAtoms := relabelList enumeration observation.ringAtoms bounded.1
  firstRingPosition := decodeAtom enumeration observation.firstRingPosition bounded.2.1
  secondRingPosition := decodeAtom enumeration observation.secondRingPosition bounded.2.2.1
  firstSubstituent := decodeAtom enumeration observation.firstSubstituent bounded.2.2.2.1
  secondSubstituent := decodeAtom enumeration observation.secondSubstituent bounded.2.2.2.2
  plane := observation.plane
  firstSide := observation.firstSide
  secondSide := observation.secondSide
  descriptor := observation.descriptor

/-- Decode a cis/trans observation to the raw carrier record. -/
def unrelabelMonocyclicCisTransAuthorityObservation (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicCisTransAuthorityObservation V policy) :
    P93MonocyclicCisTransAuthorityObservation policy where
  ringAtoms := unrelabelList enumeration observation.ringAtoms
  firstRingPosition := encodeAtom enumeration observation.firstRingPosition
  secondRingPosition := encodeAtom enumeration observation.secondRingPosition
  firstSubstituent := encodeAtom enumeration observation.firstSubstituent
  secondSubstituent := encodeAtom enumeration observation.secondSubstituent
  plane := observation.plane
  firstSide := observation.firstSide
  secondSide := observation.secondSide
  descriptor := observation.descriptor

/-- Exact recovery of a cis/trans observation, including the plane observation and both sides. -/
theorem unrelabelMonocyclicCisTransAuthorityObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicCisTransAuthorityObservation policy)
    (bounded : cisTransObservationBoundedIn n policy observation) :
    unrelabelMonocyclicCisTransAuthorityObservation enumeration policy
        (relabelMonocyclicCisTransAuthorityObservation enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨ringAtoms, firstRingPosition, secondRingPosition,
    firstSubstituent, secondSubstituent, plane, firstSide, secondSide, descriptor⟩
  simp [unrelabelMonocyclicCisTransAuthorityObservation,
    relabelMonocyclicCisTransAuthorityObservation,
    unrelabelList_relabelList, encodeAtom_decodeAtom]

/-- Relabelling a decoded cis/trans observation returns the supplied record. -/
theorem relabelMonocyclicCisTransAuthorityObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicCisTransAuthorityObservation V policy) :
    relabelMonocyclicCisTransAuthorityObservation enumeration policy
        (unrelabelMonocyclicCisTransAuthorityObservation enumeration policy observation)
        ⟨unrelabelList_bounded enumeration observation.ringAtoms,
          encodeAtom_lt enumeration observation.firstRingPosition,
          encodeAtom_lt enumeration observation.secondRingPosition,
          encodeAtom_lt enumeration observation.firstSubstituent,
          encodeAtom_lt enumeration observation.secondSubstituent⟩ = observation := by
  rcases observation with ⟨ringAtoms, firstRingPosition, secondRingPosition,
    firstSubstituent, secondSubstituent, plane, firstSide, secondSide, descriptor⟩
  simp [unrelabelMonocyclicCisTransAuthorityObservation,
    relabelMonocyclicCisTransAuthorityObservation,
    relabelList_unrelabelList, decodeAtom_encodeAtom]

/-! ## The monocyclic RCT observation -/

/-- Mirror of `P93MonocyclicRCTReferenceCandidate`: the two atom references are relabelled, the
citation, suffix flag and sequence priority are copied literally. -/
structure SuppliedMonocyclicRCTReferenceCandidate (V : Type*) where
  ringPosition : V
  substituent : V
  citation : P93AuthorityCitationToken
  namedAsSuffix : Bool
  sequencePriority : Nat

/-- Explicit bounds for one RCT reference candidate. -/
def rctCandidateBoundedIn (n : ℕ)
    (candidate : P93MonocyclicRCTReferenceCandidate) : Prop :=
  candidate.ringPosition < n ∧ candidate.substituent < n

/-- Relabel one bounded RCT reference candidate. -/
def relabelMonocyclicRCTReferenceCandidate [DecidableEq V] (enumeration : V ≃ Fin n)
    (candidate : P93MonocyclicRCTReferenceCandidate)
    (bounded : rctCandidateBoundedIn n candidate) :
    SuppliedMonocyclicRCTReferenceCandidate V where
  ringPosition := decodeAtom enumeration candidate.ringPosition bounded.1
  substituent := decodeAtom enumeration candidate.substituent bounded.2
  citation := candidate.citation
  namedAsSuffix := candidate.namedAsSuffix
  sequencePriority := candidate.sequencePriority

/-- Decode one RCT reference candidate to the raw carrier record. -/
def unrelabelMonocyclicRCTReferenceCandidate (enumeration : V ≃ Fin n)
    (candidate : SuppliedMonocyclicRCTReferenceCandidate V) :
    P93MonocyclicRCTReferenceCandidate where
  ringPosition := encodeAtom enumeration candidate.ringPosition
  substituent := encodeAtom enumeration candidate.substituent
  citation := candidate.citation
  namedAsSuffix := candidate.namedAsSuffix
  sequencePriority := candidate.sequencePriority

/-- Exact recovery of one RCT reference candidate. -/
theorem unrelabelMonocyclicRCTReferenceCandidate_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (candidate : P93MonocyclicRCTReferenceCandidate)
    (bounded : rctCandidateBoundedIn n candidate) :
    unrelabelMonocyclicRCTReferenceCandidate enumeration
        (relabelMonocyclicRCTReferenceCandidate enumeration candidate bounded) = candidate := by
  rcases candidate with ⟨ringPosition, substituent, citation, namedAsSuffix, sequencePriority⟩
  simp [unrelabelMonocyclicRCTReferenceCandidate,
    relabelMonocyclicRCTReferenceCandidate, encodeAtom_decodeAtom]

/-- Relabelling a decoded RCT reference candidate returns the supplied record. -/
theorem relabelMonocyclicRCTReferenceCandidate_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (candidate : SuppliedMonocyclicRCTReferenceCandidate V) :
    relabelMonocyclicRCTReferenceCandidate enumeration
        (unrelabelMonocyclicRCTReferenceCandidate enumeration candidate)
        ⟨encodeAtom_lt enumeration candidate.ringPosition,
          encodeAtom_lt enumeration candidate.substituent⟩ = candidate := by
  rcases candidate with ⟨ringPosition, substituent, citation, namedAsSuffix, sequencePriority⟩
  simp [unrelabelMonocyclicRCTReferenceCandidate,
    relabelMonocyclicRCTReferenceCandidate, decodeAtom_encodeAtom]

/-- Relabel an ordered list of bounded RCT reference candidates, preserving order and
multiplicity. -/
def relabelMonocyclicRCTCandidates [DecidableEq V] (enumeration : V ≃ Fin n)
    (candidates : List P93MonocyclicRCTReferenceCandidate)
    (bounded : ∀ candidate ∈ candidates, rctCandidateBoundedIn n candidate) :
    List (SuppliedMonocyclicRCTReferenceCandidate V) :=
  candidates.attach.map fun candidate =>
    relabelMonocyclicRCTReferenceCandidate enumeration candidate.1
      (bounded candidate.1 candidate.2)

/-- Decode an ordered list of RCT reference candidates. -/
def unrelabelMonocyclicRCTCandidates (enumeration : V ≃ Fin n)
    (candidates : List (SuppliedMonocyclicRCTReferenceCandidate V)) :
    List P93MonocyclicRCTReferenceCandidate :=
  candidates.map (unrelabelMonocyclicRCTReferenceCandidate enumeration)

/-- Every decoded candidate satisfies the same explicit bounds. -/
def unrelabelMonocyclicRCTCandidatesBounded (enumeration : V ≃ Fin n)
    (candidates : List (SuppliedMonocyclicRCTReferenceCandidate V)) :
    ∀ candidate ∈ unrelabelMonocyclicRCTCandidates enumeration candidates,
      rctCandidateBoundedIn n candidate := by
  intro candidate member
  rw [unrelabelMonocyclicRCTCandidates, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact ⟨encodeAtom_lt enumeration supplied.ringPosition,
    encodeAtom_lt enumeration supplied.substituent⟩

@[simp] theorem relabelMonocyclicRCTCandidates_length [DecidableEq V]
    (enumeration : V ≃ Fin n) (candidates : List P93MonocyclicRCTReferenceCandidate)
    (bounded : ∀ candidate ∈ candidates, rctCandidateBoundedIn n candidate) :
    (relabelMonocyclicRCTCandidates enumeration candidates bounded).length =
      candidates.length := by
  simp [relabelMonocyclicRCTCandidates]

@[simp] theorem unrelabelMonocyclicRCTCandidates_length (enumeration : V ≃ Fin n)
    (candidates : List (SuppliedMonocyclicRCTReferenceCandidate V)) :
    (unrelabelMonocyclicRCTCandidates enumeration candidates).length =
      candidates.length := by
  simp [unrelabelMonocyclicRCTCandidates]

/-- Exact recovery of the ordered candidate list, including order and multiplicity. -/
theorem unrelabelMonocyclicRCTCandidates_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (candidates : List P93MonocyclicRCTReferenceCandidate)
    (bounded : ∀ candidate ∈ candidates, rctCandidateBoundedIn n candidate) :
    unrelabelMonocyclicRCTCandidates enumeration
        (relabelMonocyclicRCTCandidates enumeration candidates bounded) = candidates := by
  unfold unrelabelMonocyclicRCTCandidates relabelMonocyclicRCTCandidates
  rw [List.map_map]
  trans candidates.attach.map Subtype.val
  · apply List.map_congr_left
    intro candidate _
    exact unrelabelMonocyclicRCTReferenceCandidate_relabel enumeration candidate.1
      (bounded candidate.1 candidate.2)
  · exact List.attach_map_subtype_val candidates

/-- Relabelling a decoded candidate list returns the supplied list. -/
theorem relabelMonocyclicRCTCandidates_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (candidates : List (SuppliedMonocyclicRCTReferenceCandidate V)) :
    relabelMonocyclicRCTCandidates enumeration
        (unrelabelMonocyclicRCTCandidates enumeration candidates)
        (unrelabelMonocyclicRCTCandidatesBounded enumeration candidates) = candidates := by
  unfold relabelMonocyclicRCTCandidates unrelabelMonocyclicRCTCandidates
  rw [List.attach_map, List.map_map]
  trans candidates.attach.map Subtype.val
  · apply List.map_congr_left
    intro candidate _
    exact relabelMonocyclicRCTReferenceCandidate_unrelabel enumeration candidate.1
  · exact List.attach_map_subtype_val candidates

/-- Mirror of `P93MonocyclicRCTLocatedAssignment`. -/
structure SuppliedMonocyclicRCTLocatedAssignment (V : Type*) where
  ringPosition : V
  substituent : V
  side : RingSide
  descriptor : RCTDescriptor

/-- Explicit bounds for one located RCT assignment. -/
def rctLocatedBoundedIn (n : ℕ)
    (assignment : P93MonocyclicRCTLocatedAssignment) : Prop :=
  assignment.ringPosition < n ∧ assignment.substituent < n

/-- Relabel one bounded located RCT assignment. -/
def relabelMonocyclicRCTLocatedAssignment [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignment : P93MonocyclicRCTLocatedAssignment)
    (bounded : rctLocatedBoundedIn n assignment) :
    SuppliedMonocyclicRCTLocatedAssignment V where
  ringPosition := decodeAtom enumeration assignment.ringPosition bounded.1
  substituent := decodeAtom enumeration assignment.substituent bounded.2
  side := assignment.side
  descriptor := assignment.descriptor

/-- Decode one located RCT assignment. -/
def unrelabelMonocyclicRCTLocatedAssignment (enumeration : V ≃ Fin n)
    (assignment : SuppliedMonocyclicRCTLocatedAssignment V) :
    P93MonocyclicRCTLocatedAssignment where
  ringPosition := encodeAtom enumeration assignment.ringPosition
  substituent := encodeAtom enumeration assignment.substituent
  side := assignment.side
  descriptor := assignment.descriptor

/-- Exact recovery of one located RCT assignment. -/
theorem unrelabelMonocyclicRCTLocatedAssignment_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignment : P93MonocyclicRCTLocatedAssignment)
    (bounded : rctLocatedBoundedIn n assignment) :
    unrelabelMonocyclicRCTLocatedAssignment enumeration
        (relabelMonocyclicRCTLocatedAssignment enumeration assignment bounded) =
      assignment := by
  rcases assignment with ⟨ringPosition, substituent, side, descriptor⟩
  simp [unrelabelMonocyclicRCTLocatedAssignment,
    relabelMonocyclicRCTLocatedAssignment, encodeAtom_decodeAtom]

/-- Relabelling a decoded located RCT assignment returns the supplied record. -/
theorem relabelMonocyclicRCTLocatedAssignment_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignment : SuppliedMonocyclicRCTLocatedAssignment V) :
    relabelMonocyclicRCTLocatedAssignment enumeration
        (unrelabelMonocyclicRCTLocatedAssignment enumeration assignment)
        ⟨encodeAtom_lt enumeration assignment.ringPosition,
          encodeAtom_lt enumeration assignment.substituent⟩ = assignment := by
  rcases assignment with ⟨ringPosition, substituent, side, descriptor⟩
  simp [unrelabelMonocyclicRCTLocatedAssignment,
    relabelMonocyclicRCTLocatedAssignment, decodeAtom_encodeAtom]

/-- Relabel an ordered list of bounded located RCT assignments. -/
def relabelMonocyclicRCTLocatedAssignments [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List P93MonocyclicRCTLocatedAssignment)
    (bounded : ∀ assignment ∈ assignments, rctLocatedBoundedIn n assignment) :
    List (SuppliedMonocyclicRCTLocatedAssignment V) :=
  assignments.attach.map fun assignment =>
    relabelMonocyclicRCTLocatedAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)

/-- Decode an ordered list of located RCT assignments. -/
def unrelabelMonocyclicRCTLocatedAssignments (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedMonocyclicRCTLocatedAssignment V)) :
    List P93MonocyclicRCTLocatedAssignment :=
  assignments.map (unrelabelMonocyclicRCTLocatedAssignment enumeration)

/-- Every decoded located assignment satisfies the same explicit bounds. -/
def unrelabelMonocyclicRCTLocatedAssignmentsBounded (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedMonocyclicRCTLocatedAssignment V)) :
    ∀ assignment ∈ unrelabelMonocyclicRCTLocatedAssignments enumeration assignments,
      rctLocatedBoundedIn n assignment := by
  intro assignment member
  rw [unrelabelMonocyclicRCTLocatedAssignments, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact ⟨encodeAtom_lt enumeration supplied.ringPosition,
    encodeAtom_lt enumeration supplied.substituent⟩

@[simp] theorem relabelMonocyclicRCTLocatedAssignments_length [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignments : List P93MonocyclicRCTLocatedAssignment)
    (bounded : ∀ assignment ∈ assignments, rctLocatedBoundedIn n assignment) :
    (relabelMonocyclicRCTLocatedAssignments enumeration assignments bounded).length =
      assignments.length := by
  simp [relabelMonocyclicRCTLocatedAssignments]

@[simp] theorem unrelabelMonocyclicRCTLocatedAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedMonocyclicRCTLocatedAssignment V)) :
    (unrelabelMonocyclicRCTLocatedAssignments enumeration assignments).length =
      assignments.length := by
  simp [unrelabelMonocyclicRCTLocatedAssignments]

/-- Exact recovery of the ordered located-assignment list. -/
theorem unrelabelMonocyclicRCTLocatedAssignments_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignments : List P93MonocyclicRCTLocatedAssignment)
    (bounded : ∀ assignment ∈ assignments, rctLocatedBoundedIn n assignment) :
    unrelabelMonocyclicRCTLocatedAssignments enumeration
        (relabelMonocyclicRCTLocatedAssignments enumeration assignments bounded) =
      assignments := by
  unfold unrelabelMonocyclicRCTLocatedAssignments relabelMonocyclicRCTLocatedAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelMonocyclicRCTLocatedAssignment_relabel enumeration assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

/-- Relabelling a decoded located-assignment list returns the supplied list. -/
theorem relabelMonocyclicRCTLocatedAssignments_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedMonocyclicRCTLocatedAssignment V)) :
    relabelMonocyclicRCTLocatedAssignments enumeration
        (unrelabelMonocyclicRCTLocatedAssignments enumeration assignments)
        (unrelabelMonocyclicRCTLocatedAssignmentsBounded enumeration assignments) =
      assignments := by
  unfold relabelMonocyclicRCTLocatedAssignments unrelabelMonocyclicRCTLocatedAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelMonocyclicRCTLocatedAssignment_unrelabel enumeration assignment.1
  · exact List.attach_map_subtype_val assignments

/-- Mirror of `P93MonocyclicRCTAuthorityObservation`. -/
structure SuppliedMonocyclicRCTAuthorityObservation (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  ringAtoms : List V
  candidates : List (SuppliedMonocyclicRCTReferenceCandidate V)
  selected : SuppliedMonocyclicRCTReferenceCandidate V
  referenceSide : RingSide
  assignments : List (SuppliedMonocyclicRCTLocatedAssignment V)

/-- Explicit bounds for an RCT observation. -/
def rctObservationBoundedIn (n : ℕ)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicRCTAuthorityObservation policy) : Prop :=
  (∀ atom ∈ observation.ringAtoms, atom < n) ∧
    (∀ candidate ∈ observation.candidates, rctCandidateBoundedIn n candidate) ∧
      rctCandidateBoundedIn n observation.selected ∧
        (∀ assignment ∈ observation.assignments, rctLocatedBoundedIn n assignment)

/-- Relabel a bounded RCT observation. -/
def relabelMonocyclicRCTAuthorityObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicRCTAuthorityObservation policy)
    (bounded : rctObservationBoundedIn n policy observation) :
    SuppliedMonocyclicRCTAuthorityObservation V policy where
  ringAtoms := relabelList enumeration observation.ringAtoms bounded.1
  candidates := relabelMonocyclicRCTCandidates enumeration observation.candidates bounded.2.1
  selected := relabelMonocyclicRCTReferenceCandidate enumeration observation.selected
    bounded.2.2.1
  referenceSide := observation.referenceSide
  assignments := relabelMonocyclicRCTLocatedAssignments enumeration observation.assignments
    bounded.2.2.2

/-- Decode an RCT observation to the raw carrier record. -/
def unrelabelMonocyclicRCTAuthorityObservation (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicRCTAuthorityObservation V policy) :
    P93MonocyclicRCTAuthorityObservation policy where
  ringAtoms := unrelabelList enumeration observation.ringAtoms
  candidates := unrelabelMonocyclicRCTCandidates enumeration observation.candidates
  selected := unrelabelMonocyclicRCTReferenceCandidate enumeration observation.selected
  referenceSide := observation.referenceSide
  assignments := unrelabelMonocyclicRCTLocatedAssignments enumeration observation.assignments

/-- Exact recovery of an RCT observation, including the candidate order, the selected candidate
and the located assignments. -/
theorem unrelabelMonocyclicRCTAuthorityObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicRCTAuthorityObservation policy)
    (bounded : rctObservationBoundedIn n policy observation) :
    unrelabelMonocyclicRCTAuthorityObservation enumeration policy
        (relabelMonocyclicRCTAuthorityObservation enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨ringAtoms, candidates, selected, referenceSide, assignments⟩
  simp [unrelabelMonocyclicRCTAuthorityObservation,
    relabelMonocyclicRCTAuthorityObservation,
    unrelabelMonocyclicRCTCandidates_relabel,
    unrelabelMonocyclicRCTLocatedAssignments_relabel,
    unrelabelMonocyclicRCTReferenceCandidate_relabel,
    unrelabelList_relabelList]

/-- Relabelling a decoded RCT observation returns the supplied record. -/
theorem relabelMonocyclicRCTAuthorityObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicRCTAuthorityObservation V policy) :
    relabelMonocyclicRCTAuthorityObservation enumeration policy
        (unrelabelMonocyclicRCTAuthorityObservation enumeration policy observation)
        ⟨unrelabelList_bounded enumeration observation.ringAtoms,
          unrelabelMonocyclicRCTCandidatesBounded enumeration observation.candidates,
          ⟨encodeAtom_lt enumeration observation.selected.ringPosition,
            encodeAtom_lt enumeration observation.selected.substituent⟩,
          unrelabelMonocyclicRCTLocatedAssignmentsBounded enumeration
            observation.assignments⟩ = observation := by
  rcases observation with ⟨ringAtoms, candidates, selected, referenceSide, assignments⟩
  rcases selected with ⟨selectedRingPosition, selectedSubstituent, selectedCitation,
    selectedNamedAsSuffix, selectedSequencePriority⟩
  simp [unrelabelMonocyclicRCTAuthorityObservation,
    relabelMonocyclicRCTAuthorityObservation,
    relabelMonocyclicRCTCandidates_unrelabel,
    relabelMonocyclicRCTLocatedAssignments_unrelabel,
    relabelMonocyclicRCTReferenceCandidate_unrelabel,
    relabelList_unrelabelList]

/-! ## The remaining monocyclic observation rows -/

/-- Mirror of `P93MonocyclicUnsaturationAuthorityObservation`. -/
structure SuppliedMonocyclicUnsaturationAuthorityObservation (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : SuppliedMonocyclicPhysicalUnit V
  topology : CyclicUnsaturationTopology
  doubleBondCount : Nat
  contextIsPIN : Bool
  descriptor : ChiralCycloalkeneDescriptor

/-- Explicit bounds for an unsaturation observation. -/
def monocyclicUnsaturationObservationBoundedIn (n : ℕ)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicUnsaturationAuthorityObservation policy) : Prop :=
  monocyclicPhysicalUnitBoundedIn n observation.physical

/-- Relabel the physical unit of an unsaturation observation. -/
def relabelMonocyclicUnsaturationAuthorityObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicUnsaturationAuthorityObservation policy)
    (bounded : monocyclicUnsaturationObservationBoundedIn n policy observation) :
    SuppliedMonocyclicUnsaturationAuthorityObservation V policy where
  physical := relabelMonocyclicPhysicalUnit enumeration observation.physical bounded
  topology := observation.topology
  doubleBondCount := observation.doubleBondCount
  contextIsPIN := observation.contextIsPIN
  descriptor := observation.descriptor

/-- Decode an unsaturation observation. -/
def unrelabelMonocyclicUnsaturationAuthorityObservation (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicUnsaturationAuthorityObservation V policy) :
    P93MonocyclicUnsaturationAuthorityObservation policy where
  physical := unrelabelMonocyclicPhysicalUnit enumeration observation.physical
  topology := observation.topology
  doubleBondCount := observation.doubleBondCount
  contextIsPIN := observation.contextIsPIN
  descriptor := observation.descriptor

/-- Exact recovery of an unsaturation observation. -/
theorem unrelabelMonocyclicUnsaturationAuthorityObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicUnsaturationAuthorityObservation policy)
    (bounded : monocyclicUnsaturationObservationBoundedIn n policy observation) :
    unrelabelMonocyclicUnsaturationAuthorityObservation enumeration policy
        (relabelMonocyclicUnsaturationAuthorityObservation enumeration policy observation
          bounded) = observation := by
  rcases observation with ⟨physical, topology, doubleBondCount, contextIsPIN, descriptor⟩
  simp [unrelabelMonocyclicUnsaturationAuthorityObservation,
    relabelMonocyclicUnsaturationAuthorityObservation,
    unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]

/-- Relabelling a decoded unsaturation observation returns the supplied record. -/
theorem relabelMonocyclicUnsaturationAuthorityObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicUnsaturationAuthorityObservation V policy) :
    relabelMonocyclicUnsaturationAuthorityObservation enumeration policy
        (unrelabelMonocyclicUnsaturationAuthorityObservation enumeration policy observation)
        ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
          unrelabelUnitBounded enumeration observation.physical.unit⟩ = observation := by
  rcases observation with ⟨physical, topology, doubleBondCount, contextIsPIN, descriptor⟩
  rcases physical with ⟨ringAtoms, unit⟩
  simp [unrelabelMonocyclicUnsaturationAuthorityObservation,
    relabelMonocyclicUnsaturationAuthorityObservation,
    unrelabelMonocyclicPhysicalUnit, relabelMonocyclicPhysicalUnit,
    relabelList_unrelabelList, relabelUnit_unrelabelUnit]

/-- Mirror of `P93MonocyclicDoubleBondAuthorityObservation`. -/
structure SuppliedMonocyclicDoubleBondAuthorityObservation (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : SuppliedMonocyclicPhysicalUnit V
  doubleBondCount : Nat
  geometry : MonocyclicSeniorLigandGeometry
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

/-- Explicit bounds for a double-bond observation. -/
def monocyclicDoubleBondObservationBoundedIn (n : ℕ)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicDoubleBondAuthorityObservation policy) : Prop :=
  monocyclicPhysicalUnitBoundedIn n observation.physical

/-- Relabel the physical unit of a double-bond observation. -/
def relabelMonocyclicDoubleBondAuthorityObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicDoubleBondAuthorityObservation policy)
    (bounded : monocyclicDoubleBondObservationBoundedIn n policy observation) :
    SuppliedMonocyclicDoubleBondAuthorityObservation V policy where
  physical := relabelMonocyclicPhysicalUnit enumeration observation.physical bounded
  doubleBondCount := observation.doubleBondCount
  geometry := observation.geometry
  descriptor? := observation.descriptor?

/-- Decode a double-bond observation. -/
def unrelabelMonocyclicDoubleBondAuthorityObservation (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicDoubleBondAuthorityObservation V policy) :
    P93MonocyclicDoubleBondAuthorityObservation policy where
  physical := unrelabelMonocyclicPhysicalUnit enumeration observation.physical
  doubleBondCount := observation.doubleBondCount
  geometry := observation.geometry
  descriptor? := observation.descriptor?

/-- Exact recovery of a double-bond observation. -/
theorem unrelabelMonocyclicDoubleBondAuthorityObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicDoubleBondAuthorityObservation policy)
    (bounded : monocyclicDoubleBondObservationBoundedIn n policy observation) :
    unrelabelMonocyclicDoubleBondAuthorityObservation enumeration policy
        (relabelMonocyclicDoubleBondAuthorityObservation enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨physical, doubleBondCount, geometry, descriptor?⟩
  simp [unrelabelMonocyclicDoubleBondAuthorityObservation,
    relabelMonocyclicDoubleBondAuthorityObservation,
    unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]

/-- Relabelling a decoded double-bond observation returns the supplied record. -/
theorem relabelMonocyclicDoubleBondAuthorityObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicDoubleBondAuthorityObservation V policy) :
    relabelMonocyclicDoubleBondAuthorityObservation enumeration policy
        (unrelabelMonocyclicDoubleBondAuthorityObservation enumeration policy observation)
        ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
          unrelabelUnitBounded enumeration observation.physical.unit⟩ = observation := by
  rcases observation with ⟨physical, doubleBondCount, geometry, descriptor?⟩
  rcases physical with ⟨ringAtoms, unit⟩
  simp [unrelabelMonocyclicDoubleBondAuthorityObservation,
    relabelMonocyclicDoubleBondAuthorityObservation,
    unrelabelMonocyclicPhysicalUnit, relabelMonocyclicPhysicalUnit,
    relabelList_unrelabelList, relabelUnit_unrelabelUnit]

/-- Mirror of `P93MonocyclicExocyclicAuthorityObservation`. -/
structure SuppliedMonocyclicExocyclicAuthorityObservation (V : Type*)
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : SuppliedMonocyclicPhysicalUnit V
  contextIsPIN : Bool
  doubleBondCount : Nat
  oppositePositions : Bool
  method : ExocyclicNamingMethod
  treatment : ExocyclicSystemTreatment
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

/-- Explicit bounds for an exocyclic observation. -/
def monocyclicExocyclicObservationBoundedIn (n : ℕ)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicExocyclicAuthorityObservation policy) : Prop :=
  monocyclicPhysicalUnitBoundedIn n observation.physical

/-- Relabel the physical unit of an exocyclic observation. -/
def relabelMonocyclicExocyclicAuthorityObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicExocyclicAuthorityObservation policy)
    (bounded : monocyclicExocyclicObservationBoundedIn n policy observation) :
    SuppliedMonocyclicExocyclicAuthorityObservation V policy where
  physical := relabelMonocyclicPhysicalUnit enumeration observation.physical bounded
  contextIsPIN := observation.contextIsPIN
  doubleBondCount := observation.doubleBondCount
  oppositePositions := observation.oppositePositions
  method := observation.method
  treatment := observation.treatment
  descriptor? := observation.descriptor?

/-- Decode an exocyclic observation. -/
def unrelabelMonocyclicExocyclicAuthorityObservation (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicExocyclicAuthorityObservation V policy) :
    P93MonocyclicExocyclicAuthorityObservation policy where
  physical := unrelabelMonocyclicPhysicalUnit enumeration observation.physical
  contextIsPIN := observation.contextIsPIN
  doubleBondCount := observation.doubleBondCount
  oppositePositions := observation.oppositePositions
  method := observation.method
  treatment := observation.treatment
  descriptor? := observation.descriptor?

/-- Exact recovery of an exocyclic observation. -/
theorem unrelabelMonocyclicExocyclicAuthorityObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicExocyclicAuthorityObservation policy)
    (bounded : monocyclicExocyclicObservationBoundedIn n policy observation) :
    unrelabelMonocyclicExocyclicAuthorityObservation enumeration policy
        (relabelMonocyclicExocyclicAuthorityObservation enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨physical, contextIsPIN, doubleBondCount, oppositePositions,
    method, treatment, descriptor?⟩
  simp [unrelabelMonocyclicExocyclicAuthorityObservation,
    relabelMonocyclicExocyclicAuthorityObservation,
    unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]

/-- Relabelling a decoded exocyclic observation returns the supplied record. -/
theorem relabelMonocyclicExocyclicAuthorityObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : SuppliedMonocyclicExocyclicAuthorityObservation V policy) :
    relabelMonocyclicExocyclicAuthorityObservation enumeration policy
        (unrelabelMonocyclicExocyclicAuthorityObservation enumeration policy observation)
        ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
          unrelabelUnitBounded enumeration observation.physical.unit⟩ = observation := by
  rcases observation with ⟨physical, contextIsPIN, doubleBondCount, oppositePositions,
    method, treatment, descriptor?⟩
  rcases physical with ⟨ringAtoms, unit⟩
  simp [unrelabelMonocyclicExocyclicAuthorityObservation,
    relabelMonocyclicExocyclicAuthorityObservation,
    unrelabelMonocyclicPhysicalUnit, relabelMonocyclicPhysicalUnit,
    relabelList_unrelabelList, relabelUnit_unrelabelUnit]

/-- Bounds of a valid monocyclic physical unit: the ring traversal is bounded by the carrier's own
closed-cycle predicate, and the physical unit by its own `ValidFor`. -/
theorem monocyclicPhysicalUnitBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicPhysicalUnit)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    monocyclicPhysicalUnitBoundedIn source.molecule.atomCount observation :=
  ⟨valid.1.2.2.1,
    physicalUnitBoundedIn_of_validFor source policy.physicalObservation observation.unit
      valid.2.2.1 spatialWellFormed⟩

/-- Bounds of a valid general assignment. -/
theorem generalAssignmentBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicGeneralAssignment policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    monocyclicGeneralAssignmentBoundedIn source.molecule.atomCount policy observation :=
  monocyclicPhysicalUnitBoundedIn_of_validFor source policy observation.physical valid.1
    spatialWellFormed

/-- Bounds of a valid center observation. -/
theorem centerObservationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicCenterAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    monocyclicCenterObservationBoundedIn source.molecule.atomCount policy observation :=
  monocyclicPhysicalUnitBoundedIn_of_validFor source policy observation.physical valid.1
    spatialWellFormed

/-- Bounds of a valid cis/trans observation.  Ring positions are ring members; both substituents
are endpoints of genuine binary bonds and are bounded by the source structural certificate. -/
theorem cisTransObservationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicCisTransAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed) :
    cisTransObservationBoundedIn source.molecule.atomCount policy observation := by
  rcases valid with ⟨closedCycle, _monocyclicObserved, firstMember, secondMember,
    _distinctPositions, _distinctSubstituents, _firstNotRing, _secondNotRing, firstBond,
    secondBond, _planeObserved, _planeApplicable, _firstSide, _secondSide, _relative⟩
  have ringBounded := closedCycle.2.2.1
  exact ⟨ringBounded, ringBounded _ firstMember, ringBounded _ secondMember,
    (binaryBond_atoms_bounded source structurallyWellFormed firstBond).2,
    (binaryBond_atoms_bounded source structurallyWellFormed secondBond).2⟩

/-- Bounds of a valid RCT observation.  Candidates are ring positions plus binary-bond
substituents; the selected candidate is a member of the candidate list; every located assignment
is matched to a candidate by the carrier's own cover conjunct. -/
theorem rctObservationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicRCTAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed) :
    rctObservationBoundedIn source.molecule.atomCount policy observation := by
  rcases valid with ⟨closedCycle, _monocyclicObserved, _candidatesNe, _candidatesNodup,
    perCandidate, isReference, _referenceSide, _sideObserved, _assignmentsNe, _assignmentsNodup,
    _candidateCover, perAssignment⟩
  have ringBounded := closedCycle.2.2.1
  refine ⟨ringBounded, ?_, ?_, ?_⟩
  · intro candidate member
    have candidateData := perCandidate candidate member
    exact ⟨ringBounded _ candidateData.1,
      (binaryBond_atoms_bounded source structurallyWellFormed candidateData.2.2.1).2⟩
  · have selectedMember : observation.selected ∈ observation.candidates := isReference.1
    have candidateData := perCandidate observation.selected selectedMember
    exact ⟨ringBounded _ candidateData.1,
      (binaryBond_atoms_bounded source structurallyWellFormed candidateData.2.2.1).2⟩
  · intro assignment member
    rcases (perAssignment assignment member).1 with
      ⟨candidate, candidateMember, ringEq, substituentEq⟩
    have candidateData := perCandidate candidate candidateMember
    have substituentBounded :=
      (binaryBond_atoms_bounded source structurallyWellFormed candidateData.2.2.1).2
    refine ⟨?_, ?_⟩
    · rw [ringEq]
      exact ringBounded _ candidateData.1
    · rw [substituentEq]
      exact substituentBounded

/-- Bounds of a valid unsaturation observation. -/
theorem unsaturationObservationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicUnsaturationAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    monocyclicUnsaturationObservationBoundedIn source.molecule.atomCount policy observation :=
  monocyclicPhysicalUnitBoundedIn_of_validFor source policy observation.physical valid.1
    spatialWellFormed

/-- Bounds of a valid double-bond observation. -/
theorem doubleBondObservationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicDoubleBondAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    monocyclicDoubleBondObservationBoundedIn source.molecule.atomCount policy observation :=
  monocyclicPhysicalUnitBoundedIn_of_validFor source policy observation.physical valid.1
    spatialWellFormed

/-- Bounds of a valid exocyclic observation. -/
theorem exocyclicObservationBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93MonocyclicAuthorityPolicy)
    (observation : P93MonocyclicExocyclicAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    monocyclicExocyclicObservationBoundedIn source.molecule.atomCount policy observation :=
  monocyclicPhysicalUnitBoundedIn_of_validFor source policy observation.physical valid.1
    spatialWellFormed

/-! ## The monocyclic tagged sum -/

/-- The source-side tagged sum: exactly the pre-existing monocyclic carrier records. -/
inductive SourceMonocyclicObservation (policy : P93MonocyclicAuthorityPolicy) where
  | physicalUnit (observation : P93MonocyclicPhysicalUnit)
  | general (observation : P93MonocyclicGeneralAssignment policy)
  | center (observation : P93MonocyclicCenterAuthorityObservation policy)
  | cisTrans (observation : P93MonocyclicCisTransAuthorityObservation policy)
  | rct (observation : P93MonocyclicRCTAuthorityObservation policy)
  | unsaturation (observation : P93MonocyclicUnsaturationAuthorityObservation policy)
  | doubleBond (observation : P93MonocyclicDoubleBondAuthorityObservation policy)
  | exocyclic (observation : P93MonocyclicExocyclicAuthorityObservation policy)

/-- The native tagged payload: one constructor per pre-existing monocyclic record. -/
inductive MonocyclicObservation (V : Type*) (policy : P93MonocyclicAuthorityPolicy) where
  | physicalUnit (observation : SuppliedMonocyclicPhysicalUnit V)
  | general (observation : SuppliedMonocyclicGeneralAssignment V policy)
  | center (observation : SuppliedMonocyclicCenterAuthorityObservation V policy)
  | cisTrans (observation : SuppliedMonocyclicCisTransAuthorityObservation V policy)
  | rct (observation : SuppliedMonocyclicRCTAuthorityObservation V policy)
  | unsaturation (observation : SuppliedMonocyclicUnsaturationAuthorityObservation V policy)
  | doubleBond (observation : SuppliedMonocyclicDoubleBondAuthorityObservation V policy)
  | exocyclic (observation : SuppliedMonocyclicExocyclicAuthorityObservation V policy)

/-- Explicit physical-unit bounds for a tagged source observation. -/
def SourceMonocyclicObservation.BoundedIn {policy : P93MonocyclicAuthorityPolicy} (n : ℕ) :
    SourceMonocyclicObservation policy → Prop
  | .physicalUnit observation => monocyclicPhysicalUnitBoundedIn n observation
  | .general observation => monocyclicGeneralAssignmentBoundedIn n policy observation
  | .center observation => monocyclicCenterObservationBoundedIn n policy observation
  | .cisTrans observation => cisTransObservationBoundedIn n policy observation
  | .rct observation => rctObservationBoundedIn n policy observation
  | .unsaturation observation => monocyclicUnsaturationObservationBoundedIn n policy observation
  | .doubleBond observation => monocyclicDoubleBondObservationBoundedIn n policy observation
  | .exocyclic observation => monocyclicExocyclicObservationBoundedIn n policy observation

/-- Relabel one tagged source observation.  Atom references are reindexed; every other field is
copied literally. -/
def relabelMonocyclicObservation {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n) :
    (observation : SourceMonocyclicObservation policy) →
      observation.BoundedIn n → MonocyclicObservation V policy
  | .physicalUnit observation, bounded =>
      .physicalUnit (relabelMonocyclicPhysicalUnit enumeration observation bounded)
  | .general observation, bounded =>
      .general (relabelMonocyclicGeneralAssignment enumeration policy observation bounded)
  | .center observation, bounded =>
      .center (relabelMonocyclicCenterAuthorityObservation enumeration policy observation bounded)
  | .cisTrans observation, bounded =>
      .cisTrans
        (relabelMonocyclicCisTransAuthorityObservation enumeration policy observation bounded)
  | .rct observation, bounded =>
      .rct (relabelMonocyclicRCTAuthorityObservation enumeration policy observation bounded)
  | .unsaturation observation, bounded =>
      .unsaturation
        (relabelMonocyclicUnsaturationAuthorityObservation enumeration policy observation bounded)
  | .doubleBond observation, bounded =>
      .doubleBond
        (relabelMonocyclicDoubleBondAuthorityObservation enumeration policy observation bounded)
  | .exocyclic observation, bounded =>
      .exocyclic
        (relabelMonocyclicExocyclicAuthorityObservation enumeration policy observation bounded)

/-- Decode one tagged observation to the exact pre-existing carrier record. -/
def unrelabelMonocyclicObservation {policy : P93MonocyclicAuthorityPolicy}
    (enumeration : V ≃ Fin n) :
    MonocyclicObservation V policy → SourceMonocyclicObservation policy
  | .physicalUnit observation =>
      .physicalUnit (unrelabelMonocyclicPhysicalUnit enumeration observation)
  | .general observation =>
      .general (unrelabelMonocyclicGeneralAssignment enumeration policy observation)
  | .center observation =>
      .center (unrelabelMonocyclicCenterAuthorityObservation enumeration policy observation)
  | .cisTrans observation =>
      .cisTrans
        (unrelabelMonocyclicCisTransAuthorityObservation enumeration policy observation)
  | .rct observation =>
      .rct (unrelabelMonocyclicRCTAuthorityObservation enumeration policy observation)
  | .unsaturation observation =>
      .unsaturation
        (unrelabelMonocyclicUnsaturationAuthorityObservation enumeration policy observation)
  | .doubleBond observation =>
      .doubleBond
        (unrelabelMonocyclicDoubleBondAuthorityObservation enumeration policy observation)
  | .exocyclic observation =>
      .exocyclic
        (unrelabelMonocyclicExocyclicAuthorityObservation enumeration policy observation)

/-- Exact recovery of every existing monocyclic observation record.  This theorem is the total
constructor-by-constructor claim: no observation shape is rejected, and no original record is
stored as a payload. -/
theorem unrelabelMonocyclicObservation_relabelMonocyclicObservation
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : SourceMonocyclicObservation policy)
    (bounded : observation.BoundedIn n) :
    unrelabelMonocyclicObservation enumeration
        (relabelMonocyclicObservation enumeration observation bounded) = observation := by
  cases observation with
  | physicalUnit observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]
  | general observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        unrelabelMonocyclicGeneralAssignment_relabelMonocyclicGeneralAssignment]
  | center observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        unrelabelMonocyclicCenterAuthorityObservation_relabel]
  | cisTrans observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        unrelabelMonocyclicCisTransAuthorityObservation_relabel]
  | rct observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        unrelabelMonocyclicRCTAuthorityObservation_relabel]
  | unsaturation observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        unrelabelMonocyclicUnsaturationAuthorityObservation_relabel]
  | doubleBond observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        unrelabelMonocyclicDoubleBondAuthorityObservation_relabel]
  | exocyclic observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        unrelabelMonocyclicExocyclicAuthorityObservation_relabel]

/-! ## Inverse on the supplied side -/

/-- Bounds of a decoded tagged observation. -/
def unrelabelMonocyclicObservationBounded {policy : P93MonocyclicAuthorityPolicy}
    [DecidableEq V] (enumeration : V ≃ Fin n) :
    (observation : MonocyclicObservation V policy) →
      (unrelabelMonocyclicObservation enumeration observation).BoundedIn n
  | .physicalUnit observation =>
      ⟨unrelabelList_bounded enumeration observation.ringAtoms,
        unrelabelUnitBounded enumeration observation.unit⟩
  | .general observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .center observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .cisTrans observation =>
      ⟨unrelabelList_bounded enumeration observation.ringAtoms,
        encodeAtom_lt enumeration observation.firstRingPosition,
        encodeAtom_lt enumeration observation.secondRingPosition,
        encodeAtom_lt enumeration observation.firstSubstituent,
        encodeAtom_lt enumeration observation.secondSubstituent⟩
  | .rct observation =>
      ⟨unrelabelList_bounded enumeration observation.ringAtoms,
        unrelabelMonocyclicRCTCandidatesBounded enumeration observation.candidates,
        ⟨encodeAtom_lt enumeration observation.selected.ringPosition,
          encodeAtom_lt enumeration observation.selected.substituent⟩,
        unrelabelMonocyclicRCTLocatedAssignmentsBounded enumeration observation.assignments⟩
  | .unsaturation observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .doubleBond observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .exocyclic observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩

/-- Relabelling a decoded tagged observation returns the supplied observation.  This is the
native representation inverse and requires no source validity. -/
theorem relabelMonocyclicObservation_unrelabelMonocyclicObservation
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : MonocyclicObservation V policy) :
    relabelMonocyclicObservation enumeration
        (unrelabelMonocyclicObservation enumeration observation)
        (unrelabelMonocyclicObservationBounded enumeration observation) = observation := by
  cases observation with
  | physicalUnit observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        relabelMonocyclicPhysicalUnit_unrelabelMonocyclicPhysicalUnit]
  | general observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        relabelMonocyclicGeneralAssignment_unrelabelMonocyclicGeneralAssignment]
  | center observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        relabelMonocyclicCenterAuthorityObservation_unrelabel]
  | cisTrans observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        relabelMonocyclicCisTransAuthorityObservation_unrelabel]
  | rct observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        relabelMonocyclicRCTAuthorityObservation_unrelabel]
  | unsaturation observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        relabelMonocyclicUnsaturationAuthorityObservation_unrelabel]
  | doubleBond observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        relabelMonocyclicDoubleBondAuthorityObservation_unrelabel]
  | exocyclic observation =>
      simp [relabelMonocyclicObservation, unrelabelMonocyclicObservation,
        relabelMonocyclicExocyclicAuthorityObservation_unrelabel]

/-! ## Existing validity predicates, consumed at the same source and policy -/

/-- The existing `ValidFor` of each pre-existing record, dispatched on the tag.  This is a
dispatch only: every branch is the record's own pre-existing predicate. -/
def SourceMonocyclicObservation.ValidFor {policy : P93MonocyclicAuthorityPolicy}
    (source : AuthoritativeChemicalInput) :
    SourceMonocyclicObservation policy → Prop
  | .physicalUnit observation => observation.ValidFor policy source
  | .general observation => observation.ValidFor policy source
  | .center observation => observation.ValidFor policy source
  | .cisTrans observation => observation.ValidFor policy source
  | .rct observation => observation.ValidFor policy source
  | .unsaturation observation => observation.ValidFor policy source
  | .doubleBond observation => observation.ValidFor policy source
  | .exocyclic observation => observation.ValidFor policy source

/-- **Validity transport through the exact decode.**  For every tagged observation, the decoded
record's `ValidFor` at the same `source` and `policy` is equivalent to the original record's
`ValidFor`.  The equivalence is the record equality, not an invariance claim about renumbering. -/
theorem validFor_unrelabelMonocyclicObservation_relabelMonocyclicObservation_iff
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observation : SourceMonocyclicObservation policy)
    (bounded : observation.BoundedIn n) :
    (unrelabelMonocyclicObservation enumeration
        (relabelMonocyclicObservation enumeration observation bounded)).ValidFor source ↔
      observation.ValidFor source := by
  rw [unrelabelMonocyclicObservation_relabelMonocyclicObservation]

/-- Forward validity preservation at the same source and policy. -/
theorem validFor_of_relabelMonocyclicObservation
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observation : SourceMonocyclicObservation policy)
    (bounded : observation.BoundedIn n)
    (valid : observation.ValidFor source) :
    (unrelabelMonocyclicObservation enumeration
        (relabelMonocyclicObservation enumeration observation bounded)).ValidFor source :=
  (validFor_unrelabelMonocyclicObservation_relabelMonocyclicObservation_iff enumeration source
    observation bounded).mpr valid

/-- Bounds derived from the actual `ValidFor` of a tagged source observation. -/
theorem SourceMonocyclicObservation.boundedIn_of_validFor
    {policy : P93MonocyclicAuthorityPolicy}
    (source : AuthoritativeChemicalInput)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed)
    (observation : SourceMonocyclicObservation policy)
    (valid : observation.ValidFor source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    observation.BoundedIn source.molecule.atomCount := by
  cases observation with
  | physicalUnit observation =>
      exact monocyclicPhysicalUnitBoundedIn_of_validFor source policy observation valid
        spatialWellFormed
  | general observation =>
      exact generalAssignmentBoundedIn_of_validFor source policy observation valid
        spatialWellFormed
  | center observation =>
      exact centerObservationBoundedIn_of_validFor source policy observation valid
        spatialWellFormed
  | cisTrans observation =>
      exact cisTransObservationBoundedIn_of_validFor source policy observation valid
        structurallyWellFormed
  | rct observation =>
      exact rctObservationBoundedIn_of_validFor source policy observation valid
        structurallyWellFormed
  | unsaturation observation =>
      exact unsaturationObservationBoundedIn_of_validFor source policy observation valid
        spatialWellFormed
  | doubleBond observation =>
      exact doubleBondObservationBoundedIn_of_validFor source policy observation valid
        spatialWellFormed
  | exocyclic observation =>
      exact exocyclicObservationBoundedIn_of_validFor source policy observation valid
        spatialWellFormed

/-! ## Ordered heterogeneous lists -/

/-- Relabel an ordered heterogeneous list of source observations. -/
def relabelMonocyclicObservationList {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (SourceMonocyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    List (MonocyclicObservation V policy) :=
  observations.attach.map fun observation =>
    relabelMonocyclicObservation enumeration observation.1
      (bounded observation.1 observation.2)

/-- Decode an ordered heterogeneous list of native observations. -/
def unrelabelMonocyclicObservationList {policy : P93MonocyclicAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (observations : List (MonocyclicObservation V policy)) :
    List (SourceMonocyclicObservation policy) :=
  observations.map (unrelabelMonocyclicObservation enumeration)

/-- Every decoded element of a heterogeneous list satisfies the same explicit bounds. -/
def unrelabelMonocyclicObservationListBounded {policy : P93MonocyclicAuthorityPolicy}
    [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (MonocyclicObservation V policy)) :
    ∀ observation ∈ unrelabelMonocyclicObservationList enumeration observations,
      observation.BoundedIn n := by
  intro observation member
  rw [unrelabelMonocyclicObservationList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelMonocyclicObservationBounded enumeration presented

@[simp] theorem relabelMonocyclicObservationList_length
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (SourceMonocyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    (relabelMonocyclicObservationList enumeration observations bounded).length =
      observations.length := by
  simp [relabelMonocyclicObservationList]

@[simp] theorem unrelabelMonocyclicObservationList_length
    {policy : P93MonocyclicAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observations : List (MonocyclicObservation V policy)) :
    (unrelabelMonocyclicObservationList enumeration observations).length =
      observations.length := by
  simp [unrelabelMonocyclicObservationList]

/-- Exact recovery of the ordered heterogeneous observation list, including order, multiplicity
and each concrete record shape. -/
theorem unrelabelMonocyclicObservationList_relabelMonocyclicObservationList
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (SourceMonocyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    unrelabelMonocyclicObservationList enumeration
        (relabelMonocyclicObservationList enumeration observations bounded) = observations := by
  unfold unrelabelMonocyclicObservationList relabelMonocyclicObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact unrelabelMonocyclicObservation_relabelMonocyclicObservation enumeration observation.1
      (bounded observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-- Relabelling a decoded heterogeneous list returns the supplied list. -/
theorem relabelMonocyclicObservationList_unrelabelMonocyclicObservationList
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (MonocyclicObservation V policy)) :
    relabelMonocyclicObservationList enumeration
        (unrelabelMonocyclicObservationList enumeration observations)
        (unrelabelMonocyclicObservationListBounded enumeration observations) = observations := by
  unfold relabelMonocyclicObservationList unrelabelMonocyclicObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelMonocyclicObservation_unrelabelMonocyclicObservation enumeration observation.1
  · exact List.attach_map_subtype_val observations

/-! ## Correlated sets of observations -/

/-- Image of a set of source observations under the monocyclic codec. -/
def relabelMonocyclicObservationSet {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (SourceMonocyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    Set (MonocyclicObservation V policy) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelMonocyclicObservation enumeration observation (bounded observation member) =
        presented

/-- Preimage of a set of native observations under the monocyclic codec. -/
def unrelabelMonocyclicObservationSet {policy : P93MonocyclicAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (observations : Set (MonocyclicObservation V policy)) :
    Set (SourceMonocyclicObservation policy) :=
  fun recovered =>
    ∃ presented ∈ observations,
      unrelabelMonocyclicObservation enumeration presented = recovered

/-- Every decoded element of the image set satisfies the explicit bounds. -/
def unrelabelMonocyclicObservationSetBounded {policy : P93MonocyclicAuthorityPolicy}
    [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (MonocyclicObservation V policy)) :
    ∀ observation ∈ unrelabelMonocyclicObservationSet enumeration observations,
      observation.BoundedIn n := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact unrelabelMonocyclicObservationBounded enumeration presented

/-- The correlated-set inverse on the source side. -/
theorem unrelabelMonocyclicObservationSet_relabelMonocyclicObservationSet
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (SourceMonocyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    unrelabelMonocyclicObservationSet enumeration
        (relabelMonocyclicObservationSet enumeration observations bounded) = observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [unrelabelMonocyclicObservation_relabelMonocyclicObservation] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelMonocyclicObservation enumeration recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      unrelabelMonocyclicObservation_relabelMonocyclicObservation enumeration recovered
        (bounded recovered member)⟩

/-- The relabelling of an observation does not inspect the proof of its boundedness. -/
theorem relabelMonocyclicObservation_bound_irrel {policy : P93MonocyclicAuthorityPolicy}
    [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : SourceMonocyclicObservation policy)
    (first second : observation.BoundedIn n) :
    relabelMonocyclicObservation enumeration observation first =
      relabelMonocyclicObservation enumeration observation second := by
  cases observation <;> rfl

/-- Relabelling respects equality of the underlying source observation, independently of how the
two boundedness proofs were obtained. -/
theorem relabelMonocyclicObservation_congr {policy : P93MonocyclicAuthorityPolicy}
    [DecidableEq V] (enumeration : V ≃ Fin n)
    {first second : SourceMonocyclicObservation policy} (h : first = second)
    (firstBounded : first.BoundedIn n) (secondBounded : second.BoundedIn n) :
    relabelMonocyclicObservation enumeration first firstBounded =
      relabelMonocyclicObservation enumeration second secondBounded := by
  cases h
  exact relabelMonocyclicObservation_bound_irrel enumeration _ firstBounded secondBounded

/-- The correlated-set inverse on the native side. -/
theorem relabelMonocyclicObservationSet_unrelabelMonocyclicObservationSet
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (MonocyclicObservation V policy)) :
    relabelMonocyclicObservationSet enumeration
        (unrelabelMonocyclicObservationSet enumeration observations)
        (unrelabelMonocyclicObservationSetBounded enumeration observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have obsEq : unrelabelMonocyclicObservation enumeration presented = observation := by
      have := congrArg (unrelabelMonocyclicObservation enumeration) relabelEq.symm
      rwa [unrelabelMonocyclicObservation_relabelMonocyclicObservation] at this
    have decodeEq' : unrelabelMonocyclicObservation enumeration presented₀ =
        unrelabelMonocyclicObservation enumeration presented := by
      rw [decodeEq, ← obsEq]
    have key : relabelMonocyclicObservation enumeration
        (unrelabelMonocyclicObservation enumeration presented₀)
        (unrelabelMonocyclicObservationBounded enumeration presented₀) = presented := by
      calc
        relabelMonocyclicObservation enumeration
            (unrelabelMonocyclicObservation enumeration presented₀)
            (unrelabelMonocyclicObservationBounded enumeration presented₀) =
          relabelMonocyclicObservation enumeration
            (unrelabelMonocyclicObservation enumeration presented)
            (unrelabelMonocyclicObservationBounded enumeration presented) :=
          relabelMonocyclicObservation_congr enumeration decodeEq' _ _
        _ = presented :=
          relabelMonocyclicObservation_unrelabelMonocyclicObservation enumeration presented
    have presentedEq : presented = presented₀ := by
      rw [← key, relabelMonocyclicObservation_unrelabelMonocyclicObservation]
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨unrelabelMonocyclicObservation enumeration presented,
      ⟨presented, member, rfl⟩,
      relabelMonocyclicObservation_unrelabelMonocyclicObservation enumeration presented⟩

/-- **Correlated validity for a set.**  A native observation belongs to the image of a set exactly
when its decoded record is one of the source observations; consequently its `ValidFor` at the same
source and policy is exactly the validity of that source observation. -/
theorem validFor_mem_relabelMonocyclicObservationSet_iff
    {policy : P93MonocyclicAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observations : Set (SourceMonocyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (presented : MonocyclicObservation V policy)
    (member : presented ∈ relabelMonocyclicObservationSet enumeration observations bounded) :
    (unrelabelMonocyclicObservation enumeration presented).ValidFor source ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelMonocyclicObservation enumeration observation
            (bounded observation observationMember) = presented ∧
          observation.ValidFor source := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rwa [unrelabelMonocyclicObservation_relabelMonocyclicObservation] at valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rwa [unrelabelMonocyclicObservation_relabelMonocyclicObservation]

/-! ## Ring-assembly junctions and rings

The two ring-list indices of a junction are positions in the ordered ring list, not atom
references, and are never relabelled. -/

/-- Mirror of `P93RingAssemblyJunction`. -/
structure SuppliedRingAssemblyJunction (V : Type*) where
  leftRingIndex : Nat
  rightRingIndex : Nat
  leftAtom : V
  rightAtom : V

/-- Explicit bounds for one junction: its two endpoint atoms. -/
def junctionBoundedIn (n : ℕ) (junction : P93RingAssemblyJunction) : Prop :=
  junction.leftAtom < n ∧ junction.rightAtom < n

/-- Relabel one bounded junction, retaining both ring-list indices literally. -/
def relabelRingAssemblyJunction [DecidableEq V] (enumeration : V ≃ Fin n)
    (junction : P93RingAssemblyJunction) (bounded : junctionBoundedIn n junction) :
    SuppliedRingAssemblyJunction V where
  leftRingIndex := junction.leftRingIndex
  rightRingIndex := junction.rightRingIndex
  leftAtom := decodeAtom enumeration junction.leftAtom bounded.1
  rightAtom := decodeAtom enumeration junction.rightAtom bounded.2

/-- Decode one junction, retaining both ring-list indices literally. -/
def unrelabelRingAssemblyJunction (enumeration : V ≃ Fin n)
    (junction : SuppliedRingAssemblyJunction V) : P93RingAssemblyJunction where
  leftRingIndex := junction.leftRingIndex
  rightRingIndex := junction.rightRingIndex
  leftAtom := encodeAtom enumeration junction.leftAtom
  rightAtom := encodeAtom enumeration junction.rightAtom

/-- Exact recovery of one junction, including both ring-list indices. -/
theorem unrelabelRingAssemblyJunction_relabel [DecidableEq V] (enumeration : V ≃ Fin n)
    (junction : P93RingAssemblyJunction) (bounded : junctionBoundedIn n junction) :
    unrelabelRingAssemblyJunction enumeration
        (relabelRingAssemblyJunction enumeration junction bounded) = junction := by
  rcases junction with ⟨leftRingIndex, rightRingIndex, leftAtom, rightAtom⟩
  simp [unrelabelRingAssemblyJunction, relabelRingAssemblyJunction, encodeAtom_decodeAtom]

/-- Relabelling a decoded junction returns the supplied record. -/
theorem relabelRingAssemblyJunction_unrelabel [DecidableEq V] (enumeration : V ≃ Fin n)
    (junction : SuppliedRingAssemblyJunction V) :
    relabelRingAssemblyJunction enumeration
        (unrelabelRingAssemblyJunction enumeration junction)
        ⟨encodeAtom_lt enumeration junction.leftAtom,
          encodeAtom_lt enumeration junction.rightAtom⟩ = junction := by
  rcases junction with ⟨leftRingIndex, rightRingIndex, leftAtom, rightAtom⟩
  simp [unrelabelRingAssemblyJunction, relabelRingAssemblyJunction, decodeAtom_encodeAtom]

/-- Relabel an ordered list of bounded junctions, preserving order and multiplicity. -/
def relabelJunctions [DecidableEq V] (enumeration : V ≃ Fin n)
    (junctions : List P93RingAssemblyJunction)
    (bounded : ∀ junction ∈ junctions, junctionBoundedIn n junction) :
    List (SuppliedRingAssemblyJunction V) :=
  junctions.attach.map fun junction =>
    relabelRingAssemblyJunction enumeration junction.1 (bounded junction.1 junction.2)

/-- Decode an ordered list of junctions. -/
def unrelabelJunctions (enumeration : V ≃ Fin n)
    (junctions : List (SuppliedRingAssemblyJunction V)) :
    List P93RingAssemblyJunction :=
  junctions.map (unrelabelRingAssemblyJunction enumeration)

/-- Every decoded junction satisfies the same explicit bounds. -/
def unrelabelJunctionsBounded (enumeration : V ≃ Fin n)
    (junctions : List (SuppliedRingAssemblyJunction V)) :
    ∀ junction ∈ unrelabelJunctions enumeration junctions, junctionBoundedIn n junction := by
  intro junction member
  rw [unrelabelJunctions, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact ⟨encodeAtom_lt enumeration supplied.leftAtom,
    encodeAtom_lt enumeration supplied.rightAtom⟩

@[simp] theorem relabelJunctions_length [DecidableEq V] (enumeration : V ≃ Fin n)
    (junctions : List P93RingAssemblyJunction)
    (bounded : ∀ junction ∈ junctions, junctionBoundedIn n junction) :
    (relabelJunctions enumeration junctions bounded).length = junctions.length := by
  simp [relabelJunctions]

@[simp] theorem unrelabelJunctions_length (enumeration : V ≃ Fin n)
    (junctions : List (SuppliedRingAssemblyJunction V)) :
    (unrelabelJunctions enumeration junctions).length = junctions.length := by
  simp [unrelabelJunctions]

/-- Exact recovery of the ordered junction list. -/
theorem unrelabelJunctions_relabelJunctions [DecidableEq V] (enumeration : V ≃ Fin n)
    (junctions : List P93RingAssemblyJunction)
    (bounded : ∀ junction ∈ junctions, junctionBoundedIn n junction) :
    unrelabelJunctions enumeration (relabelJunctions enumeration junctions bounded) =
      junctions := by
  unfold unrelabelJunctions relabelJunctions
  rw [List.map_map]
  trans junctions.attach.map Subtype.val
  · apply List.map_congr_left
    intro junction _
    exact unrelabelRingAssemblyJunction_relabel enumeration junction.1
      (bounded junction.1 junction.2)
  · exact List.attach_map_subtype_val junctions

/-- Relabelling a decoded junction list returns the supplied list. -/
theorem relabelJunctions_unrelabelJunctions [DecidableEq V] (enumeration : V ≃ Fin n)
    (junctions : List (SuppliedRingAssemblyJunction V)) :
    relabelJunctions enumeration (unrelabelJunctions enumeration junctions)
        (unrelabelJunctionsBounded enumeration junctions) = junctions := by
  unfold relabelJunctions unrelabelJunctions
  rw [List.attach_map, List.map_map]
  trans junctions.attach.map Subtype.val
  · apply List.map_congr_left
    intro junction _
    exact relabelRingAssemblyJunction_unrelabel enumeration junction.1
  · exact List.attach_map_subtype_val junctions

/-- Relabel an ordered list of bounded rings.  Outer order is the ring index; inner order is the
audited cycle traversal.  Both are preserved. -/
def relabelRings [DecidableEq V] (enumeration : V ≃ Fin n) (rings : List (List Nat))
    (bounded : ∀ ring ∈ rings, ∀ atom ∈ ring, atom < n) : List (List V) :=
  rings.attach.map fun ring => relabelList enumeration ring.1 (bounded ring.1 ring.2)

/-- Decode an ordered list of rings. -/
def unrelabelRings (enumeration : V ≃ Fin n) (rings : List (List V)) : List (List Nat) :=
  rings.map (unrelabelList enumeration)

/-- Every atom of every decoded ring satisfies the same explicit bounds. -/
def unrelabelRingsBounded (enumeration : V ≃ Fin n) (rings : List (List V)) :
    ∀ ring ∈ unrelabelRings enumeration rings, ∀ atom ∈ ring, atom < n := by
  intro ring member atom atomMember
  rw [unrelabelRings, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact unrelabelList_bounded enumeration supplied atom atomMember

@[simp] theorem relabelRings_length [DecidableEq V] (enumeration : V ≃ Fin n)
    (rings : List (List Nat)) (bounded : ∀ ring ∈ rings, ∀ atom ∈ ring, atom < n) :
    (relabelRings enumeration rings bounded).length = rings.length := by
  simp [relabelRings]

@[simp] theorem unrelabelRings_length (enumeration : V ≃ Fin n) (rings : List (List V)) :
    (unrelabelRings enumeration rings).length = rings.length := by
  simp [unrelabelRings]

/-- Exact recovery of the ordered ring list, preserving every inner cycle traversal. -/
theorem unrelabelRings_relabelRings [DecidableEq V] (enumeration : V ≃ Fin n)
    (rings : List (List Nat)) (bounded : ∀ ring ∈ rings, ∀ atom ∈ ring, atom < n) :
    unrelabelRings enumeration (relabelRings enumeration rings bounded) = rings := by
  unfold unrelabelRings relabelRings
  rw [List.map_map]
  trans rings.attach.map Subtype.val
  · apply List.map_congr_left
    intro ring _
    exact unrelabelList_relabelList enumeration ring.1 (bounded ring.1 ring.2)
  · exact List.attach_map_subtype_val rings

/-- Relabelling a decoded ring list returns the supplied list. -/
theorem relabelRings_unrelabelRings [DecidableEq V] (enumeration : V ≃ Fin n)
    (rings : List (List V)) :
    relabelRings enumeration (unrelabelRings enumeration rings)
        (unrelabelRingsBounded enumeration rings) = rings := by
  unfold relabelRings unrelabelRings
  rw [List.attach_map, List.map_map]
  trans rings.attach.map Subtype.val
  · apply List.map_congr_left
    intro ring _
    exact relabelList_unrelabelList enumeration ring.1
  · exact List.attach_map_subtype_val rings

/-- Mirror of `P93AuthorityRingAssembly`: the ordered ring list and the ordered junction
list. -/
structure SuppliedAuthorityRingAssembly (V : Type*) where
  rings : List (List V)
  junctions : List (SuppliedRingAssemblyJunction V)

/-- Explicit bounds for a whole assembly. -/
def assemblyBoundedIn (n : ℕ) (assembly : P93AuthorityRingAssembly) : Prop :=
  (∀ ring ∈ assembly.rings, ∀ atom ∈ ring, atom < n) ∧
    ∀ junction ∈ assembly.junctions, junctionBoundedIn n junction

/-- Relabel a bounded assembly. -/
def relabelRingAssembly [DecidableEq V] (enumeration : V ≃ Fin n)
    (assembly : P93AuthorityRingAssembly) (bounded : assemblyBoundedIn n assembly) :
    SuppliedAuthorityRingAssembly V where
  rings := relabelRings enumeration assembly.rings bounded.1
  junctions := relabelJunctions enumeration assembly.junctions bounded.2

/-- Decode an assembly to the raw carrier record. -/
def unrelabelRingAssembly (enumeration : V ≃ Fin n)
    (assembly : SuppliedAuthorityRingAssembly V) : P93AuthorityRingAssembly where
  rings := unrelabelRings enumeration assembly.rings
  junctions := unrelabelJunctions enumeration assembly.junctions

/-- Exact recovery of the whole assembly, including ordered rings and ordered junctions. -/
theorem unrelabelRingAssembly_relabelRingAssembly [DecidableEq V] (enumeration : V ≃ Fin n)
    (assembly : P93AuthorityRingAssembly) (bounded : assemblyBoundedIn n assembly) :
    unrelabelRingAssembly enumeration
        (relabelRingAssembly enumeration assembly bounded) = assembly := by
  rcases assembly with ⟨rings, junctions⟩
  simp [unrelabelRingAssembly, relabelRingAssembly,
    unrelabelRings_relabelRings, unrelabelJunctions_relabelJunctions]

/-- Relabelling a decoded assembly returns the supplied record. -/
theorem relabelRingAssembly_unrelabelRingAssembly [DecidableEq V] (enumeration : V ≃ Fin n)
    (assembly : SuppliedAuthorityRingAssembly V) :
    relabelRingAssembly enumeration (unrelabelRingAssembly enumeration assembly)
        ⟨unrelabelRingsBounded enumeration assembly.rings,
          unrelabelJunctionsBounded enumeration assembly.junctions⟩ = assembly := by
  rcases assembly with ⟨rings, junctions⟩
  simp [unrelabelRingAssembly, relabelRingAssembly,
    relabelRings_unrelabelRings, relabelJunctions_unrelabelJunctions]

/-! ## Ring-assembly axial geometry and assignments -/

/-- Mirror of `IndexedAxialGeometryObservation`: the six atom references are relabelled, the
supplied axial sense is copied literally. -/
structure SuppliedAxialGeometryObservation (V : Type*) where
  axisStart : V
  axisEnd : V
  startFirst : V
  startSecond : V
  endFirst : V
  endSecond : V
  sense : StereoSense

/-- Explicit bounds for one indexed axial geometry observation. -/
def axialGeometryBoundedIn (n : ℕ) (record : IndexedAxialGeometryObservation) : Prop :=
  record.axisStart < n ∧ record.axisEnd < n ∧ record.startFirst < n ∧
    record.startSecond < n ∧ record.endFirst < n ∧ record.endSecond < n

/-- Relabel one bounded axial geometry record. -/
def relabelAxialGeometryObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (record : IndexedAxialGeometryObservation)
    (bounded : axialGeometryBoundedIn n record) :
    SuppliedAxialGeometryObservation V where
  axisStart := decodeAtom enumeration record.axisStart bounded.1
  axisEnd := decodeAtom enumeration record.axisEnd bounded.2.1
  startFirst := decodeAtom enumeration record.startFirst bounded.2.2.1
  startSecond := decodeAtom enumeration record.startSecond bounded.2.2.2.1
  endFirst := decodeAtom enumeration record.endFirst bounded.2.2.2.2.1
  endSecond := decodeAtom enumeration record.endSecond bounded.2.2.2.2.2
  sense := record.sense

/-- Decode one axial geometry record. -/
def unrelabelAxialGeometryObservation (enumeration : V ≃ Fin n)
    (record : SuppliedAxialGeometryObservation V) : IndexedAxialGeometryObservation where
  axisStart := encodeAtom enumeration record.axisStart
  axisEnd := encodeAtom enumeration record.axisEnd
  startFirst := encodeAtom enumeration record.startFirst
  startSecond := encodeAtom enumeration record.startSecond
  endFirst := encodeAtom enumeration record.endFirst
  endSecond := encodeAtom enumeration record.endSecond
  sense := record.sense

/-- Exact recovery of one axial geometry record, including the supplied sense. -/
theorem unrelabelAxialGeometryObservation_relabel [DecidableEq V] (enumeration : V ≃ Fin n)
    (record : IndexedAxialGeometryObservation) (bounded : axialGeometryBoundedIn n record) :
    unrelabelAxialGeometryObservation enumeration
        (relabelAxialGeometryObservation enumeration record bounded) = record := by
  rcases record with ⟨axisStart, axisEnd, startFirst, startSecond, endFirst, endSecond, sense⟩
  simp [unrelabelAxialGeometryObservation, relabelAxialGeometryObservation, encodeAtom_decodeAtom]

/-- Relabelling a decoded axial geometry record returns the supplied record. -/
theorem relabelAxialGeometryObservation_unrelabel [DecidableEq V] (enumeration : V ≃ Fin n)
    (record : SuppliedAxialGeometryObservation V) :
    relabelAxialGeometryObservation enumeration
        (unrelabelAxialGeometryObservation enumeration record)
        ⟨encodeAtom_lt enumeration record.axisStart,
          encodeAtom_lt enumeration record.axisEnd,
          encodeAtom_lt enumeration record.startFirst,
          encodeAtom_lt enumeration record.startSecond,
          encodeAtom_lt enumeration record.endFirst,
          encodeAtom_lt enumeration record.endSecond⟩ = record := by
  rcases record with ⟨axisStart, axisEnd, startFirst, startSecond, endFirst, endSecond, sense⟩
  simp [unrelabelAxialGeometryObservation, relabelAxialGeometryObservation, decodeAtom_encodeAtom]

/-- Mirror of `P93RingAssemblyAxisAssignment`. -/
structure SuppliedRingAssemblyAxisAssignment (V : Type*) where
  junction : SuppliedRingAssemblyJunction V
  record : SuppliedAxialGeometryObservation V
  citation : P93AuthorityCitationToken
  cipDescriptor : AxialDescriptor
  preferredDescriptor : RingAssemblyAxisDescriptor
  generalDescriptor : RingAssemblyAxisDescriptor

/-- Explicit bounds for one axis assignment. -/
def axisAssignmentBoundedIn (n : ℕ) (assignment : P93RingAssemblyAxisAssignment) : Prop :=
  junctionBoundedIn n assignment.junction ∧ axialGeometryBoundedIn n assignment.record

/-- Relabel one bounded axis assignment. -/
def relabelRingAssemblyAxisAssignment [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignment : P93RingAssemblyAxisAssignment)
    (bounded : axisAssignmentBoundedIn n assignment) :
    SuppliedRingAssemblyAxisAssignment V where
  junction := relabelRingAssemblyJunction enumeration assignment.junction bounded.1
  record := relabelAxialGeometryObservation enumeration assignment.record bounded.2
  citation := assignment.citation
  cipDescriptor := assignment.cipDescriptor
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor := assignment.generalDescriptor

/-- Decode one axis assignment. -/
def unrelabelRingAssemblyAxisAssignment (enumeration : V ≃ Fin n)
    (assignment : SuppliedRingAssemblyAxisAssignment V) :
    P93RingAssemblyAxisAssignment where
  junction := unrelabelRingAssemblyJunction enumeration assignment.junction
  record := unrelabelAxialGeometryObservation enumeration assignment.record
  citation := assignment.citation
  cipDescriptor := assignment.cipDescriptor
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor := assignment.generalDescriptor

/-- Exact recovery of one axis assignment. -/
theorem unrelabelRingAssemblyAxisAssignment_relabel [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignment : P93RingAssemblyAxisAssignment)
    (bounded : axisAssignmentBoundedIn n assignment) :
    unrelabelRingAssemblyAxisAssignment enumeration
        (relabelRingAssemblyAxisAssignment enumeration assignment bounded) = assignment := by
  rcases assignment with ⟨junction, record, citation, cipDescriptor, preferredDescriptor,
    generalDescriptor⟩
  simp [unrelabelRingAssemblyAxisAssignment, relabelRingAssemblyAxisAssignment,
    unrelabelRingAssemblyJunction_relabel, unrelabelAxialGeometryObservation_relabel]

/-- Relabelling a decoded axis assignment returns the supplied record. -/
theorem relabelRingAssemblyAxisAssignment_unrelabel [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignment : SuppliedRingAssemblyAxisAssignment V) :
    relabelRingAssemblyAxisAssignment enumeration
        (unrelabelRingAssemblyAxisAssignment enumeration assignment)
        ⟨⟨encodeAtom_lt enumeration assignment.junction.leftAtom,
            encodeAtom_lt enumeration assignment.junction.rightAtom⟩,
          ⟨encodeAtom_lt enumeration assignment.record.axisStart,
            encodeAtom_lt enumeration assignment.record.axisEnd,
            encodeAtom_lt enumeration assignment.record.startFirst,
            encodeAtom_lt enumeration assignment.record.startSecond,
            encodeAtom_lt enumeration assignment.record.endFirst,
            encodeAtom_lt enumeration assignment.record.endSecond⟩⟩ = assignment := by
  rcases assignment with ⟨junction, record, citation, cipDescriptor, preferredDescriptor,
    generalDescriptor⟩
  rcases junction with ⟨leftRingIndex, rightRingIndex, leftAtom, rightAtom⟩
  rcases record with ⟨axisStart, axisEnd, startFirst, startSecond, endFirst, endSecond, sense⟩
  simp [unrelabelRingAssemblyAxisAssignment, relabelRingAssemblyAxisAssignment,
    unrelabelRingAssemblyJunction, relabelRingAssemblyJunction,
    unrelabelAxialGeometryObservation, relabelAxialGeometryObservation,
    decodeAtom_encodeAtom]

/-- Relabel an ordered list of bounded axis assignments. -/
def relabelRingAssemblyAxisAssignments [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List P93RingAssemblyAxisAssignment)
    (bounded : ∀ assignment ∈ assignments, axisAssignmentBoundedIn n assignment) :
    List (SuppliedRingAssemblyAxisAssignment V) :=
  assignments.attach.map fun assignment =>
    relabelRingAssemblyAxisAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)

/-- Decode an ordered list of axis assignments. -/
def unrelabelRingAssemblyAxisAssignments (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyAxisAssignment V)) :
    List P93RingAssemblyAxisAssignment :=
  assignments.map (unrelabelRingAssemblyAxisAssignment enumeration)

/-- Every decoded axis assignment satisfies the same explicit bounds. -/
def unrelabelRingAssemblyAxisAssignmentsBounded (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyAxisAssignment V)) :
    ∀ assignment ∈ unrelabelRingAssemblyAxisAssignments enumeration assignments,
      axisAssignmentBoundedIn n assignment := by
  intro assignment member
  rw [unrelabelRingAssemblyAxisAssignments, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact ⟨⟨encodeAtom_lt enumeration supplied.junction.leftAtom,
      encodeAtom_lt enumeration supplied.junction.rightAtom⟩,
    ⟨encodeAtom_lt enumeration supplied.record.axisStart,
      encodeAtom_lt enumeration supplied.record.axisEnd,
      encodeAtom_lt enumeration supplied.record.startFirst,
      encodeAtom_lt enumeration supplied.record.startSecond,
      encodeAtom_lt enumeration supplied.record.endFirst,
      encodeAtom_lt enumeration supplied.record.endSecond⟩⟩

@[simp] theorem relabelRingAssemblyAxisAssignments_length [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignments : List P93RingAssemblyAxisAssignment)
    (bounded : ∀ assignment ∈ assignments, axisAssignmentBoundedIn n assignment) :
    (relabelRingAssemblyAxisAssignments enumeration assignments bounded).length =
      assignments.length := by
  simp [relabelRingAssemblyAxisAssignments]

@[simp] theorem unrelabelRingAssemblyAxisAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyAxisAssignment V)) :
    (unrelabelRingAssemblyAxisAssignments enumeration assignments).length =
      assignments.length := by
  simp [unrelabelRingAssemblyAxisAssignments]

/-- Exact recovery of the ordered axis-assignment list. -/
theorem unrelabelRingAssemblyAxisAssignments_relabel [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List P93RingAssemblyAxisAssignment)
    (bounded : ∀ assignment ∈ assignments, axisAssignmentBoundedIn n assignment) :
    unrelabelRingAssemblyAxisAssignments enumeration
        (relabelRingAssemblyAxisAssignments enumeration assignments bounded) =
      assignments := by
  unfold unrelabelRingAssemblyAxisAssignments relabelRingAssemblyAxisAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelRingAssemblyAxisAssignment_relabel enumeration assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

/-- Relabelling a decoded axis-assignment list returns the supplied list. -/
theorem relabelRingAssemblyAxisAssignments_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyAxisAssignment V)) :
    relabelRingAssemblyAxisAssignments enumeration
        (unrelabelRingAssemblyAxisAssignments enumeration assignments)
        (unrelabelRingAssemblyAxisAssignmentsBounded enumeration assignments) =
      assignments := by
  unfold relabelRingAssemblyAxisAssignments unrelabelRingAssemblyAxisAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelRingAssemblyAxisAssignment_unrelabel enumeration assignment.1
  · exact List.attach_map_subtype_val assignments

/-- Mirror of `P93RingAssemblyCenterAssignment`. -/
structure SuppliedRingAssemblyCenterAssignment (V : Type*) where
  center : V
  citation : P93AuthorityCitationToken
  preferredDescriptor : RingAssemblyCenterDescriptor
  generalDescriptor? : Option RingAssemblyCenterDescriptor

/-- Explicit bounds for one center assignment. -/
def centerAssignmentBoundedIn (n : ℕ)
    (assignment : P93RingAssemblyCenterAssignment) : Prop :=
  assignment.center < n

/-- Relabel one bounded center assignment. -/
def relabelRingAssemblyCenterAssignment [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignment : P93RingAssemblyCenterAssignment)
    (bounded : centerAssignmentBoundedIn n assignment) :
    SuppliedRingAssemblyCenterAssignment V where
  center := decodeAtom enumeration assignment.center bounded
  citation := assignment.citation
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor? := assignment.generalDescriptor?

/-- Decode one center assignment. -/
def unrelabelRingAssemblyCenterAssignment (enumeration : V ≃ Fin n)
    (assignment : SuppliedRingAssemblyCenterAssignment V) :
    P93RingAssemblyCenterAssignment where
  center := encodeAtom enumeration assignment.center
  citation := assignment.citation
  preferredDescriptor := assignment.preferredDescriptor
  generalDescriptor? := assignment.generalDescriptor?

/-- Exact recovery of one center assignment, including the optional general descriptor. -/
theorem unrelabelRingAssemblyCenterAssignment_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignment : P93RingAssemblyCenterAssignment)
    (bounded : centerAssignmentBoundedIn n assignment) :
    unrelabelRingAssemblyCenterAssignment enumeration
        (relabelRingAssemblyCenterAssignment enumeration assignment bounded) =
      assignment := by
  rcases assignment with ⟨center, citation, preferredDescriptor, generalDescriptor?⟩
  simp [unrelabelRingAssemblyCenterAssignment, relabelRingAssemblyCenterAssignment,
    encodeAtom_decodeAtom]

/-- Relabelling a decoded center assignment returns the supplied record. -/
theorem relabelRingAssemblyCenterAssignment_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignment : SuppliedRingAssemblyCenterAssignment V) :
    relabelRingAssemblyCenterAssignment enumeration
        (unrelabelRingAssemblyCenterAssignment enumeration assignment)
        (encodeAtom_lt enumeration assignment.center) = assignment := by
  rcases assignment with ⟨center, citation, preferredDescriptor, generalDescriptor?⟩
  simp [unrelabelRingAssemblyCenterAssignment, relabelRingAssemblyCenterAssignment,
    decodeAtom_encodeAtom]

/-- Relabel an ordered list of bounded center assignments. -/
def relabelRingAssemblyCenterAssignments [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List P93RingAssemblyCenterAssignment)
    (bounded : ∀ assignment ∈ assignments, centerAssignmentBoundedIn n assignment) :
    List (SuppliedRingAssemblyCenterAssignment V) :=
  assignments.attach.map fun assignment =>
    relabelRingAssemblyCenterAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)

/-- Decode an ordered list of center assignments. -/
def unrelabelRingAssemblyCenterAssignments (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyCenterAssignment V)) :
    List P93RingAssemblyCenterAssignment :=
  assignments.map (unrelabelRingAssemblyCenterAssignment enumeration)

/-- Every decoded center assignment satisfies the same explicit bounds. -/
def unrelabelRingAssemblyCenterAssignmentsBounded (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyCenterAssignment V)) :
    ∀ assignment ∈ unrelabelRingAssemblyCenterAssignments enumeration assignments,
      centerAssignmentBoundedIn n assignment := by
  intro assignment member
  rw [unrelabelRingAssemblyCenterAssignments, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact encodeAtom_lt enumeration supplied.center

@[simp] theorem relabelRingAssemblyCenterAssignments_length [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignments : List P93RingAssemblyCenterAssignment)
    (bounded : ∀ assignment ∈ assignments, centerAssignmentBoundedIn n assignment) :
    (relabelRingAssemblyCenterAssignments enumeration assignments bounded).length =
      assignments.length := by
  simp [relabelRingAssemblyCenterAssignments]

@[simp] theorem unrelabelRingAssemblyCenterAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyCenterAssignment V)) :
    (unrelabelRingAssemblyCenterAssignments enumeration assignments).length =
      assignments.length := by
  simp [unrelabelRingAssemblyCenterAssignments]

/-- Exact recovery of the ordered center-assignment list. -/
theorem unrelabelRingAssemblyCenterAssignments_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignments : List P93RingAssemblyCenterAssignment)
    (bounded : ∀ assignment ∈ assignments, centerAssignmentBoundedIn n assignment) :
    unrelabelRingAssemblyCenterAssignments enumeration
        (relabelRingAssemblyCenterAssignments enumeration assignments bounded) =
      assignments := by
  unfold unrelabelRingAssemblyCenterAssignments relabelRingAssemblyCenterAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelRingAssemblyCenterAssignment_relabel enumeration assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

/-- Relabelling a decoded center-assignment list returns the supplied list. -/
theorem relabelRingAssemblyCenterAssignments_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyCenterAssignment V)) :
    relabelRingAssemblyCenterAssignments enumeration
        (unrelabelRingAssemblyCenterAssignments enumeration assignments)
        (unrelabelRingAssemblyCenterAssignmentsBounded enumeration assignments) =
      assignments := by
  unfold relabelRingAssemblyCenterAssignments unrelabelRingAssemblyCenterAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelRingAssemblyCenterAssignment_unrelabel enumeration assignment.1
  · exact List.attach_map_subtype_val assignments

/-- Mirror of `P93RingAssemblyDoubleBondAssignment`.  The ring index is a ring-list position and
is retained; the two bond endpoints are relabelled. -/
structure SuppliedRingAssemblyDoubleBondAssignment (V : Type*) where
  ringIndex : Nat
  first : V
  second : V
  citation : P93AuthorityCitationToken
  descriptor : BlueBookP93.Acyclic.Descriptor

/-- Explicit bounds for one double-bond assignment. -/
def doubleBondAssignmentBoundedIn (n : ℕ)
    (assignment : P93RingAssemblyDoubleBondAssignment) : Prop :=
  assignment.first < n ∧ assignment.second < n

/-- Relabel one bounded double-bond assignment. -/
def relabelRingAssemblyDoubleBondAssignment [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignment : P93RingAssemblyDoubleBondAssignment)
    (bounded : doubleBondAssignmentBoundedIn n assignment) :
    SuppliedRingAssemblyDoubleBondAssignment V where
  ringIndex := assignment.ringIndex
  first := decodeAtom enumeration assignment.first bounded.1
  second := decodeAtom enumeration assignment.second bounded.2
  citation := assignment.citation
  descriptor := assignment.descriptor

/-- Decode one double-bond assignment. -/
def unrelabelRingAssemblyDoubleBondAssignment (enumeration : V ≃ Fin n)
    (assignment : SuppliedRingAssemblyDoubleBondAssignment V) :
    P93RingAssemblyDoubleBondAssignment where
  ringIndex := assignment.ringIndex
  first := encodeAtom enumeration assignment.first
  second := encodeAtom enumeration assignment.second
  citation := assignment.citation
  descriptor := assignment.descriptor

/-- Exact recovery of one double-bond assignment, including its ring index. -/
theorem unrelabelRingAssemblyDoubleBondAssignment_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignment : P93RingAssemblyDoubleBondAssignment)
    (bounded : doubleBondAssignmentBoundedIn n assignment) :
    unrelabelRingAssemblyDoubleBondAssignment enumeration
        (relabelRingAssemblyDoubleBondAssignment enumeration assignment bounded) =
      assignment := by
  rcases assignment with ⟨ringIndex, first, second, citation, descriptor⟩
  simp [unrelabelRingAssemblyDoubleBondAssignment, relabelRingAssemblyDoubleBondAssignment,
    encodeAtom_decodeAtom]

/-- Relabelling a decoded double-bond assignment returns the supplied record. -/
theorem relabelRingAssemblyDoubleBondAssignment_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignment : SuppliedRingAssemblyDoubleBondAssignment V) :
    relabelRingAssemblyDoubleBondAssignment enumeration
        (unrelabelRingAssemblyDoubleBondAssignment enumeration assignment)
        ⟨encodeAtom_lt enumeration assignment.first,
          encodeAtom_lt enumeration assignment.second⟩ = assignment := by
  rcases assignment with ⟨ringIndex, first, second, citation, descriptor⟩
  simp [unrelabelRingAssemblyDoubleBondAssignment, relabelRingAssemblyDoubleBondAssignment,
    decodeAtom_encodeAtom]

/-- Relabel an ordered list of bounded double-bond assignments. -/
def relabelRingAssemblyDoubleBondAssignments [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List P93RingAssemblyDoubleBondAssignment)
    (bounded : ∀ assignment ∈ assignments, doubleBondAssignmentBoundedIn n assignment) :
    List (SuppliedRingAssemblyDoubleBondAssignment V) :=
  assignments.attach.map fun assignment =>
    relabelRingAssemblyDoubleBondAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)

/-- Decode an ordered list of double-bond assignments. -/
def unrelabelRingAssemblyDoubleBondAssignments (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyDoubleBondAssignment V)) :
    List P93RingAssemblyDoubleBondAssignment :=
  assignments.map (unrelabelRingAssemblyDoubleBondAssignment enumeration)

/-- Every decoded double-bond assignment satisfies the same explicit bounds. -/
def unrelabelRingAssemblyDoubleBondAssignmentsBounded (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyDoubleBondAssignment V)) :
    ∀ assignment ∈ unrelabelRingAssemblyDoubleBondAssignments enumeration assignments,
      doubleBondAssignmentBoundedIn n assignment := by
  intro assignment member
  rw [unrelabelRingAssemblyDoubleBondAssignments, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact ⟨encodeAtom_lt enumeration supplied.first, encodeAtom_lt enumeration supplied.second⟩

@[simp] theorem relabelRingAssemblyDoubleBondAssignments_length [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignments : List P93RingAssemblyDoubleBondAssignment)
    (bounded : ∀ assignment ∈ assignments, doubleBondAssignmentBoundedIn n assignment) :
    (relabelRingAssemblyDoubleBondAssignments enumeration assignments bounded).length =
      assignments.length := by
  simp [relabelRingAssemblyDoubleBondAssignments]

@[simp] theorem unrelabelRingAssemblyDoubleBondAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyDoubleBondAssignment V)) :
    (unrelabelRingAssemblyDoubleBondAssignments enumeration assignments).length =
      assignments.length := by
  simp [unrelabelRingAssemblyDoubleBondAssignments]

/-- Exact recovery of the ordered double-bond-assignment list. -/
theorem unrelabelRingAssemblyDoubleBondAssignments_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (assignments : List P93RingAssemblyDoubleBondAssignment)
    (bounded : ∀ assignment ∈ assignments, doubleBondAssignmentBoundedIn n assignment) :
    unrelabelRingAssemblyDoubleBondAssignments enumeration
        (relabelRingAssemblyDoubleBondAssignments enumeration assignments bounded) =
      assignments := by
  unfold unrelabelRingAssemblyDoubleBondAssignments
    relabelRingAssemblyDoubleBondAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelRingAssemblyDoubleBondAssignment_relabel enumeration assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

/-- Relabelling a decoded double-bond-assignment list returns the supplied list. -/
theorem relabelRingAssemblyDoubleBondAssignments_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedRingAssemblyDoubleBondAssignment V)) :
    relabelRingAssemblyDoubleBondAssignments enumeration
        (unrelabelRingAssemblyDoubleBondAssignments enumeration assignments)
        (unrelabelRingAssemblyDoubleBondAssignmentsBounded enumeration assignments) =
      assignments := by
  unfold relabelRingAssemblyDoubleBondAssignments
    unrelabelRingAssemblyDoubleBondAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelRingAssemblyDoubleBondAssignment_unrelabel enumeration assignment.1
  · exact List.attach_map_subtype_val assignments

/-! ## Bounds derived from the assembly predicates -/

/-- Ring atoms of an assembly are bounded: every ring satisfies the closed-cycle predicate, whose
third conjunct is the explicit source atom bound. -/
theorem assemblyBoundedIn_of_mechanicallyValidFor
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed)
    (mechanical : assembly.MechanicallyValidFor source) :
    assemblyBoundedIn source.molecule.atomCount assembly := by
  rcases mechanical with ⟨_two, _nodup, cycles, _disjoint, _ne, _junctionNodup,
    junctionValid, _connected⟩
  constructor
  · intro ring member atom atomMember
    exact (cycles ring member).2.2.1 atom atomMember
  · intro junction member
    rcases junctionValid junction member with
      ⟨_indexOrder, _leftRing, _rightRing, _leftLookup, _rightLookup,
        _leftMember, _rightMember, bond⟩
    exact binaryBond_atoms_bounded source structurallyWellFormed bond

/-- Bounds of a whole decoded assembly. -/
def unrelabelRingAssemblyBounded (enumeration : V ≃ Fin n)
    (assembly : SuppliedAuthorityRingAssembly V) :
    assemblyBoundedIn n (unrelabelRingAssembly enumeration assembly) :=
  ⟨unrelabelRingsBounded enumeration assembly.rings,
    unrelabelJunctionsBounded enumeration assembly.junctions⟩

/-- Bounds of a valid axis assignment.  The junction endpoints come from the assembly's mechanical
validity; the axial record's six references are its axis endpoints (equal to the junction
endpoints by frame validity) and the four reference atoms, which lie in the two named rings. -/
theorem axisAssignmentBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93RingAssemblyAuthorityPolicy)
    (assembly : P93AuthorityRingAssembly)
    (result : ChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed)
    (mechanical : assembly.MechanicallyValidFor source)
    (assignment : P93RingAssemblyAxisAssignment)
    (valid : assignment.ValidFor policy source assembly result spatial) :
    axisAssignmentBoundedIn source.molecule.atomCount assignment := by
  rcases valid with ⟨junctionMember, _eligible, frameValid, _cip, _rational, _preferred,
    _general, _preferredValid, _descriptorsObserved, _citationValid, _citationAuthorized⟩
  rcases frameValid with
    ⟨axisStartEq, axisEndEq, leftRing, rightRing, leftLookup, rightLookup,
      startFirstMember, startSecondMember, endFirstMember, endSecondMember,
      _startDistinct, _endDistinct, _startFirstBond, _startSecondBond, _endFirstBond,
      _endSecondBond⟩
  have bounded := assemblyBoundedIn_of_mechanicallyValidFor source assembly
    structurallyWellFormed mechanical
  have junctionBounded : junctionBoundedIn source.molecule.atomCount assignment.junction :=
    bounded.2 assignment.junction junctionMember
  have leftBounded : ∀ atom ∈ leftRing, atom < source.molecule.atomCount :=
    bounded.1 leftRing (List.mem_of_getElem? leftLookup)
  have rightBounded : ∀ atom ∈ rightRing, atom < source.molecule.atomCount :=
    bounded.1 rightRing (List.mem_of_getElem? rightLookup)
  refine ⟨junctionBounded, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [axisStartEq]
    exact junctionBounded.1
  · rw [axisEndEq]
    exact junctionBounded.2
  · exact leftBounded assignment.record.startFirst startFirstMember
  · exact leftBounded assignment.record.startSecond startSecondMember
  · exact rightBounded assignment.record.endFirst endFirstMember
  · exact rightBounded assignment.record.endSecond endSecondMember

/-- Bounds of a valid center assignment: the center atom is in range by the physical-unit
certificate carried in the assignment's own `ValidFor`. -/
theorem centerAssignmentBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93RingAssemblyAuthorityPolicy)
    (assembly : P93AuthorityRingAssembly)
    (assignment : P93RingAssemblyCenterAssignment)
    (valid : assignment.ValidFor policy source assembly) :
    centerAssignmentBoundedIn source.molecule.atomCount assignment := by
  rcases valid with ⟨_inExactlyOneRing, unitValid, _eligible, _preferred, _cipAuthorized,
    _citationValid, _citationAuthorized, _general⟩
  exact unitValid.1

/-- Bounds of a valid double-bond assignment: both endpoints are participants of a genuine binary
bond, so the source structural certificate bounds them. -/
theorem doubleBondAssignmentBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (policy : P93RingAssemblyAuthorityPolicy)
    (assembly : P93AuthorityRingAssembly)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed)
    (assignment : P93RingAssemblyDoubleBondAssignment)
    (valid : assignment.ValidFor policy source assembly) :
    doubleBondAssignmentBoundedIn source.molecule.atomCount assignment := by
  rcases valid with ⟨bondInRing, _required, _ez, _descriptorAuthorized, _citationValid,
    _citationAuthorized⟩
  rcases bondInRing with ⟨_ordered, _ring, _lookup, _firstMember, _secondMember, _edge, bond⟩
  exact binaryBond_atoms_bounded source structurallyWellFormed bond

/-! ## The three ring-assembly observation records -/

/-- Mirror of `P93RingAssemblyAxesAuthorityObservation`.  The normalization result is replaced by
its independent raw parsed syntax `parsed`; the decoder recomputes
`normalization := normalizeRawMolecule parsed`.  The coordinate channel is the total function used
by `OrganicFiniteSource.encodeSpatial?`. -/
structure SuppliedRingAssemblyAxesAuthorityObservation (V : Type*)
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : SuppliedAuthorityRingAssembly V
  parsed : RawMolecule
  spatial : V → CartesianPoint3
  assignments : List (SuppliedRingAssemblyAxisAssignment V)

/-- Explicit bounds for one axes observation: the assembly, the coordinate-list length and every
axis assignment. -/
def axesObservationBoundedIn (n : ℕ) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy) : Prop :=
  assemblyBoundedIn n observation.assembly ∧
    observation.spatial.positions.length = n ∧
    ∀ assignment ∈ observation.assignments, axisAssignmentBoundedIn n assignment

/-- Relabel one bounded axes observation.  The raw parsed syntax and every non-atom field are
copied; the assembly, coordinate list and axis assignments are relabelled. -/
def relabelRingAssemblyAxesObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (bounded : axesObservationBoundedIn n policy observation) :
    SuppliedRingAssemblyAxesAuthorityObservation V policy where
  assembly := relabelRingAssembly enumeration observation.assembly bounded.1
  parsed := observation.normalization.parsed
  spatial := relabelSpatial enumeration observation.spatial bounded.2.1
  assignments := relabelRingAssemblyAxisAssignments enumeration observation.assignments bounded.2.2

/-- Decode one axes observation, recomputing the normalization result from its parsed syntax. -/
def unrelabelRingAssemblyAxesObservation (enumeration : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyAxesAuthorityObservation V policy) :
    P93RingAssemblyAxesAuthorityObservation policy where
  assembly := unrelabelRingAssembly enumeration observation.assembly
  normalization := normalizeRawMolecule observation.parsed
  spatial := unrelabelSpatial enumeration observation.spatial
  assignments := unrelabelRingAssemblyAxisAssignments enumeration observation.assignments

/-- The normalization result recomputes its parsed component definitionally. -/
theorem normalizeRawMolecule_parsed (mol : RawMolecule) :
    (normalizeRawMolecule mol).parsed = mol.normalizeUnspecifiedBonds := rfl

/-- The explicit native-side condition under which the recomputed normalization is stable: the
stored independent raw syntax is already in its unspecified-bond-normalized form.  This is not
assumed anywhere as a validity claim; it is a stated hypothesis of the native-side inverse. -/
def RawMoleculeNormalized (mol : RawMolecule) : Prop :=
  mol.normalizeUnspecifiedBonds = mol

/-- Exact recovery of one axes observation.  The normalization equality is exactly the fourth
conjunct of the carrier's own `ValidFor`; it is required here because the record's normalization is
recomputed from its parsed syntax. -/
theorem unrelabelRingAssemblyAxesObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (bounded : axesObservationBoundedIn n policy observation)
    (normalizationFixed :
      observation.normalization = normalizeRawMolecule observation.normalization.parsed) :
    unrelabelRingAssemblyAxesObservation enumeration policy
        (relabelRingAssemblyAxesObservation enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨assembly, normalization, spatial, assignments⟩
  have normalizationEq : normalizeRawMolecule normalization.parsed = normalization :=
    normalizationFixed.symm
  simp [relabelRingAssemblyAxesObservation, unrelabelRingAssemblyAxesObservation,
    unrelabelRingAssembly_relabelRingAssembly,
    unrelabelRingAssemblyAxisAssignments_relabel,
    unrelabelSpatial_relabelSpatial, normalizationEq]

/-- Bounds of a decoded axes observation. -/
def unrelabelRingAssemblyAxesObservationBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyAxesAuthorityObservation V policy) :
    axesObservationBoundedIn n policy
      (unrelabelRingAssemblyAxesObservation enumeration policy observation) :=
  ⟨unrelabelRingAssemblyBounded enumeration observation.assembly,
    by simp [unrelabelRingAssemblyAxesObservation, unrelabelSpatial],
    unrelabelRingAssemblyAxisAssignmentsBounded enumeration observation.assignments⟩

/-- Relabelling a decoded axes observation returns the supplied record.  The extra hypothesis
records that the stored raw syntax is already in its normalized form; without it the decoder's
recomputed normalization would be normalized a second time. -/
theorem relabelRingAssemblyAxesObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyAxesAuthorityObservation V policy)
    (rawSyntaxNormalized : RawMoleculeNormalized observation.parsed) :
    relabelRingAssemblyAxesObservation enumeration policy
        (unrelabelRingAssemblyAxesObservation enumeration policy observation)
        (unrelabelRingAssemblyAxesObservationBounded enumeration policy observation) =
      observation := by
  rcases observation with ⟨assembly, parsed, spatial, assignments⟩
  have idempotent : parsed.normalizeUnspecifiedBonds = parsed := by
    simpa [RawMoleculeNormalized] using rawSyntaxNormalized
  simp [relabelRingAssemblyAxesObservation, unrelabelRingAssemblyAxesObservation,
    relabelRingAssembly_unrelabelRingAssembly,
    relabelRingAssemblyAxisAssignments_unrelabel,
    relabelSpatial_unrelabelSpatial, normalizeRawMolecule_parsed, idempotent]

/-- Mirror of `P93RingAssemblyCentersAuthorityObservation`. -/
structure SuppliedRingAssemblyCentersAuthorityObservation (V : Type*)
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : SuppliedAuthorityRingAssembly V
  assignments : List (SuppliedRingAssemblyCenterAssignment V)

/-- Explicit bounds for one centers observation. -/
def centersObservationBoundedIn (n : ℕ) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyCentersAuthorityObservation policy) : Prop :=
  assemblyBoundedIn n observation.assembly ∧
    ∀ assignment ∈ observation.assignments, centerAssignmentBoundedIn n assignment

/-- Relabel one bounded centers observation. -/
def relabelRingAssemblyCentersObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyCentersAuthorityObservation policy)
    (bounded : centersObservationBoundedIn n policy observation) :
    SuppliedRingAssemblyCentersAuthorityObservation V policy where
  assembly := relabelRingAssembly enumeration observation.assembly bounded.1
  assignments := relabelRingAssemblyCenterAssignments enumeration observation.assignments bounded.2

/-- Decode one centers observation. -/
def unrelabelRingAssemblyCentersObservation (enumeration : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyCentersAuthorityObservation V policy) :
    P93RingAssemblyCentersAuthorityObservation policy where
  assembly := unrelabelRingAssembly enumeration observation.assembly
  assignments := unrelabelRingAssemblyCenterAssignments enumeration observation.assignments

/-- Exact recovery of one centers observation, including the ordered assignment list. -/
theorem unrelabelRingAssemblyCentersObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyCentersAuthorityObservation policy)
    (bounded : centersObservationBoundedIn n policy observation) :
    unrelabelRingAssemblyCentersObservation enumeration policy
        (relabelRingAssemblyCentersObservation enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨assembly, assignments⟩
  simp [relabelRingAssemblyCentersObservation, unrelabelRingAssemblyCentersObservation,
    unrelabelRingAssembly_relabelRingAssembly,
    unrelabelRingAssemblyCenterAssignments_relabel]

/-- Bounds of a decoded centers observation. -/
def unrelabelRingAssemblyCentersObservationBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyCentersAuthorityObservation V policy) :
    centersObservationBoundedIn n policy
      (unrelabelRingAssemblyCentersObservation enumeration policy observation) :=
  ⟨unrelabelRingAssemblyBounded enumeration observation.assembly,
    unrelabelRingAssemblyCenterAssignmentsBounded enumeration observation.assignments⟩

/-- Relabelling a decoded centers observation returns the supplied record. -/
theorem relabelRingAssemblyCentersObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyCentersAuthorityObservation V policy) :
    relabelRingAssemblyCentersObservation enumeration policy
        (unrelabelRingAssemblyCentersObservation enumeration policy observation)
        (unrelabelRingAssemblyCentersObservationBounded enumeration policy observation) =
      observation := by
  rcases observation with ⟨assembly, assignments⟩
  simp [relabelRingAssemblyCentersObservation, unrelabelRingAssemblyCentersObservation,
    relabelRingAssembly_unrelabelRingAssembly,
    relabelRingAssemblyCenterAssignments_unrelabel]

/-- Mirror of `P93RingAssemblyDoubleBondsAuthorityObservation`. -/
structure SuppliedRingAssemblyDoubleBondsAuthorityObservation (V : Type*)
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : SuppliedAuthorityRingAssembly V
  assignments : List (SuppliedRingAssemblyDoubleBondAssignment V)

/-- Explicit bounds for one double-bonds observation. -/
def doubleBondsObservationBoundedIn (n : ℕ) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy) : Prop :=
  assemblyBoundedIn n observation.assembly ∧
    ∀ assignment ∈ observation.assignments, doubleBondAssignmentBoundedIn n assignment

/-- Relabel one bounded double-bonds observation. -/
def relabelRingAssemblyDoubleBondsObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy)
    (bounded : doubleBondsObservationBoundedIn n policy observation) :
    SuppliedRingAssemblyDoubleBondsAuthorityObservation V policy where
  assembly := relabelRingAssembly enumeration observation.assembly bounded.1
  assignments := relabelRingAssemblyDoubleBondAssignments enumeration observation.assignments
    bounded.2

/-- Decode one double-bonds observation. -/
def unrelabelRingAssemblyDoubleBondsObservation (enumeration : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyDoubleBondsAuthorityObservation V policy) :
    P93RingAssemblyDoubleBondsAuthorityObservation policy where
  assembly := unrelabelRingAssembly enumeration observation.assembly
  assignments := unrelabelRingAssemblyDoubleBondAssignments enumeration observation.assignments

/-- Exact recovery of one double-bonds observation, including its ring indices. -/
theorem unrelabelRingAssemblyDoubleBondsObservation_relabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy)
    (bounded : doubleBondsObservationBoundedIn n policy observation) :
    unrelabelRingAssemblyDoubleBondsObservation enumeration policy
        (relabelRingAssemblyDoubleBondsObservation enumeration policy observation bounded) =
      observation := by
  rcases observation with ⟨assembly, assignments⟩
  simp [relabelRingAssemblyDoubleBondsObservation,
    unrelabelRingAssemblyDoubleBondsObservation,
    unrelabelRingAssembly_relabelRingAssembly,
    unrelabelRingAssemblyDoubleBondAssignments_relabel]

/-- Bounds of a decoded double-bonds observation. -/
def unrelabelRingAssemblyDoubleBondsObservationBounded [DecidableEq V]
    (enumeration : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyDoubleBondsAuthorityObservation V policy) :
    doubleBondsObservationBoundedIn n policy
      (unrelabelRingAssemblyDoubleBondsObservation enumeration policy observation) :=
  ⟨unrelabelRingAssemblyBounded enumeration observation.assembly,
    unrelabelRingAssemblyDoubleBondAssignmentsBounded enumeration observation.assignments⟩

/-- Relabelling a decoded double-bonds observation returns the supplied record. -/
theorem relabelRingAssemblyDoubleBondsObservation_unrelabel [DecidableEq V]
    (enumeration : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedRingAssemblyDoubleBondsAuthorityObservation V policy) :
    relabelRingAssemblyDoubleBondsObservation enumeration policy
        (unrelabelRingAssemblyDoubleBondsObservation enumeration policy observation)
        (unrelabelRingAssemblyDoubleBondsObservationBounded enumeration policy observation) =
      observation := by
  rcases observation with ⟨assembly, assignments⟩
  simp [relabelRingAssemblyDoubleBondsObservation,
    unrelabelRingAssemblyDoubleBondsObservation,
    relabelRingAssembly_unrelabelRingAssembly,
    relabelRingAssemblyDoubleBondAssignments_unrelabel]

/-! ## The ring-assembly tagged sum -/

/-- The source-side tagged sum: exactly the three pre-existing ring-assembly observation records. -/
inductive SourceRingAssemblyObservation (policy : P93RingAssemblyAuthorityPolicy) where
  | axes (observation : P93RingAssemblyAxesAuthorityObservation policy)
  | centers (observation : P93RingAssemblyCentersAuthorityObservation policy)
  | doubleBonds (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy)

/-- The native tagged payload: one constructor per pre-existing ring-assembly record. -/
inductive RingAssemblyObservation (V : Type*) (policy : P93RingAssemblyAuthorityPolicy) where
  | axes (observation : SuppliedRingAssemblyAxesAuthorityObservation V policy)
  | centers (observation : SuppliedRingAssemblyCentersAuthorityObservation V policy)
  | doubleBonds (observation : SuppliedRingAssemblyDoubleBondsAuthorityObservation V policy)

/-- Explicit bounds for a tagged source observation. -/
def SourceRingAssemblyObservation.BoundedIn (n : ℕ) :
    SourceRingAssemblyObservation policy → Prop
  | .axes observation => axesObservationBoundedIn n policy observation
  | .centers observation => centersObservationBoundedIn n policy observation
  | .doubleBonds observation => doubleBondsObservationBoundedIn n policy observation

/-- The source-side normalization-recomputation condition.  It is exactly the fourth conjunct of
`P93RingAssemblyAxesAuthorityObservation.ValidFor` for the axes row and vacuous for the other two. -/
def SourceRingAssemblyObservation.NormalizationFixed :
    SourceRingAssemblyObservation policy → Prop
  | .axes observation =>
      observation.normalization = normalizeRawMolecule observation.normalization.parsed
  | .centers _ => True
  | .doubleBonds _ => True

/-- The native-side raw-syntax condition; vacuous except for the axes row. -/
def RingAssemblyObservation.RawSyntaxNormalized :
    RingAssemblyObservation V policy → Prop
  | .axes observation => RawMoleculeNormalized observation.parsed
  | .centers _ => True
  | .doubleBonds _ => True

/-- Relabel one tagged source observation, constructor by constructor. -/
def relabelRingAssemblyObservation [DecidableEq V] (enumeration : V ≃ Fin n) :
    (observation : SourceRingAssemblyObservation policy) →
      observation.BoundedIn n → RingAssemblyObservation V policy
  | .axes observation, bounded =>
      .axes (relabelRingAssemblyAxesObservation enumeration policy observation bounded)
  | .centers observation, bounded =>
      .centers (relabelRingAssemblyCentersObservation enumeration policy observation bounded)
  | .doubleBonds observation, bounded =>
      .doubleBonds (relabelRingAssemblyDoubleBondsObservation enumeration policy observation bounded)

/-- Decode one tagged observation to the exact pre-existing ring-assembly carrier record. -/
def unrelabelRingAssemblyObservation [DecidableEq V] (enumeration : V ≃ Fin n) :
    RingAssemblyObservation V policy → SourceRingAssemblyObservation policy
  | .axes observation =>
      .axes (unrelabelRingAssemblyAxesObservation enumeration policy observation)
  | .centers observation =>
      .centers (unrelabelRingAssemblyCentersObservation enumeration policy observation)
  | .doubleBonds observation =>
      .doubleBonds (unrelabelRingAssemblyDoubleBondsObservation enumeration policy observation)

/-- Exact recovery of every existing ring-assembly observation record.  The axes branch needs the
normalization equality that the carrier's own `ValidFor` supplies; the other two branches need
nothing beyond the bounds. -/
theorem unrelabelRingAssemblyObservation_relabelRingAssemblyObservation [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observation : SourceRingAssemblyObservation policy)
    (bounded : observation.BoundedIn n)
    (normalizationFixed : observation.NormalizationFixed) :
    unrelabelRingAssemblyObservation enumeration
        (relabelRingAssemblyObservation enumeration observation bounded) = observation := by
  cases observation with
  | axes observation =>
      change SourceRingAssemblyObservation.axes
        (unrelabelRingAssemblyAxesObservation enumeration policy
          (relabelRingAssemblyAxesObservation enumeration policy observation bounded)) =
        SourceRingAssemblyObservation.axes observation
      rw [unrelabelRingAssemblyAxesObservation_relabel enumeration policy observation bounded
        normalizationFixed]
  | centers observation =>
      change SourceRingAssemblyObservation.centers
        (unrelabelRingAssemblyCentersObservation enumeration policy
          (relabelRingAssemblyCentersObservation enumeration policy observation bounded)) =
        SourceRingAssemblyObservation.centers observation
      rw [unrelabelRingAssemblyCentersObservation_relabel enumeration policy observation bounded]
  | doubleBonds observation =>
      change SourceRingAssemblyObservation.doubleBonds
        (unrelabelRingAssemblyDoubleBondsObservation enumeration policy
          (relabelRingAssemblyDoubleBondsObservation enumeration policy observation bounded)) =
        SourceRingAssemblyObservation.doubleBonds observation
      rw [unrelabelRingAssemblyDoubleBondsObservation_relabel enumeration policy observation
        bounded]

/-- Bounds of a decoded tagged observation. -/
def unrelabelRingAssemblyObservationBounded [DecidableEq V] (enumeration : V ≃ Fin n) :
    (observation : RingAssemblyObservation V policy) →
      (unrelabelRingAssemblyObservation enumeration observation).BoundedIn n
  | .axes observation =>
      unrelabelRingAssemblyAxesObservationBounded enumeration policy observation
  | .centers observation =>
      unrelabelRingAssemblyCentersObservationBounded enumeration policy observation
  | .doubleBonds observation =>
      unrelabelRingAssemblyDoubleBondsObservationBounded enumeration policy observation

/-- Relabelling a decoded tagged observation returns the supplied observation.  The axes branch
carries the explicit raw-syntax-normalized hypothesis. -/
theorem relabelRingAssemblyObservation_unrelabelRingAssemblyObservation [DecidableEq V]
    (enumeration : V ≃ Fin n) (observation : RingAssemblyObservation V policy)
    (rawSyntaxNormalized : observation.RawSyntaxNormalized) :
    relabelRingAssemblyObservation enumeration
        (unrelabelRingAssemblyObservation enumeration observation)
        (unrelabelRingAssemblyObservationBounded enumeration observation) = observation := by
  cases observation with
  | axes observation =>
      change RingAssemblyObservation.axes
        (relabelRingAssemblyAxesObservation enumeration policy
          (unrelabelRingAssemblyAxesObservation enumeration policy observation)
          (unrelabelRingAssemblyAxesObservationBounded enumeration policy observation)) =
        RingAssemblyObservation.axes observation
      rw [relabelRingAssemblyAxesObservation_unrelabel enumeration policy observation
        rawSyntaxNormalized]
  | centers observation =>
      change RingAssemblyObservation.centers
        (relabelRingAssemblyCentersObservation enumeration policy
          (unrelabelRingAssemblyCentersObservation enumeration policy observation)
          (unrelabelRingAssemblyCentersObservationBounded enumeration policy observation)) =
        RingAssemblyObservation.centers observation
      rw [relabelRingAssemblyCentersObservation_unrelabel enumeration policy observation]
  | doubleBonds observation =>
      change RingAssemblyObservation.doubleBonds
        (relabelRingAssemblyDoubleBondsObservation enumeration policy
          (unrelabelRingAssemblyDoubleBondsObservation enumeration policy observation)
          (unrelabelRingAssemblyDoubleBondsObservationBounded enumeration policy observation)) =
        RingAssemblyObservation.doubleBonds observation
      rw [relabelRingAssemblyDoubleBondsObservation_unrelabel enumeration policy observation]

/-- A decoded axes record always satisfies the normalization-recomputation condition once the
stored raw syntax is normalized: the decoder's normalization is `normalizeRawMolecule parsed` and
normalizing it again returns the same parsed syntax.  The other two rows are vacuous. -/
theorem normalizationFixed_unrelabelRingAssemblyObservation [DecidableEq V]
    (enumeration : V ≃ Fin n) (observation : RingAssemblyObservation V policy)
    (rawSyntaxNormalized : observation.RawSyntaxNormalized) :
    (unrelabelRingAssemblyObservation enumeration observation).NormalizationFixed := by
  cases observation with
  | axes observation =>
      rcases observation with ⟨assembly, parsed, spatial, assignments⟩
      have idempotent : parsed.normalizeUnspecifiedBonds = parsed := by
        simpa [RingAssemblyObservation.RawSyntaxNormalized, RawMoleculeNormalized]
          using rawSyntaxNormalized
      simp [unrelabelRingAssemblyObservation, unrelabelRingAssemblyAxesObservation,
        SourceRingAssemblyObservation.NormalizationFixed, normalizeRawMolecule_parsed, idempotent]
  | centers _ => trivial
  | doubleBonds _ => trivial

/-! ## Validity at the same recovered source and policy -/

/-- `ValidFor` of a tagged source observation at the exact source and policy. -/
def SourceRingAssemblyObservation.ValidFor (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput) :
    SourceRingAssemblyObservation policy → Prop
  | .axes observation => observation.ValidFor policy source
  | .centers observation => observation.ValidFor policy source
  | .doubleBonds observation => observation.ValidFor policy source

/-- The normalization equality is a conjunct of the carrier's own axes `ValidFor`, so it is
derived, never assumed. -/
theorem SourceRingAssemblyObservation.normalizationFixed_of_validFor
    (source : AuthoritativeChemicalInput)
    (observation : SourceRingAssemblyObservation policy)
    (valid : observation.ValidFor policy source) :
    observation.NormalizationFixed := by
  cases observation with
  | axes observation => exact valid.2.2.2.1
  | centers _ => trivial
  | doubleBonds _ => trivial

/-- **Validity transport through the exact decode.**  The decoded record's `ValidFor` at the same
source and policy is equivalent to the original record's, because the records are equal. -/
theorem validFor_unrelabelRingAssemblyObservation_relabelRingAssemblyObservation_iff
    [DecidableEq V] (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observation : SourceRingAssemblyObservation policy)
    (bounded : observation.BoundedIn n)
    (normalizationFixed : observation.NormalizationFixed) :
    (unrelabelRingAssemblyObservation enumeration
        (relabelRingAssemblyObservation enumeration observation bounded)).ValidFor policy source ↔
      observation.ValidFor policy source := by
  rw [unrelabelRingAssemblyObservation_relabelRingAssemblyObservation enumeration observation
    bounded normalizationFixed]

/-- Forward validity preservation at the same source and policy. -/
theorem validFor_of_relabelRingAssemblyObservation [DecidableEq V]
    (enumeration : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (observation : SourceRingAssemblyObservation policy)
    (bounded : observation.BoundedIn n)
    (normalizationFixed : observation.NormalizationFixed)
    (valid : observation.ValidFor policy source) :
    (unrelabelRingAssemblyObservation enumeration
        (relabelRingAssemblyObservation enumeration observation bounded)).ValidFor policy source :=
  (validFor_unrelabelRingAssemblyObservation_relabelRingAssemblyObservation_iff
    enumeration source observation bounded normalizationFixed).mpr valid

/-- Validity transport for a decoded native observation through a native round trip. -/
theorem validFor_unrelabelRingAssemblyObservation_roundtrip_iff [DecidableEq V]
    (enumeration : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (observation : RingAssemblyObservation V policy)
    (rawSyntaxNormalized : observation.RawSyntaxNormalized) :
    (unrelabelRingAssemblyObservation enumeration
        (relabelRingAssemblyObservation enumeration
          (unrelabelRingAssemblyObservation enumeration observation)
          (unrelabelRingAssemblyObservationBounded enumeration observation))).ValidFor
        policy source ↔
      (unrelabelRingAssemblyObservation enumeration observation).ValidFor policy source := by
  rw [relabelRingAssemblyObservation_unrelabelRingAssemblyObservation enumeration observation
    rawSyntaxNormalized]

/-- Bounds derived from the actual `ValidFor` of a tagged ring-assembly source observation. -/
theorem SourceRingAssemblyObservation.boundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (observation : SourceRingAssemblyObservation policy)
    (valid : observation.ValidFor policy source)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    observation.BoundedIn source.molecule.atomCount := by
  cases observation with
  | axes observation =>
      rcases observation with ⟨assembly, normalization, spatial, assignments⟩
      rcases valid with ⟨assemblyValid, spatialEq, _agreement, _normalization, _ne,
        _junctionNodup, _citationNodup, perAssignment, _cover⟩
      refine ⟨assemblyBoundedIn_of_mechanicallyValidFor source assembly
          structurallyWellFormed assemblyValid.1,
        spatialFits_of_wf source spatialWellFormed spatial spatialEq, ?_⟩
      intro assignment member
      exact axisAssignmentBoundedIn_of_validFor source policy assembly normalization spatial
        structurallyWellFormed assemblyValid.1 assignment (perAssignment assignment member)
  | centers observation =>
      rcases observation with ⟨assembly, assignments⟩
      rcases valid with ⟨assemblyValid, _ne, _centerNodup, _citationNodup, perAssignment,
        _cover⟩
      refine ⟨assemblyBoundedIn_of_mechanicallyValidFor source assembly
          structurallyWellFormed assemblyValid.1, ?_⟩
      intro assignment member
      exact centerAssignmentBoundedIn_of_validFor source policy assembly assignment
        (perAssignment assignment member)
  | doubleBonds observation =>
      rcases observation with ⟨assembly, assignments⟩
      rcases valid with ⟨assemblyValid, _ne, _tripleNodup, _citationNodup, perAssignment,
        _cover⟩
      refine ⟨assemblyBoundedIn_of_mechanicallyValidFor source assembly
          structurallyWellFormed assemblyValid.1, ?_⟩
      intro assignment member
      exact doubleBondAssignmentBoundedIn_of_validFor source policy assembly
        structurallyWellFormed assignment (perAssignment assignment member)

/-! ## Ordered heterogeneous lists -/

/-- Relabel an ordered heterogeneous list of ring-assembly observations. -/
def relabelRingAssemblyObservationList [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (SourceRingAssemblyObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    List (RingAssemblyObservation V policy) :=
  observations.attach.map fun observation =>
    relabelRingAssemblyObservation enumeration observation.1
      (bounded observation.1 observation.2)

/-- Decode an ordered heterogeneous list of native observations. -/
def unrelabelRingAssemblyObservationList [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (RingAssemblyObservation V policy)) :
    List (SourceRingAssemblyObservation policy) :=
  observations.map (unrelabelRingAssemblyObservation enumeration)

/-- Every decoded element satisfies the same explicit bounds. -/
def unrelabelRingAssemblyObservationListBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (RingAssemblyObservation V policy)) :
    ∀ observation ∈ unrelabelRingAssemblyObservationList enumeration observations,
      observation.BoundedIn n := by
  intro observation member
  rw [unrelabelRingAssemblyObservationList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelRingAssemblyObservationBounded enumeration presented

@[simp] theorem relabelRingAssemblyObservationList_length [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (SourceRingAssemblyObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    (relabelRingAssemblyObservationList enumeration observations bounded).length =
      observations.length := by
  simp [relabelRingAssemblyObservationList]

@[simp] theorem unrelabelRingAssemblyObservationList_length [DecidableEq V]
    (enumeration : V ≃ Fin n) (observations : List (RingAssemblyObservation V policy)) :
    (unrelabelRingAssemblyObservationList enumeration observations).length =
      observations.length := by
  simp [unrelabelRingAssemblyObservationList]

/-- Exact recovery of the ordered heterogeneous observation list, including order, multiplicity
and each concrete record shape. -/
theorem unrelabelRingAssemblyObservationList_relabelRingAssemblyObservationList [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (SourceRingAssemblyObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (normalizationFixed : ∀ observation ∈ observations, observation.NormalizationFixed) :
    unrelabelRingAssemblyObservationList enumeration
        (relabelRingAssemblyObservationList enumeration observations bounded) = observations := by
  unfold unrelabelRingAssemblyObservationList relabelRingAssemblyObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact unrelabelRingAssemblyObservation_relabelRingAssemblyObservation enumeration
      observation.1 (bounded observation.1 observation.2)
      (normalizationFixed observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-- Relabelling a decoded heterogeneous list returns the supplied list. -/
theorem relabelRingAssemblyObservationList_unrelabelRingAssemblyObservationList [DecidableEq V]
    (enumeration : V ≃ Fin n) (observations : List (RingAssemblyObservation V policy))
    (rawSyntaxNormalized : ∀ observation ∈ observations, observation.RawSyntaxNormalized) :
    relabelRingAssemblyObservationList enumeration
        (unrelabelRingAssemblyObservationList enumeration observations)
        (unrelabelRingAssemblyObservationListBounded enumeration observations) = observations := by
  unfold relabelRingAssemblyObservationList unrelabelRingAssemblyObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelRingAssemblyObservation_unrelabelRingAssemblyObservation enumeration
      observation.1 (rawSyntaxNormalized observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-! ## Correlated sets of observations -/

/-- Image of a set of source observations under the codec. -/
def relabelRingAssemblyObservationSet [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (SourceRingAssemblyObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    Set (RingAssemblyObservation V policy) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelRingAssemblyObservation enumeration observation
        (bounded observation member) = presented

/-- Preimage of a set of native observations under the codec. -/
def unrelabelRingAssemblyObservationSet [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (RingAssemblyObservation V policy)) :
    Set (SourceRingAssemblyObservation policy) :=
  fun recovered =>
    ∃ presented ∈ observations,
      unrelabelRingAssemblyObservation enumeration presented = recovered

/-- Every decoded element of the image set satisfies the explicit bounds. -/
def unrelabelRingAssemblyObservationSetBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (RingAssemblyObservation V policy)) :
    ∀ observation ∈ unrelabelRingAssemblyObservationSet enumeration observations,
      observation.BoundedIn n := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact unrelabelRingAssemblyObservationBounded enumeration presented

/-- The correlated-set inverse on the source side. -/
theorem unrelabelRingAssemblyObservationSet_relabelRingAssemblyObservationSet [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (SourceRingAssemblyObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (normalizationFixed : ∀ observation ∈ observations, observation.NormalizationFixed) :
    unrelabelRingAssemblyObservationSet enumeration
        (relabelRingAssemblyObservationSet enumeration observations bounded) = observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [unrelabelRingAssemblyObservation_relabelRingAssemblyObservation enumeration observation
      (bounded observation member) (normalizationFixed observation member)] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelRingAssemblyObservation enumeration recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      unrelabelRingAssemblyObservation_relabelRingAssemblyObservation enumeration recovered
        (bounded recovered member) (normalizationFixed recovered member)⟩

/-- The relabelling of an observation does not inspect the proof of its boundedness. -/
theorem relabelRingAssemblyObservation_bound_irrel [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : SourceRingAssemblyObservation policy)
    (first second : observation.BoundedIn n) :
    relabelRingAssemblyObservation enumeration observation first =
      relabelRingAssemblyObservation enumeration observation second := by
  cases observation <;> rfl

/-- Relabelling respects equality of the underlying source observation, independently of how the
two boundedness proofs were obtained. -/
theorem relabelRingAssemblyObservation_congr [DecidableEq V] (enumeration : V ≃ Fin n)
    {first second : SourceRingAssemblyObservation policy} (h : first = second)
    (firstBounded : first.BoundedIn n) (secondBounded : second.BoundedIn n) :
    relabelRingAssemblyObservation enumeration first firstBounded =
      relabelRingAssemblyObservation enumeration second secondBounded := by
  cases h
  exact relabelRingAssemblyObservation_bound_irrel enumeration _ firstBounded secondBounded

/-- The correlated-set inverse on the native side. -/
theorem relabelRingAssemblyObservationSet_unrelabelRingAssemblyObservationSet [DecidableEq V]
    (enumeration : V ≃ Fin n) (observations : Set (RingAssemblyObservation V policy))
    (rawSyntaxNormalized : ∀ observation ∈ observations, observation.RawSyntaxNormalized) :
    relabelRingAssemblyObservationSet enumeration
        (unrelabelRingAssemblyObservationSet enumeration observations)
        (unrelabelRingAssemblyObservationSetBounded enumeration observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have roundTrip : relabelRingAssemblyObservation enumeration
        (unrelabelRingAssemblyObservation enumeration presented₀)
        (unrelabelRingAssemblyObservationBounded enumeration presented₀) = presented₀ :=
      relabelRingAssemblyObservation_unrelabelRingAssemblyObservation enumeration presented₀
        (rawSyntaxNormalized presented₀ presentedMember)
    have relabelEq' : relabelRingAssemblyObservation enumeration
        (unrelabelRingAssemblyObservation enumeration presented₀)
        (unrelabelRingAssemblyObservationBounded enumeration presented₀) = presented := by
      simpa only [decodeEq] using relabelEq
    have presentedEq : presented = presented₀ := by
      rw [← relabelEq', roundTrip]
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨unrelabelRingAssemblyObservation enumeration presented,
      ⟨presented, member, rfl⟩,
      relabelRingAssemblyObservation_unrelabelRingAssemblyObservation enumeration presented
        (rawSyntaxNormalized presented member)⟩

/-- **Correlated validity for a set.**  A native observation belongs to the image of a set exactly
when its decoded record is one of the source observations; consequently its `ValidFor` at the same
source and policy is exactly the validity of that source observation. -/
theorem validFor_mem_relabelRingAssemblyObservationSet_iff [DecidableEq V]
    (enumeration : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (observations : Set (SourceRingAssemblyObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (normalizationFixed : ∀ observation ∈ observations, observation.NormalizationFixed)
    (presented : RingAssemblyObservation V policy)
    (member : presented ∈
      relabelRingAssemblyObservationSet enumeration observations bounded) :
    (unrelabelRingAssemblyObservation enumeration presented).ValidFor policy source ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelRingAssemblyObservation enumeration observation
            (bounded observation observationMember) = presented ∧
          observation.ValidFor policy source := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rwa [unrelabelRingAssemblyObservation_relabelRingAssemblyObservation enumeration observation
      (bounded observation observationMember)
      (normalizationFixed observation observationMember)] at valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rwa [unrelabelRingAssemblyObservation_relabelRingAssemblyObservation enumeration observation
      (bounded observation observationMember)
      (normalizationFixed observation observationMember)]

/-! ## Shared source context and the composable satellite -/

/-- The common source binding: the accepted molecule-codec binding from
`OrganicStereoP93PhysicalFrameIngress`.  It ties a shared finite graph, coordinate channel and
diagram channel to the authoritative input by actual equalities. -/
abbrev MonocyclicRingAssemblySourceBinding (V : Type*) [DecidableEq V] [Fintype V] :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V

/-- Bounds of a tagged observation derived from its validity and the exact source binding. -/
theorem SourceRingAssemblyObservation.boundedIn_of_validFor_binding
    [DecidableEq V] [Fintype V]
    (binding : MonocyclicRingAssemblySourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (observation : SourceRingAssemblyObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.BoundedIn (Fintype.card V) := by
  have bounded := SourceRingAssemblyObservation.boundedIn_of_validFor binding.source
    observation valid structurallyWellFormed binding.spatial_wellFormed
  rwa [binding.atomCount_eq] at bounded

/-- A raw monocyclic/ring-assembly observation source: the exact source binding, the source's
structural certificate, and an ordered list of `Nat`-indexed carrier observations, each valid at
the bound source. -/
structure RawMonocyclicRingAssemblySource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93RingAssemblyAuthorityPolicy) where
  binding : MonocyclicRingAssemblySourceBinding V
  structurallyWellFormed : binding.source.molecule.StructurallyWellFormed
  observations : List (SourceRingAssemblyObservation policy)
  valid : ∀ observation ∈ observations, observation.ValidFor policy binding.source

/-- The composable native satellite.  It carries the same graph/spatial/diagram context as the
existing molecule codec and the ordered list of native observations.  No original observation and
no original `AuthoritativeChemicalInput` is stored here. -/
structure MonocyclicRingAssemblyObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93RingAssemblyAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (RingAssemblyObservation V policy)

namespace MonocyclicRingAssemblyObservationSatellite

variable [DecidableEq V] [Fintype V]

/-- The shared finite source, with observations intentionally excluded. -/
def toFiniteSource
    (satellite : MonocyclicRingAssemblyObservationSatellite V policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end MonocyclicRingAssemblyObservationSatellite

/-- Adapt a raw source into the satellite: keep the exact shared finite source and relabel every
observation, deriving the atom bounds from its actual `ValidFor`. -/
def adapt [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicRingAssemblySource V policy) :
    MonocyclicRingAssemblyObservationSatellite V policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelRingAssemblyObservation raw.binding.enumeration observation.1
      (SourceRingAssemblyObservation.boundedIn_of_validFor_binding raw.binding
        raw.structurallyWellFormed observation.1 (raw.valid observation.1 observation.2))

@[simp] theorem adapt_graph [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicRingAssemblySource V policy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicRingAssemblySource V policy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicRingAssemblySource V policy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

/-- The recovered source record: the exact authoritative input and the decoded observation list. -/
@[ext] structure RecoveredMonocyclicRingAssemblySource
    (policy : P93RingAssemblyAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceRingAssemblyObservation policy)

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; observations are decoded with the same enumeration. -/
def suppliedSource [DecidableEq V] [Fintype V]
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : MonocyclicRingAssemblyObservationSatellite V policy) :
    RecoveredMonocyclicRingAssemblySource policy where
  source := satellite.toFiniteSource.encode enumeration
  observations := unrelabelRingAssemblyObservationList enumeration satellite.observations

/-- **Exact full source recovery.**  Adapting a raw source and decoding it returns the exact
authoritative input (through the binding's actual source equality) and the exact ordered list of
pre-existing ring-assembly observation records. -/
theorem suppliedSource_adapt [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicRingAssemblySource V policy) :
    suppliedSource raw.binding.enumeration (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredMonocyclicRingAssemblySource.ext
  · exact raw.binding.encode_shared
  · change unrelabelRingAssemblyObservationList raw.binding.enumeration
      (adapt raw).observations = raw.observations
    rw [show (adapt raw).observations = raw.observations.attach.map (fun observation =>
        relabelRingAssemblyObservation raw.binding.enumeration observation.1
          (SourceRingAssemblyObservation.boundedIn_of_validFor_binding raw.binding
            raw.structurallyWellFormed observation.1
            (raw.valid observation.1 observation.2))) from rfl]
    exact unrelabelRingAssemblyObservationList_relabelRingAssemblyObservationList
      raw.binding.enumeration raw.observations
      (fun observation member =>
        SourceRingAssemblyObservation.boundedIn_of_validFor_binding raw.binding
          raw.structurallyWellFormed observation (raw.valid observation member))
      (fun observation member =>
        SourceRingAssemblyObservation.normalizationFixed_of_validFor raw.binding.source
          observation (raw.valid observation member))

/-- Validity is preserved for the whole recovered list at the same source and policy. -/
theorem suppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicRingAssemblySource V policy)
    (observation : SourceRingAssemblyObservation policy)
    (member : observation ∈
      (suppliedSource raw.binding.enumeration (adapt raw)).observations) :
    observation.ValidFor policy raw.binding.source := by
  have listEq : (suppliedSource raw.binding.enumeration (adapt raw)).observations =
      raw.observations := by
    simpa using congrArg RecoveredMonocyclicRingAssemblySource.observations
      (suppliedSource_adapt raw)
  have sourceMember : observation ∈ raw.observations := by
    rw [← listEq]
    exact member
  exact raw.valid observation sourceMember

/-! ## Concrete certified-source adapter -/

/-- The concrete binding of a certified authoritative input to its exact finite ingress source,
reusing the existing molecule codec's certified binding. -/
def certifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    MonocyclicRingAssemblySourceBinding (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

/-- Adapt a certified source together with an ordered list of valid carrier observations. -/
def adaptCertified (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceRingAssemblyObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor policy certified.input) :
    MonocyclicRingAssemblyObservationSatellite
      (Fin certified.input.molecule.atomCount) policy :=
  adapt { binding := certifiedBinding certified
          structurallyWellFormed := certified.structurallyWellFormed.1
          observations := observations
          valid := valid }

/-- **Concrete exact recovery from a certified source.** -/
theorem suppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceRingAssemblyObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor policy certified.input) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified observations valid) =
      { source := certified.input, observations := observations } :=
  suppliedSource_adapt
    { binding := certifiedBinding certified
      structurallyWellFormed := certified.structurallyWellFormed.1
      observations := observations
      valid := valid }

/-! ## The monocyclic full-source binding and its certified adapter

The monocyclic carrier receives the same end-to-end treatment as the ring-assembly carrier above:
one shared source binding with actual graph/spatial/diagram equalities, a raw source that stores
the exact authoritative input only through that binding, and a satellite that stores only the
native shared finite source and the ordered list of supplied observations. -/

/-- The monocyclic source binding is the same accepted molecule-codec binding used by the
ring-assembly satellite; both carriers share one source binding. -/
abbrev MonocyclicSourceBinding (V : Type*) [DecidableEq V] [Fintype V] :=
  MonocyclicRingAssemblySourceBinding V

/-- Bounds of a tagged monocyclic observation derived from its validity and the exact source
binding. -/
theorem SourceMonocyclicObservation.boundedIn_of_validFor_binding
    [DecidableEq V] [Fintype V]
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    (binding : MonocyclicSourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (observation : SourceMonocyclicObservation monocyclicPolicy)
    (valid : observation.ValidFor binding.source) :
    observation.BoundedIn (Fintype.card V) := by
  have bounded := SourceMonocyclicObservation.boundedIn_of_validFor binding.source
    structurallyWellFormed observation valid binding.spatial_wellFormed
  rwa [binding.atomCount_eq] at bounded

variable {monocyclicPolicy : P93MonocyclicAuthorityPolicy}

/-- A raw monocyclic observation source: the exact source binding, the source's structural
certificate, and an ordered list of `Nat`-indexed monocyclic carrier observations, each valid at
the bound source. -/
structure RawMonocyclicSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93MonocyclicAuthorityPolicy) where
  binding : MonocyclicSourceBinding V
  structurallyWellFormed : binding.source.molecule.StructurallyWellFormed
  observations : List (SourceMonocyclicObservation policy)
  valid : ∀ observation ∈ observations, observation.ValidFor binding.source

/-- The monocyclic native satellite.  It carries the same graph/spatial/diagram context as the
existing molecule codec and the ordered list of native monocyclic observations.  No original
observation and no original `AuthoritativeChemicalInput` is stored here. -/
structure MonocyclicObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93MonocyclicAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (MonocyclicObservation V policy)

namespace MonocyclicObservationSatellite

variable [DecidableEq V] [Fintype V]

/-- The shared finite source, with observations intentionally excluded. -/
def toFiniteSource
    (satellite : MonocyclicObservationSatellite V monocyclicPolicy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end MonocyclicObservationSatellite

/-- Adapt a raw monocyclic source into the satellite: keep the exact shared finite source and
relabel every observation, deriving the atom bounds from its actual `ValidFor`. -/
def adaptMonocyclic [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    MonocyclicObservationSatellite V monocyclicPolicy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelMonocyclicObservation raw.binding.enumeration observation.1
      (SourceMonocyclicObservation.boundedIn_of_validFor_binding raw.binding
        raw.structurallyWellFormed observation.1 (raw.valid observation.1 observation.2))

@[simp] theorem adaptMonocyclic_graph [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    (adaptMonocyclic raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adaptMonocyclic_spatial? [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    (adaptMonocyclic raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adaptMonocyclic_diagram? [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    (adaptMonocyclic raw).diagram? = raw.binding.shared.diagram? := rfl

/-- The adapted satellite's shared finite source is the binding's shared source exactly. -/
@[simp] theorem adaptMonocyclic_toFiniteSource [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    (adaptMonocyclic raw).toFiniteSource = raw.binding.shared := rfl

/-- The recovered monocyclic source record: the exact authoritative input and the decoded
observation list. -/
@[ext] structure RecoveredMonocyclicSource (policy : P93MonocyclicAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceMonocyclicObservation policy)

/-- Decode a monocyclic satellite into the recovered source record.  The authoritative input is
the exact encode of the shared finite source; observations are decoded with the same
enumeration. -/
def monocyclicSuppliedSource [DecidableEq V] [Fintype V]
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : MonocyclicObservationSatellite V monocyclicPolicy) :
    RecoveredMonocyclicSource monocyclicPolicy where
  source := satellite.toFiniteSource.encode enumeration
  observations := unrelabelMonocyclicObservationList enumeration satellite.observations

/-- **Exact full-source recovery for monocyclic observations.**  Adapting a raw source and
decoding it returns the exact authoritative input (through the binding's actual source equality)
and the exact ordered list of pre-existing monocyclic observation records. -/
theorem monocyclicSuppliedSource_adapt [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    monocyclicSuppliedSource raw.binding.enumeration (adaptMonocyclic raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredMonocyclicSource.ext
  · exact raw.binding.encode_shared
  · change unrelabelMonocyclicObservationList raw.binding.enumeration
      (adaptMonocyclic raw).observations = raw.observations
    rw [show (adaptMonocyclic raw).observations = raw.observations.attach.map (fun observation =>
        relabelMonocyclicObservation raw.binding.enumeration observation.1
          (SourceMonocyclicObservation.boundedIn_of_validFor_binding raw.binding
            raw.structurallyWellFormed observation.1
            (raw.valid observation.1 observation.2))) from rfl]
    exact unrelabelMonocyclicObservationList_relabelMonocyclicObservationList
      raw.binding.enumeration raw.observations
      (fun observation member =>
        SourceMonocyclicObservation.boundedIn_of_validFor_binding raw.binding
          raw.structurallyWellFormed observation (raw.valid observation member))

/-- Validity is preserved for the whole recovered monocyclic list at the same source and
policy. -/
theorem monocyclicSuppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy)
    (observation : SourceMonocyclicObservation monocyclicPolicy)
    (member : observation ∈
      (monocyclicSuppliedSource raw.binding.enumeration (adaptMonocyclic raw)).observations) :
    observation.ValidFor raw.binding.source := by
  have listEq : (monocyclicSuppliedSource raw.binding.enumeration
      (adaptMonocyclic raw)).observations = raw.observations := by
    simpa using congrArg RecoveredMonocyclicSource.observations
      (monocyclicSuppliedSource_adapt raw)
  have sourceMember : observation ∈ raw.observations := by
    rw [← listEq]
    exact member
  exact raw.valid observation sourceMember

/-- The recovered authoritative input is exactly the binding's source. -/
@[simp] theorem monocyclicSuppliedSource_adapt_source [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    (monocyclicSuppliedSource raw.binding.enumeration (adaptMonocyclic raw)).source =
      raw.binding.source := by
  simpa using congrArg RecoveredMonocyclicSource.source (monocyclicSuppliedSource_adapt raw)

/-- The recovered graph channel is exactly the original graph channel. -/
@[simp] theorem monocyclicSuppliedSource_adapt_molecule [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    (monocyclicSuppliedSource raw.binding.enumeration (adaptMonocyclic raw)).source.molecule =
      raw.binding.source.molecule := by
  rw [monocyclicSuppliedSource_adapt_source]

/-- The recovered spatial channel is exactly the original spatial channel. -/
@[simp] theorem monocyclicSuppliedSource_adapt_spatial [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    (monocyclicSuppliedSource raw.binding.enumeration (adaptMonocyclic raw)).source.spatial? =
      raw.binding.source.spatial? := by
  rw [monocyclicSuppliedSource_adapt_source]

/-- The recovered diagram channel is exactly the original diagram channel. -/
@[simp] theorem monocyclicSuppliedSource_adapt_diagram [DecidableEq V] [Fintype V]
    (raw : RawMonocyclicSource V monocyclicPolicy) :
    (monocyclicSuppliedSource raw.binding.enumeration (adaptMonocyclic raw)).source.diagram? =
      raw.binding.source.diagram? := by
  rw [monocyclicSuppliedSource_adapt_source]

/-! ## The concrete certified monocyclic adapter -/

/-- The concrete binding of a certified authoritative input to its exact finite ingress source,
reusing the existing molecule codec's certified binding. -/
def monocyclicCertifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    MonocyclicSourceBinding (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

/-- Adapt a certified source together with an ordered list of valid monocyclic carrier
observations. -/
def adaptCertifiedMonocyclic (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceMonocyclicObservation monocyclicPolicy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    MonocyclicObservationSatellite (Fin certified.input.molecule.atomCount) monocyclicPolicy :=
  adaptMonocyclic { binding := monocyclicCertifiedBinding certified
                    structurallyWellFormed := certified.structurallyWellFormed.1
                    observations := observations
                    valid := valid }

/-- **Concrete exact recovery from a certified source.** -/
theorem monocyclicSuppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceMonocyclicObservation monocyclicPolicy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    monocyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedMonocyclic certified observations valid) =
      { source := certified.input, observations := observations } :=
  monocyclicSuppliedSource_adapt
    { binding := monocyclicCertifiedBinding certified
      structurallyWellFormed := certified.structurallyWellFormed.1
      observations := observations
      valid := valid }

/-- The certified monocyclic adapter recovers the graph, spatial and diagram channels of the
certified input together with the exact ordered observation list. -/
theorem monocyclicSuppliedSource_adaptCertified_channels
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceMonocyclicObservation monocyclicPolicy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    (monocyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedMonocyclic certified observations valid)).source.molecule =
        certified.input.molecule ∧
      (monocyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedMonocyclic certified observations valid)).source.spatial? =
        certified.input.spatial? ∧
      (monocyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedMonocyclic certified observations valid)).source.diagram? =
        certified.input.diagram? ∧
      (monocyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedMonocyclic certified observations valid)).observations =
        observations := by
  simp [monocyclicSuppliedSource_adaptCertified]

/-! ## The concrete combined monocyclic/ring-assembly tag

The combined carrier exposes every one of the eight pre-existing monocyclic observation records
and every one of the three pre-existing ring-assembly observation records as its own constructor.
The codecs below are dispatches onto the accepted per-record codecs; no new codec is assumed and
no original record is stored on the native side. -/

/-- The concrete combined source tag: the eight pre-existing monocyclic carrier records and the
three pre-existing ring-assembly carrier records. -/
inductive SourceCyclicObservation (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy) where
  | monocyclicPhysicalUnit (observation : P93MonocyclicPhysicalUnit)
  | monocyclicGeneral (observation : P93MonocyclicGeneralAssignment monocyclicPolicy)
  | monocyclicCenter (observation : P93MonocyclicCenterAuthorityObservation monocyclicPolicy)
  | monocyclicCisTrans
      (observation : P93MonocyclicCisTransAuthorityObservation monocyclicPolicy)
  | monocyclicRCT (observation : P93MonocyclicRCTAuthorityObservation monocyclicPolicy)
  | monocyclicUnsaturation
      (observation : P93MonocyclicUnsaturationAuthorityObservation monocyclicPolicy)
  | monocyclicDoubleBond
      (observation : P93MonocyclicDoubleBondAuthorityObservation monocyclicPolicy)
  | monocyclicExocyclic
      (observation : P93MonocyclicExocyclicAuthorityObservation monocyclicPolicy)
  | ringAssemblyAxes (observation : P93RingAssemblyAxesAuthorityObservation assemblyPolicy)
  | ringAssemblyCenters
      (observation : P93RingAssemblyCentersAuthorityObservation assemblyPolicy)
  | ringAssemblyDoubleBonds
      (observation : P93RingAssemblyDoubleBondsAuthorityObservation assemblyPolicy)

/-- The native combined payload: one constructor per pre-existing record, carrying only supplied
data. -/
inductive CyclicObservation (V : Type*) (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy) where
  | monocyclicPhysicalUnit (observation : SuppliedMonocyclicPhysicalUnit V)
  | monocyclicGeneral (observation : SuppliedMonocyclicGeneralAssignment V monocyclicPolicy)
  | monocyclicCenter
      (observation : SuppliedMonocyclicCenterAuthorityObservation V monocyclicPolicy)
  | monocyclicCisTrans
      (observation : SuppliedMonocyclicCisTransAuthorityObservation V monocyclicPolicy)
  | monocyclicRCT
      (observation : SuppliedMonocyclicRCTAuthorityObservation V monocyclicPolicy)
  | monocyclicUnsaturation
      (observation : SuppliedMonocyclicUnsaturationAuthorityObservation V monocyclicPolicy)
  | monocyclicDoubleBond
      (observation : SuppliedMonocyclicDoubleBondAuthorityObservation V monocyclicPolicy)
  | monocyclicExocyclic
      (observation : SuppliedMonocyclicExocyclicAuthorityObservation V monocyclicPolicy)
  | ringAssemblyAxes
      (observation : SuppliedRingAssemblyAxesAuthorityObservation V assemblyPolicy)
  | ringAssemblyCenters
      (observation : SuppliedRingAssemblyCentersAuthorityObservation V assemblyPolicy)
  | ringAssemblyDoubleBonds
      (observation : SuppliedRingAssemblyDoubleBondsAuthorityObservation V assemblyPolicy)

/-- Explicit bounds for a combined source observation: exactly the accepted per-record bound of
its constructor. -/
def SourceCyclicObservation.BoundedIn {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} (n : ℕ) :
    SourceCyclicObservation monocyclicPolicy assemblyPolicy → Prop
  | .monocyclicPhysicalUnit observation => monocyclicPhysicalUnitBoundedIn n observation
  | .monocyclicGeneral observation =>
      monocyclicGeneralAssignmentBoundedIn n monocyclicPolicy observation
  | .monocyclicCenter observation =>
      monocyclicCenterObservationBoundedIn n monocyclicPolicy observation
  | .monocyclicCisTrans observation =>
      cisTransObservationBoundedIn n monocyclicPolicy observation
  | .monocyclicRCT observation => rctObservationBoundedIn n monocyclicPolicy observation
  | .monocyclicUnsaturation observation =>
      monocyclicUnsaturationObservationBoundedIn n monocyclicPolicy observation
  | .monocyclicDoubleBond observation =>
      monocyclicDoubleBondObservationBoundedIn n monocyclicPolicy observation
  | .monocyclicExocyclic observation =>
      monocyclicExocyclicObservationBoundedIn n monocyclicPolicy observation
  | .ringAssemblyAxes observation => axesObservationBoundedIn n assemblyPolicy observation
  | .ringAssemblyCenters observation =>
      centersObservationBoundedIn n assemblyPolicy observation
  | .ringAssemblyDoubleBonds observation =>
      doubleBondsObservationBoundedIn n assemblyPolicy observation

/-- The source-side normalization-recomputation condition.  It is the fourth conjunct of the
ring-assembly axes row's own `ValidFor` and vacuous for every other combined constructor. -/
def SourceCyclicObservation.NormalizationFixed
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} :
    SourceCyclicObservation monocyclicPolicy assemblyPolicy → Prop
  | .ringAssemblyAxes observation =>
      observation.normalization = normalizeRawMolecule observation.normalization.parsed
  | _ => True

/-- The native-side raw-syntax normalization condition; vacuous except for the axes row. -/
def CyclicObservation.RawSyntaxNormalized {V : Type*}
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} :
    CyclicObservation V monocyclicPolicy assemblyPolicy → Prop
  | .ringAssemblyAxes observation => RawMoleculeNormalized observation.parsed
  | _ => True

/-- Relabel one combined source observation, constructor by constructor, through the accepted
per-record codecs. -/
def relabelCyclicObservation {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n) :
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy) →
      observation.BoundedIn n → CyclicObservation V monocyclicPolicy assemblyPolicy
  | .monocyclicPhysicalUnit observation, bounded =>
      .monocyclicPhysicalUnit (relabelMonocyclicPhysicalUnit enumeration observation bounded)
  | .monocyclicGeneral observation, bounded =>
      .monocyclicGeneral
        (relabelMonocyclicGeneralAssignment enumeration monocyclicPolicy observation bounded)
  | .monocyclicCenter observation, bounded =>
      .monocyclicCenter
        (relabelMonocyclicCenterAuthorityObservation enumeration monocyclicPolicy observation
          bounded)
  | .monocyclicCisTrans observation, bounded =>
      .monocyclicCisTrans
        (relabelMonocyclicCisTransAuthorityObservation enumeration monocyclicPolicy observation
          bounded)
  | .monocyclicRCT observation, bounded =>
      .monocyclicRCT
        (relabelMonocyclicRCTAuthorityObservation enumeration monocyclicPolicy observation
          bounded)
  | .monocyclicUnsaturation observation, bounded =>
      .monocyclicUnsaturation
        (relabelMonocyclicUnsaturationAuthorityObservation enumeration monocyclicPolicy
          observation bounded)
  | .monocyclicDoubleBond observation, bounded =>
      .monocyclicDoubleBond
        (relabelMonocyclicDoubleBondAuthorityObservation enumeration monocyclicPolicy observation
          bounded)
  | .monocyclicExocyclic observation, bounded =>
      .monocyclicExocyclic
        (relabelMonocyclicExocyclicAuthorityObservation enumeration monocyclicPolicy observation
          bounded)
  | .ringAssemblyAxes observation, bounded =>
      .ringAssemblyAxes
        (relabelRingAssemblyAxesObservation enumeration assemblyPolicy observation bounded)
  | .ringAssemblyCenters observation, bounded =>
      .ringAssemblyCenters
        (relabelRingAssemblyCentersObservation enumeration assemblyPolicy observation bounded)
  | .ringAssemblyDoubleBonds observation, bounded =>
      .ringAssemblyDoubleBonds
        (relabelRingAssemblyDoubleBondsObservation enumeration assemblyPolicy observation bounded)

/-- Decode one combined native observation to the exact pre-existing carrier record. -/
def unrelabelCyclicObservation {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n) :
    CyclicObservation V monocyclicPolicy assemblyPolicy →
      SourceCyclicObservation monocyclicPolicy assemblyPolicy
  | .monocyclicPhysicalUnit observation =>
      .monocyclicPhysicalUnit (unrelabelMonocyclicPhysicalUnit enumeration observation)
  | .monocyclicGeneral observation =>
      .monocyclicGeneral
        (unrelabelMonocyclicGeneralAssignment enumeration monocyclicPolicy observation)
  | .monocyclicCenter observation =>
      .monocyclicCenter
        (unrelabelMonocyclicCenterAuthorityObservation enumeration monocyclicPolicy observation)
  | .monocyclicCisTrans observation =>
      .monocyclicCisTrans
        (unrelabelMonocyclicCisTransAuthorityObservation enumeration monocyclicPolicy observation)
  | .monocyclicRCT observation =>
      .monocyclicRCT
        (unrelabelMonocyclicRCTAuthorityObservation enumeration monocyclicPolicy observation)
  | .monocyclicUnsaturation observation =>
      .monocyclicUnsaturation
        (unrelabelMonocyclicUnsaturationAuthorityObservation enumeration monocyclicPolicy
          observation)
  | .monocyclicDoubleBond observation =>
      .monocyclicDoubleBond
        (unrelabelMonocyclicDoubleBondAuthorityObservation enumeration monocyclicPolicy
          observation)
  | .monocyclicExocyclic observation =>
      .monocyclicExocyclic
        (unrelabelMonocyclicExocyclicAuthorityObservation enumeration monocyclicPolicy
          observation)
  | .ringAssemblyAxes observation =>
      .ringAssemblyAxes
        (unrelabelRingAssemblyAxesObservation enumeration assemblyPolicy observation)
  | .ringAssemblyCenters observation =>
      .ringAssemblyCenters
        (unrelabelRingAssemblyCentersObservation enumeration assemblyPolicy observation)
  | .ringAssemblyDoubleBonds observation =>
      .ringAssemblyDoubleBonds
        (unrelabelRingAssemblyDoubleBondsObservation enumeration assemblyPolicy observation)

/-- Exact recovery of every combined source observation record, constructor by constructor.  The
axes branch uses the normalization equality that the carrier's own `ValidFor` supplies; all other
branches need only their explicit bounds. -/
theorem unrelabelCyclicObservation_relabelCyclicObservation
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
    (bounded : observation.BoundedIn n)
    (normalizationFixed : observation.NormalizationFixed) :
    unrelabelCyclicObservation enumeration
        (relabelCyclicObservation enumeration observation bounded) = observation := by
  cases observation with
  | monocyclicPhysicalUnit observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        unrelabelMonocyclicPhysicalUnit_relabelMonocyclicPhysicalUnit]
  | monocyclicGeneral observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        unrelabelMonocyclicGeneralAssignment_relabelMonocyclicGeneralAssignment]
  | monocyclicCenter observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        unrelabelMonocyclicCenterAuthorityObservation_relabel]
  | monocyclicCisTrans observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        unrelabelMonocyclicCisTransAuthorityObservation_relabel]
  | monocyclicRCT observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        unrelabelMonocyclicRCTAuthorityObservation_relabel]
  | monocyclicUnsaturation observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        unrelabelMonocyclicUnsaturationAuthorityObservation_relabel]
  | monocyclicDoubleBond observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        unrelabelMonocyclicDoubleBondAuthorityObservation_relabel]
  | monocyclicExocyclic observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        unrelabelMonocyclicExocyclicAuthorityObservation_relabel]
  | ringAssemblyAxes observation =>
      change SourceCyclicObservation.ringAssemblyAxes
        (unrelabelRingAssemblyAxesObservation enumeration assemblyPolicy
          (relabelRingAssemblyAxesObservation enumeration assemblyPolicy observation bounded)) =
        SourceCyclicObservation.ringAssemblyAxes observation
      rw [unrelabelRingAssemblyAxesObservation_relabel enumeration assemblyPolicy observation
        bounded normalizationFixed]
  | ringAssemblyCenters observation =>
      change SourceCyclicObservation.ringAssemblyCenters
        (unrelabelRingAssemblyCentersObservation enumeration assemblyPolicy
          (relabelRingAssemblyCentersObservation enumeration assemblyPolicy observation
            bounded)) =
        SourceCyclicObservation.ringAssemblyCenters observation
      rw [unrelabelRingAssemblyCentersObservation_relabel enumeration assemblyPolicy observation
        bounded]
  | ringAssemblyDoubleBonds observation =>
      change SourceCyclicObservation.ringAssemblyDoubleBonds
        (unrelabelRingAssemblyDoubleBondsObservation enumeration assemblyPolicy
          (relabelRingAssemblyDoubleBondsObservation enumeration assemblyPolicy observation
            bounded)) =
        SourceCyclicObservation.ringAssemblyDoubleBonds observation
      rw [unrelabelRingAssemblyDoubleBondsObservation_relabel enumeration assemblyPolicy
        observation bounded]

/-- Bounds of a decoded combined observation. -/
def unrelabelCyclicObservationBounded {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n) :
    (observation : CyclicObservation V monocyclicPolicy assemblyPolicy) →
      (unrelabelCyclicObservation enumeration observation).BoundedIn n
  | .monocyclicPhysicalUnit observation =>
      ⟨unrelabelList_bounded enumeration observation.ringAtoms,
        unrelabelUnitBounded enumeration observation.unit⟩
  | .monocyclicGeneral observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .monocyclicCenter observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .monocyclicCisTrans observation =>
      ⟨unrelabelList_bounded enumeration observation.ringAtoms,
        encodeAtom_lt enumeration observation.firstRingPosition,
        encodeAtom_lt enumeration observation.secondRingPosition,
        encodeAtom_lt enumeration observation.firstSubstituent,
        encodeAtom_lt enumeration observation.secondSubstituent⟩
  | .monocyclicRCT observation =>
      ⟨unrelabelList_bounded enumeration observation.ringAtoms,
        unrelabelMonocyclicRCTCandidatesBounded enumeration observation.candidates,
        ⟨encodeAtom_lt enumeration observation.selected.ringPosition,
          encodeAtom_lt enumeration observation.selected.substituent⟩,
        unrelabelMonocyclicRCTLocatedAssignmentsBounded enumeration observation.assignments⟩
  | .monocyclicUnsaturation observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .monocyclicDoubleBond observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .monocyclicExocyclic observation =>
      ⟨unrelabelList_bounded enumeration observation.physical.ringAtoms,
        unrelabelUnitBounded enumeration observation.physical.unit⟩
  | .ringAssemblyAxes observation =>
      unrelabelRingAssemblyAxesObservationBounded enumeration assemblyPolicy observation
  | .ringAssemblyCenters observation =>
      unrelabelRingAssemblyCentersObservationBounded enumeration assemblyPolicy observation
  | .ringAssemblyDoubleBonds observation =>
      unrelabelRingAssemblyDoubleBondsObservationBounded enumeration assemblyPolicy observation

/-- Relabelling a decoded combined observation returns the supplied observation.  The axes branch
carries the explicit raw-syntax-normalized hypothesis; no other branch needs it. -/
theorem relabelCyclicObservation_unrelabelCyclicObservation
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observation : CyclicObservation V monocyclicPolicy assemblyPolicy)
    (rawSyntaxNormalized : observation.RawSyntaxNormalized) :
    relabelCyclicObservation enumeration
        (unrelabelCyclicObservation enumeration observation)
        (unrelabelCyclicObservationBounded enumeration observation) = observation := by
  cases observation with
  | monocyclicPhysicalUnit observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        relabelMonocyclicPhysicalUnit_unrelabelMonocyclicPhysicalUnit]
  | monocyclicGeneral observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        relabelMonocyclicGeneralAssignment_unrelabelMonocyclicGeneralAssignment]
  | monocyclicCenter observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        relabelMonocyclicCenterAuthorityObservation_unrelabel]
  | monocyclicCisTrans observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        relabelMonocyclicCisTransAuthorityObservation_unrelabel]
  | monocyclicRCT observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        relabelMonocyclicRCTAuthorityObservation_unrelabel]
  | monocyclicUnsaturation observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        relabelMonocyclicUnsaturationAuthorityObservation_unrelabel]
  | monocyclicDoubleBond observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        relabelMonocyclicDoubleBondAuthorityObservation_unrelabel]
  | monocyclicExocyclic observation =>
      simp [relabelCyclicObservation, unrelabelCyclicObservation,
        relabelMonocyclicExocyclicAuthorityObservation_unrelabel]
  | ringAssemblyAxes observation =>
      change CyclicObservation.ringAssemblyAxes
        (relabelRingAssemblyAxesObservation enumeration assemblyPolicy
          (unrelabelRingAssemblyAxesObservation enumeration assemblyPolicy observation)
          (unrelabelRingAssemblyAxesObservationBounded enumeration assemblyPolicy observation)) =
        CyclicObservation.ringAssemblyAxes observation
      rw [relabelRingAssemblyAxesObservation_unrelabel enumeration assemblyPolicy observation
        rawSyntaxNormalized]
  | ringAssemblyCenters observation =>
      change CyclicObservation.ringAssemblyCenters
        (relabelRingAssemblyCentersObservation enumeration assemblyPolicy
          (unrelabelRingAssemblyCentersObservation enumeration assemblyPolicy observation)
          (unrelabelRingAssemblyCentersObservationBounded enumeration assemblyPolicy observation)) =
        CyclicObservation.ringAssemblyCenters observation
      rw [relabelRingAssemblyCentersObservation_unrelabel enumeration assemblyPolicy observation]
  | ringAssemblyDoubleBonds observation =>
      change CyclicObservation.ringAssemblyDoubleBonds
        (relabelRingAssemblyDoubleBondsObservation enumeration assemblyPolicy
          (unrelabelRingAssemblyDoubleBondsObservation enumeration assemblyPolicy observation)
          (unrelabelRingAssemblyDoubleBondsObservationBounded enumeration assemblyPolicy
            observation)) =
        CyclicObservation.ringAssemblyDoubleBonds observation
      rw [relabelRingAssemblyDoubleBondsObservation_unrelabel enumeration assemblyPolicy
        observation]

/-! ## Validity at the same source and policy -/

/-- `ValidFor` of a combined source observation: dispatch onto each constructor's own existing
predicate at the exact same source and the exact same policy. -/
def SourceCyclicObservation.ValidFor {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy}
    (source : AuthoritativeChemicalInput) :
    SourceCyclicObservation monocyclicPolicy assemblyPolicy → Prop
  | .monocyclicPhysicalUnit observation => observation.ValidFor monocyclicPolicy source
  | .monocyclicGeneral observation => observation.ValidFor monocyclicPolicy source
  | .monocyclicCenter observation => observation.ValidFor monocyclicPolicy source
  | .monocyclicCisTrans observation => observation.ValidFor monocyclicPolicy source
  | .monocyclicRCT observation => observation.ValidFor monocyclicPolicy source
  | .monocyclicUnsaturation observation => observation.ValidFor monocyclicPolicy source
  | .monocyclicDoubleBond observation => observation.ValidFor monocyclicPolicy source
  | .monocyclicExocyclic observation => observation.ValidFor monocyclicPolicy source
  | .ringAssemblyAxes observation => observation.ValidFor assemblyPolicy source
  | .ringAssemblyCenters observation => observation.ValidFor assemblyPolicy source
  | .ringAssemblyDoubleBonds observation => observation.ValidFor assemblyPolicy source

/-- The axes normalization equality is a conjunct of the carrier's own axes `ValidFor`, so it is
derived for the combined tag, never assumed. -/
theorem SourceCyclicObservation.normalizationFixed_of_validFor
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy}
    (source : AuthoritativeChemicalInput)
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
    (valid : observation.ValidFor source) :
    observation.NormalizationFixed := by
  cases observation with
  | monocyclicPhysicalUnit observation => trivial
  | monocyclicGeneral observation => trivial
  | monocyclicCenter observation => trivial
  | monocyclicCisTrans observation => trivial
  | monocyclicRCT observation => trivial
  | monocyclicUnsaturation observation => trivial
  | monocyclicDoubleBond observation => trivial
  | monocyclicExocyclic observation => trivial
  | ringAssemblyAxes observation => exact valid.2.2.2.1
  | ringAssemblyCenters observation => trivial
  | ringAssemblyDoubleBonds observation => trivial

/-- Bounds derived from the actual `ValidFor` of a combined source observation, using each
constructor's accepted bound derivation. -/
theorem SourceCyclicObservation.boundedIn_of_validFor
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy}
    (source : AuthoritativeChemicalInput)
    (structurallyWellFormed : source.molecule.StructurallyWellFormed)
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
    (valid : observation.ValidFor source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    observation.BoundedIn source.molecule.atomCount := by
  cases observation with
  | monocyclicPhysicalUnit observation =>
      exact monocyclicPhysicalUnitBoundedIn_of_validFor source monocyclicPolicy observation
        valid spatialWellFormed
  | monocyclicGeneral observation =>
      exact generalAssignmentBoundedIn_of_validFor source monocyclicPolicy observation valid
        spatialWellFormed
  | monocyclicCenter observation =>
      exact centerObservationBoundedIn_of_validFor source monocyclicPolicy observation valid
        spatialWellFormed
  | monocyclicCisTrans observation =>
      exact cisTransObservationBoundedIn_of_validFor source monocyclicPolicy observation valid
        structurallyWellFormed
  | monocyclicRCT observation =>
      exact rctObservationBoundedIn_of_validFor source monocyclicPolicy observation valid
        structurallyWellFormed
  | monocyclicUnsaturation observation =>
      exact unsaturationObservationBoundedIn_of_validFor source monocyclicPolicy observation
        valid spatialWellFormed
  | monocyclicDoubleBond observation =>
      exact doubleBondObservationBoundedIn_of_validFor source monocyclicPolicy observation valid
        spatialWellFormed
  | monocyclicExocyclic observation =>
      exact exocyclicObservationBoundedIn_of_validFor source monocyclicPolicy observation valid
        spatialWellFormed
  | ringAssemblyAxes observation =>
      exact SourceRingAssemblyObservation.boundedIn_of_validFor source
        (SourceRingAssemblyObservation.axes observation) valid structurallyWellFormed
        spatialWellFormed
  | ringAssemblyCenters observation =>
      exact SourceRingAssemblyObservation.boundedIn_of_validFor source
        (SourceRingAssemblyObservation.centers observation) valid structurallyWellFormed
        spatialWellFormed
  | ringAssemblyDoubleBonds observation =>
      exact SourceRingAssemblyObservation.boundedIn_of_validFor source
        (SourceRingAssemblyObservation.doubleBonds observation) valid structurallyWellFormed
        spatialWellFormed

/-- Bounds of a combined observation derived from its validity and the exact source binding. -/
theorem SourceCyclicObservation.boundedIn_of_validFor_binding
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy}
    [DecidableEq V] [Fintype V]
    (binding : MonocyclicRingAssemblySourceBinding V)
    (structurallyWellFormed : binding.source.molecule.StructurallyWellFormed)
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
    (valid : observation.ValidFor binding.source) :
    observation.BoundedIn (Fintype.card V) := by
  have bounded := SourceCyclicObservation.boundedIn_of_validFor binding.source
    structurallyWellFormed observation valid binding.spatial_wellFormed
  rwa [binding.atomCount_eq] at bounded

/-! ## Ordered heterogeneous lists -/

/-- Relabel an ordered heterogeneous list of combined source observations. -/
def relabelCyclicObservationList {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    List (CyclicObservation V monocyclicPolicy assemblyPolicy) :=
  observations.attach.map fun observation =>
    relabelCyclicObservation enumeration observation.1
      (bounded observation.1 observation.2)

/-- Decode an ordered heterogeneous list of combined native observations. -/
def unrelabelCyclicObservationList {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (CyclicObservation V monocyclicPolicy assemblyPolicy)) :
    List (SourceCyclicObservation monocyclicPolicy assemblyPolicy) :=
  observations.map (unrelabelCyclicObservation enumeration)

/-- Every decoded element of a combined list satisfies the same explicit bounds. -/
def unrelabelCyclicObservationListBounded
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (CyclicObservation V monocyclicPolicy assemblyPolicy)) :
    ∀ observation ∈ unrelabelCyclicObservationList enumeration observations,
      observation.BoundedIn n := by
  intro observation member
  rw [unrelabelCyclicObservationList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelCyclicObservationBounded enumeration presented

@[simp] theorem relabelCyclicObservationList_length
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    (relabelCyclicObservationList enumeration observations bounded).length =
      observations.length := by
  simp [relabelCyclicObservationList]

@[simp] theorem unrelabelCyclicObservationList_length
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (CyclicObservation V monocyclicPolicy assemblyPolicy)) :
    (unrelabelCyclicObservationList enumeration observations).length =
      observations.length := by
  simp [unrelabelCyclicObservationList]

/-- Exact recovery of the ordered combined observation list, including order, multiplicity and
each concrete record shape. -/
theorem unrelabelCyclicObservationList_relabelCyclicObservationList
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (normalizationFixed : ∀ observation ∈ observations, observation.NormalizationFixed) :
    unrelabelCyclicObservationList enumeration
        (relabelCyclicObservationList enumeration observations bounded) = observations := by
  unfold unrelabelCyclicObservationList relabelCyclicObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact unrelabelCyclicObservation_relabelCyclicObservation enumeration observation.1
      (bounded observation.1 observation.2)
      (normalizationFixed observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-- Relabelling a decoded combined list returns the supplied list. -/
theorem relabelCyclicObservationList_unrelabelCyclicObservationList
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (CyclicObservation V monocyclicPolicy assemblyPolicy))
    (rawSyntaxNormalized : ∀ observation ∈ observations, observation.RawSyntaxNormalized) :
    relabelCyclicObservationList enumeration
        (unrelabelCyclicObservationList enumeration observations)
        (unrelabelCyclicObservationListBounded enumeration observations) = observations := by
  unfold relabelCyclicObservationList unrelabelCyclicObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelCyclicObservation_unrelabelCyclicObservation enumeration observation.1
      (rawSyntaxNormalized observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-! ## Arbitrary correlated sets of combined observations -/

/-- Image of an arbitrary set of combined source observations under the combined codec. -/
def relabelCyclicObservationSet {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    Set (CyclicObservation V monocyclicPolicy assemblyPolicy) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelCyclicObservation enumeration observation (bounded observation member) = presented

/-- Preimage of an arbitrary set of combined native observations under the combined codec. -/
def unrelabelCyclicObservationSet {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (CyclicObservation V monocyclicPolicy assemblyPolicy)) :
    Set (SourceCyclicObservation monocyclicPolicy assemblyPolicy) :=
  fun recovered =>
    ∃ presented ∈ observations,
      unrelabelCyclicObservation enumeration presented = recovered

/-- Every decoded element of the image set satisfies the explicit bounds. -/
def unrelabelCyclicObservationSetBounded
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (CyclicObservation V monocyclicPolicy assemblyPolicy)) :
    ∀ observation ∈ unrelabelCyclicObservationSet enumeration observations,
      observation.BoundedIn n := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact unrelabelCyclicObservationBounded enumeration presented

/-- The correlated-set inverse on the source side, for an arbitrary set. -/
theorem unrelabelCyclicObservationSet_relabelCyclicObservationSet
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (normalizationFixed : ∀ observation ∈ observations, observation.NormalizationFixed) :
    unrelabelCyclicObservationSet enumeration
        (relabelCyclicObservationSet enumeration observations bounded) = observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [unrelabelCyclicObservation_relabelCyclicObservation enumeration observation
      (bounded observation member) (normalizationFixed observation member)] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelCyclicObservation enumeration recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      unrelabelCyclicObservation_relabelCyclicObservation enumeration recovered
        (bounded recovered member) (normalizationFixed recovered member)⟩

/-- The relabelling of a combined observation does not inspect the proof of its boundedness. -/
theorem relabelCyclicObservation_bound_irrel
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
    (first second : observation.BoundedIn n) :
    relabelCyclicObservation enumeration observation first =
      relabelCyclicObservation enumeration observation second := by
  cases observation <;> rfl

/-- Relabelling respects equality of the underlying combined source observation, independently of
how the two boundedness proofs were obtained. -/
theorem relabelCyclicObservation_congr
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    {first second : SourceCyclicObservation monocyclicPolicy assemblyPolicy} (h : first = second)
    (firstBounded : first.BoundedIn n) (secondBounded : second.BoundedIn n) :
    relabelCyclicObservation enumeration first firstBounded =
      relabelCyclicObservation enumeration second secondBounded := by
  cases h
  exact relabelCyclicObservation_bound_irrel enumeration _ firstBounded secondBounded

/-- The correlated-set inverse on the native side, for an arbitrary set. -/
theorem relabelCyclicObservationSet_unrelabelCyclicObservationSet
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (CyclicObservation V monocyclicPolicy assemblyPolicy))
    (rawSyntaxNormalized : ∀ observation ∈ observations, observation.RawSyntaxNormalized) :
    relabelCyclicObservationSet enumeration
        (unrelabelCyclicObservationSet enumeration observations)
        (unrelabelCyclicObservationSetBounded enumeration observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have roundTrip : relabelCyclicObservation enumeration
        (unrelabelCyclicObservation enumeration presented₀)
        (unrelabelCyclicObservationBounded enumeration presented₀) = presented₀ :=
      relabelCyclicObservation_unrelabelCyclicObservation enumeration presented₀
        (rawSyntaxNormalized presented₀ presentedMember)
    have relabelEq' : relabelCyclicObservation enumeration
        (unrelabelCyclicObservation enumeration presented₀)
        (unrelabelCyclicObservationBounded enumeration presented₀) = presented := by
      simpa only [decodeEq] using relabelEq
    have presentedEq : presented = presented₀ := by
      rw [← relabelEq', roundTrip]
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨unrelabelCyclicObservation enumeration presented,
      ⟨presented, member, rfl⟩,
      relabelCyclicObservation_unrelabelCyclicObservation enumeration presented
        (rawSyntaxNormalized presented member)⟩

/-- **Correlated validity for an arbitrary combined set.**  A native observation belongs to the
image of a set exactly when its decoded record is one of the source observations; consequently its
`ValidFor` at the same source and policies is exactly the validity of that source observation. -/
theorem validFor_mem_relabelCyclicObservationSet_iff
    {monocyclicPolicy : P93MonocyclicAuthorityPolicy}
    {assemblyPolicy : P93RingAssemblyAuthorityPolicy} [DecidableEq V]
    (enumeration : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (observations : Set (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (normalizationFixed : ∀ observation ∈ observations, observation.NormalizationFixed)
    (presented : CyclicObservation V monocyclicPolicy assemblyPolicy)
    (member : presented ∈
      relabelCyclicObservationSet enumeration observations bounded) :
    (unrelabelCyclicObservation enumeration presented).ValidFor source ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelCyclicObservation enumeration observation
            (bounded observation observationMember) = presented ∧
          observation.ValidFor source := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rwa [unrelabelCyclicObservation_relabelCyclicObservation enumeration observation
      (bounded observation observationMember)
      (normalizationFixed observation observationMember)] at valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rwa [unrelabelCyclicObservation_relabelCyclicObservation enumeration observation
      (bounded observation observationMember)
      (normalizationFixed observation observationMember)]

/-! ## The combined satellite with one shared source binding -/

variable {assemblyPolicy : P93RingAssemblyAuthorityPolicy}

/-- The combined source binding is the same accepted binding already used by the monocyclic and
ring-assembly satellites. -/
abbrev CyclicSourceBinding (V : Type*) [DecidableEq V] [Fintype V] :=
  MonocyclicRingAssemblySourceBinding V

/-- A raw combined source: one shared binding for both policies, the source's structural
certificate, and an ordered list of `Nat`-indexed combined carrier observations valid at the bound
source. -/
structure RawCyclicSource (V : Type*) [DecidableEq V] [Fintype V]
    (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy) where
  binding : CyclicSourceBinding V
  structurallyWellFormed : binding.source.molecule.StructurallyWellFormed
  observations : List (SourceCyclicObservation monocyclicPolicy assemblyPolicy)
  valid : ∀ observation ∈ observations, observation.ValidFor binding.source

/-- The combined native satellite.  It stores the shared graph/spatial/diagram context and the
ordered list of native combined observations.  No original observation and no original
`AuthoritativeChemicalInput` is stored here. -/
structure CyclicObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (CyclicObservation V monocyclicPolicy assemblyPolicy)

namespace CyclicObservationSatellite

variable [DecidableEq V] [Fintype V]

/-- The shared finite source, with observations intentionally excluded. -/
def toFiniteSource
    (satellite : CyclicObservationSatellite V monocyclicPolicy assemblyPolicy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end CyclicObservationSatellite

/-- Adapt a raw combined source into the satellite: keep the exact shared finite source and
relabel every observation, deriving the atom bounds from its actual `ValidFor`. -/
def adaptCyclic [DecidableEq V] [Fintype V]
    (raw : RawCyclicSource V monocyclicPolicy assemblyPolicy) :
    CyclicObservationSatellite V monocyclicPolicy assemblyPolicy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelCyclicObservation raw.binding.enumeration observation.1
      (SourceCyclicObservation.boundedIn_of_validFor_binding raw.binding
        raw.structurallyWellFormed observation.1 (raw.valid observation.1 observation.2))

@[simp] theorem adaptCyclic_graph [DecidableEq V] [Fintype V]
    (raw : RawCyclicSource V monocyclicPolicy assemblyPolicy) :
    (adaptCyclic raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adaptCyclic_spatial? [DecidableEq V] [Fintype V]
    (raw : RawCyclicSource V monocyclicPolicy assemblyPolicy) :
    (adaptCyclic raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adaptCyclic_diagram? [DecidableEq V] [Fintype V]
    (raw : RawCyclicSource V monocyclicPolicy assemblyPolicy) :
    (adaptCyclic raw).diagram? = raw.binding.shared.diagram? := rfl

/-- The adapted combined satellite's shared finite source is the binding's shared source
exactly. -/
@[simp] theorem adaptCyclic_toFiniteSource [DecidableEq V] [Fintype V]
    (raw : RawCyclicSource V monocyclicPolicy assemblyPolicy) :
    (adaptCyclic raw).toFiniteSource = raw.binding.shared := rfl

/-- The recovered combined source record: the exact authoritative input and the decoded ordered
observation list. -/
@[ext] structure RecoveredCyclicSource (monocyclicPolicy : P93MonocyclicAuthorityPolicy)
    (assemblyPolicy : P93RingAssemblyAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceCyclicObservation monocyclicPolicy assemblyPolicy)

/-- Decode a combined satellite into the recovered source record.  The authoritative input is the
exact encode of the shared finite source; observations are decoded with the same enumeration. -/
def cyclicSuppliedSource [DecidableEq V] [Fintype V]
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : CyclicObservationSatellite V monocyclicPolicy assemblyPolicy) :
    RecoveredCyclicSource monocyclicPolicy assemblyPolicy where
  source := satellite.toFiniteSource.encode enumeration
  observations := unrelabelCyclicObservationList enumeration satellite.observations

/-- **Exact whole-source and whole-list recovery.**  Adapting a raw combined source and decoding
it returns the exact authoritative input and the exact ordered list of pre-existing monocyclic and
ring-assembly observation records. -/
theorem cyclicSuppliedSource_adapt [DecidableEq V] [Fintype V]
    (raw : RawCyclicSource V monocyclicPolicy assemblyPolicy) :
    cyclicSuppliedSource raw.binding.enumeration (adaptCyclic raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredCyclicSource.ext
  · exact raw.binding.encode_shared
  · change unrelabelCyclicObservationList raw.binding.enumeration
      (adaptCyclic raw).observations = raw.observations
    rw [show (adaptCyclic raw).observations = raw.observations.attach.map (fun observation =>
        relabelCyclicObservation raw.binding.enumeration observation.1
          (SourceCyclicObservation.boundedIn_of_validFor_binding raw.binding
            raw.structurallyWellFormed observation.1
            (raw.valid observation.1 observation.2))) from rfl]
    exact unrelabelCyclicObservationList_relabelCyclicObservationList
      raw.binding.enumeration raw.observations
      (fun observation member =>
        SourceCyclicObservation.boundedIn_of_validFor_binding raw.binding
          raw.structurallyWellFormed observation (raw.valid observation member))
      (fun observation member =>
        SourceCyclicObservation.normalizationFixed_of_validFor raw.binding.source
          observation (raw.valid observation member))

/-- The recovered graph, spatial and diagram channels are exactly the original channels, and the
recovered observation list is exactly the original ordered list. -/
theorem cyclicSuppliedSource_adapt_channels [DecidableEq V] [Fintype V]
    (raw : RawCyclicSource V monocyclicPolicy assemblyPolicy) :
    (cyclicSuppliedSource raw.binding.enumeration (adaptCyclic raw)).source.molecule =
        raw.binding.source.molecule ∧
      (cyclicSuppliedSource raw.binding.enumeration (adaptCyclic raw)).source.spatial? =
        raw.binding.source.spatial? ∧
      (cyclicSuppliedSource raw.binding.enumeration (adaptCyclic raw)).source.diagram? =
        raw.binding.source.diagram? ∧
      (cyclicSuppliedSource raw.binding.enumeration (adaptCyclic raw)).observations =
        raw.observations := by
  simp [cyclicSuppliedSource_adapt]

/-- Validity is preserved for the whole recovered combined list at the same source and
policies. -/
theorem cyclicSuppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    (raw : RawCyclicSource V monocyclicPolicy assemblyPolicy)
    (observation : SourceCyclicObservation monocyclicPolicy assemblyPolicy)
    (member : observation ∈
      (cyclicSuppliedSource raw.binding.enumeration (adaptCyclic raw)).observations) :
    observation.ValidFor raw.binding.source := by
  have listEq : (cyclicSuppliedSource raw.binding.enumeration
      (adaptCyclic raw)).observations = raw.observations := by
    simpa using congrArg RecoveredCyclicSource.observations (cyclicSuppliedSource_adapt raw)
  have sourceMember : observation ∈ raw.observations := by
    rw [← listEq]
    exact member
  exact raw.valid observation sourceMember

/-! ## The concrete certified combined adapter -/

/-- The concrete binding of a certified authoritative input to its exact finite ingress source for
the combined carrier. -/
def cyclicCertifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    CyclicSourceBinding (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

/-- Adapt a certified source together with an ordered list of valid combined carrier
observations. -/
def adaptCertifiedCyclic (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    CyclicObservationSatellite (Fin certified.input.molecule.atomCount)
      monocyclicPolicy assemblyPolicy :=
  adaptCyclic { binding := cyclicCertifiedBinding certified
                structurallyWellFormed := certified.structurallyWellFormed.1
                observations := observations
                valid := valid }

/-- **Concrete exact combined recovery from a certified source.** -/
theorem cyclicSuppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    cyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedCyclic certified observations valid) =
      { source := certified.input, observations := observations } :=
  cyclicSuppliedSource_adapt
    { binding := cyclicCertifiedBinding certified
      structurallyWellFormed := certified.structurallyWellFormed.1
      observations := observations
      valid := valid }

/-- The certified combined adapter recovers the graph, spatial and diagram channels of the
certified input together with the exact ordered observation list. -/
theorem cyclicSuppliedSource_adaptCertified_channels
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceCyclicObservation monocyclicPolicy assemblyPolicy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    (cyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedCyclic certified observations valid)).source.molecule =
        certified.input.molecule ∧
      (cyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedCyclic certified observations valid)).source.spatial? =
        certified.input.spatial? ∧
      (cyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedCyclic certified observations valid)).source.diagram? =
        certified.input.diagram? ∧
      (cyclicSuppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertifiedCyclic certified observations valid)).observations =
        observations := by
  simp [cyclicSuppliedSource_adaptCertified]

end

end OrganicStereoMonocyclicRingAssemblyIngress

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.unrelabelRingAssemblyObservation_relabelRingAssemblyObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.relabelRingAssemblyObservation_unrelabelRingAssemblyObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.unrelabelRingAssemblyObservationSet_relabelRingAssemblyObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.validFor_mem_relabelRingAssemblyObservationSet_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.suppliedSource_adaptCertified
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.SourceRingAssemblyObservation.boundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.axisAssignmentBoundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.monocyclicSuppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.monocyclicSuppliedSource_adaptCertified
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservation_relabelCyclicObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.relabelCyclicObservation_unrelabelCyclicObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservationList_relabelCyclicObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.relabelCyclicObservationList_unrelabelCyclicObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.unrelabelCyclicObservationSet_relabelCyclicObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.relabelCyclicObservationSet_unrelabelCyclicObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.validFor_mem_relabelCyclicObservationSet_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.cyclicSuppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.cyclicSuppliedSource_adaptCertified
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation.boundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress.SourceCyclicObservation.normalizationFixed_of_validFor
