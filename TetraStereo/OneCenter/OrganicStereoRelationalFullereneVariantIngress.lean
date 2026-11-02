import TetraStereo.OneCenter.OrganicStereoRelationalFullereneInputEncoding

set_option autoImplicit false

/-!
# Native variant ingress for the three relational P-93 fullerene authority forms

The approved successor codec `OrganicStereoRelationalFullereneInputEncoding` covers the common
relational observation `P93RelationalFullereneAuthorityObservation`.  It does not cover the three
*additional* source-side authority forms that `IUPACP93RelationalFullereneAuthorityCarrier`
introduces:

* `P93RelationalFullereneHandedAuthorityObservation` -- a common relational observation plus one
  source-authorized `numberingKind` and `handedness` (Types 1--3);
* `P93RelationalFullereneType4AuthorityObservation` -- a *different* shape: it has a
  `RelationalSymmetryDerivedMolecularFullereneConfigurationInput` only, with no printed cage
  numbering record and no turn source, because the Type-4 row reports substituent CIP only;
* `P93RelationalFullereneSuperimposedAuthorityObservation` -- a wrapper around one handed
  observation.

This module supplies a concrete raw/native variant union with three distinct tags and a complete
field-by-field codec for all three shapes.

## What is reused, not reinvented

* For `handed` and `superimposed`, the whole common observation is encoded with the approved
  `OrganicStereoRelationalFullereneInputEncoding.relabelObservation` /
  `unrelabelObservation` full native base.  That base already encodes the ordered input family,
  the selected input, every ordered addend with its complete ordered attachment-port set and
  identity class, the chiral-addend `Finset`, the assignment unit, the chirality type, the
  descriptor payload list and the whole substituent CIP corpus (owners, typed units, citations
  and descriptors).  Nothing is projected to attachment sites and no original source record is
  stored.
* For `type4`, the relational symmetry-derived input is encoded with the approved
  `encodeRelationalSymmetryInput` / `decodeRelationalSymmetryInput`, and the assignment unit and
  substituent corpus use the approved `relabelList` / `relabelSubstituentAssignments` codecs.
  The Type-4 shape keeps its own source record.  No numbering kind and no turn source is
  invented for it: the source structure has neither, and the native structure has neither.

## Bounds

The native atom-reference codec used inside `encodeRelationalSymmetryInput` is total, so no bound
is needed for the input evidence.  The fields that are relabelled onto the finite graph type `V`
(the assignment unit and the substituent corpus) do need bounds.  They are derived from the
carrier's own `ValidFor` and the exact atom-count agreement of the physical-frame binding, never
assumed.

## Native validity is indexed by decoded data

The native satellite stores no original observation and no `CertifiedAuthoritativeChemicalInput`.
Its `valid` field is a proof about the *decoded* source observations:

`(decodeVariant e (encodeSpatial? e spatial?) observation).ValidFor policy source`

where `source` is exactly the encoding of the satellite's shared finite source.  This is the
source-side validity restated as a native proof indexed by the actual decoded data.

## Exactness

Source-to-native-to-source reconstruction is unconditional for every observation whose stored
spatial channel is the one observed at the fixed source.  The converse direction is not claimed:
the native reference codec normalizes an out-of-range-representable `.unresolved` reference to
`.resolved`, exactly as documented by the approved base.  Ordered lists stay ordered and the
three tags stay distinct.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic
open OrganicStereoP93PhysicalFrameIngress
open OrganicStereoSuppliedCitationIngress
open OrganicStereoFullereneAuthorityIngress
open OrganicStereoRelationalFullereneIngress
open OrganicStereoRelationalFullereneInputEncoding

namespace OrganicStereoRelationalFullereneVariantIngress

variable {V : Type*} [DecidableEq V] {n : Nat}
  {policy : P93RelationalFullereneAuthorityPolicy}

/-! ## Type-4 boundedness

A Type-4 observation has no observation-level addend list: its addends live inside the
symmetry-derived input evidence and are already encoded by the total native reference codec.
Only the assignment unit and the substituent corpus are written onto `V`, so only those two
fields need bounds. -/

/-- Bounds for the fields of a Type-4 observation that are relabelled onto `V`. -/
def type4ObservationBoundedIn (n : Nat)
    (observation : P93RelationalFullereneType4AuthorityObservation policy) : Prop :=
  (∀ atom ∈ observation.assignment.unit, atom < n) ∧
    ∀ assignment ∈ observation.substituentAssignments,
      substituentAssignmentBoundedIn n assignment

/-! ## The source-side variant union -/

/-- The three additional source authority observation forms, tagged distinctly.  Every branch
retains the complete source record; no branch stores a projection or a weakened hypothesis. -/
inductive SourceRelationalVariantObservation
    (policy : P93RelationalFullereneAuthorityPolicy) where
  /-- Types 1--3: the common relational observation plus one printed cage handedness. -/
  | handed (observation : P93RelationalFullereneHandedAuthorityObservation policy)
  /-- Type 4: symmetry-derived input only, with neither numbering nor turn. -/
  | type4 (observation : P93RelationalFullereneType4AuthorityObservation policy)
  /-- Superimposed: a handed observation wrappper. -/
  | superimposed (observation : P93RelationalFullereneSuperimposedAuthorityObservation policy)

namespace SourceRelationalVariantObservation

/-- Source-side validity of one tagged observation, at the exact source and policy.  The policy
is inferred from the tag's type, so no policy is separately manufactured. -/
def ValidFor (observation : SourceRelationalVariantObservation policy)
    (source : AuthoritativeChemicalInput) : Prop :=
  match observation with
  | .handed o => o.ValidFor policy source
  | .type4 o => o.ValidFor policy source
  | .superimposed o => o.ValidFor policy source

/-- The stored spatial channel of one tagged observation.  For `handed` and `superimposed` it is
the base observation's channel; for `type4` it is the Type-4 record's own channel. -/
def spatial? (observation : SourceRelationalVariantObservation policy) :
    Option SpatialConfiguration :=
  match observation with
  | .handed o => o.base.spatial?
  | .type4 o => o.spatial?
  | .superimposed o => o.handed.base.spatial?

/-- The raw molecule carried by one tagged observation.  It is provenance only; it never
substitutes for an atom occurrence. -/
def molecule (observation : SourceRelationalVariantObservation policy) : RawMolecule :=
  match observation with
  | .handed o => o.base.molecule
  | .type4 o => o.molecule
  | .superimposed o => o.handed.base.molecule

/-- The boundedness needed to write a tagged observation into the finite atom type `V`.  Each
branch names exactly the fields that the codec relabels onto `V`. -/
def BoundedIn (observation : SourceRelationalVariantObservation policy) (n : Nat) : Prop :=
  match observation with
  | .handed o => relationalObservationBoundedIn n o.base
  | .type4 o => type4ObservationBoundedIn n o
  | .superimposed o => relationalObservationBoundedIn n o.handed.base

end SourceRelationalVariantObservation

/-! ## Type-4 bounds derived from its own authority validity -/

/-- Atom-count agreement for one valid Type-4 observation.  It is a consequence of the exact
topology representation agreement and the binding's own graph equality. -/
theorem type4ObservationAtomCount_eq [Fintype V]
    (binding : PhysicalFrameSourceBinding V)
    (observation : P93RelationalFullereneType4AuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    observation.molecule.atomCount = Fintype.card V := by
  rw [← RawMolecule.toMolecularFullereneTopologySemanticMolecule?_atomCount
    observation.molecule observation.input.cage.carrier binding.source.molecule
    valid.structureAgreement.1]
  exact binding.atomCount_eq

/-- Every relabelled Type-4 field is bounded, using only the observation's own `ValidFor` and the
exact atom-count agreement.  No new atom bound is introduced. -/
theorem type4ObservationBoundedIn_of_validFor
    {source : AuthoritativeChemicalInput}
    {observation : P93RelationalFullereneType4AuthorityObservation policy} {n : Nat}
    (atomCountEq : observation.molecule.atomCount = n)
    (valid : observation.ValidFor policy source) :
    type4ObservationBoundedIn n observation := by
  have oriented : OrientedMolecularFullereneFaceMapJudgment
      observation.molecule observation.input.cage := valid.inputJudged
  have carrierJudged : MolecularFullereneCarrierJudgment
      observation.molecule observation.input.cage := oriented.1
  have cageBound : ∀ atom ∈ observation.input.cage.carrier, atom < n := by
    intro atom member
    obtain ⟨spec, atomAt, _carbon⟩ := carrierJudged.carbonAtoms atom member
    have lookup := listGet?_eq_some_implies_lt observation.molecule.atoms atom spec atomAt
    have counted : atom < observation.molecule.atomCount := by
      simpa [RawMolecule.atomCount] using lookup
    exact atomCountEq ▸ counted
  have carrierBound :
      ∀ atom ∈ observation.input.topologyInput.carrier, atom < n := by
    intro atom member
    exact cageBound atom (by simpa using member)
  have unitBound : ∀ atom ∈ observation.assignment.unit, atom < n := by
    intro atom member
    obtain ⟨chiralityType, payloads, _typeMatches, _payloadJudgment, assignmentEq⟩ :=
      valid.localAssignmentJudged
    have unitEq : observation.assignment.unit =
        observation.input.cage.toFullereneConfigurationInput.unit := by
      rw [assignmentEq]
    rw [unitEq] at member
    have carrierMember : atom ∈ observation.input.cage.carrier := by
      simpa [MolecularFullereneConfigurationInput.toFullereneConfigurationInput] using member
    exact cageBound atom carrierMember
  have corpusBound : ∀ assignment ∈ observation.substituentAssignments,
      substituentAssignmentBoundedIn n assignment := by
    intro assignment member
    exact substituentAssignmentBoundedIn_of_validFor carrierBound atomCountEq
      (valid.substituentCorpusComplete.assignmentsValid assignment member)
  exact ⟨unitBound, corpusBound⟩

/-! ## Native Type-4 observation -/

/-- One Type-4 observation over the finite atom type `V`.  The symmetry-derived input is the
approved native input record; the assignment is stored as its relabelled unit together with its
literal chirality type and payload list; the substituent corpus is the approved native record.
No numbering record and no turn source exists here, matching the source shape exactly. -/
structure NativeRelationalType4Observation (V : Type*) [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) where
  molecule : RawMolecule
  input : NativeRelationalSymmetryInput V e molecule
  assignmentUnit : List V
  chiralityType : FullereneChiralityType
  payloads : List FullereneDescriptorPayload
  substituentAssignments : List (SuppliedSubstituentCIPAssignment V)

/-- Encode one bounded Type-4 observation. -/
def encodeType4 {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (observation : P93RelationalFullereneType4AuthorityObservation policy)
    (bounded : type4ObservationBoundedIn n observation) :
    NativeRelationalType4Observation V e where
  molecule := observation.molecule
  input := encodeRelationalSymmetryInput e observation.molecule observation.input
  assignmentUnit := relabelList e observation.assignment.unit bounded.1
  chiralityType := observation.assignment.chiralityType
  payloads := observation.assignment.payloads
  substituentAssignments :=
    relabelSubstituentAssignments e observation.substituentAssignments bounded.2

/-- Decode one native Type-4 observation.  The spatial channel is supplied by the shared source,
never stored in the native payload. -/
def decodeType4 {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (spatial? : Option SpatialConfiguration)
    (observation : NativeRelationalType4Observation V e) :
    P93RelationalFullereneType4AuthorityObservation policy where
  molecule := observation.molecule
  spatial? := spatial?
  input := decodeRelationalSymmetryInput e observation.molecule observation.input
  assignment :=
    { unit := unrelabelList e observation.assignmentUnit
      chiralityType := observation.chiralityType
      payloads := observation.payloads }
  substituentAssignments :=
    unrelabelSubstituentAssignments e observation.substituentAssignments

/-- **Exact Type-4 recovery.**  The only side condition is the exact spatial-channel agreement
that the Type-4 source validity already supplies. -/
theorem decodeType4_encodeType4 {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (observation : P93RelationalFullereneType4AuthorityObservation policy)
    (bounded : type4ObservationBoundedIn n observation)
    (spatial? : Option SpatialConfiguration)
    (spatialExact : observation.spatial? = spatial?) :
    decodeType4 e spatial? (encodeType4 e observation bounded) = observation := by
  obtain ⟨molecule, spatial, input, assignment, substituentAssignments⟩ := observation
  subst spatialExact
  simp only [encodeType4, decodeType4,
    decodeRelationalSymmetryInput_encodeRelationalSymmetryInput,
    unrelabelList_relabelList,
    unrelabelSubstituentAssignments_relabelSubstituentAssignments]

/-! ## The native variant union -/

/-- One native tagged observation over the finite atom type `V`.  `handed` and `superimposed`
carry the approved full native base plus the printed numbering kind and handedness;
`superimposed` is a distinct tag, not an alias.  `type4` carries the Type-4 native shape. -/
inductive NativeRelationalVariantObservation (V : Type*) [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (policy : P93RelationalFullereneAuthorityPolicy) where
  | handed (base : NativeRelationalFullereneObservation V e policy)
      (numberingKind : FullereneNumberingKind) (handedness : FullereneHandedness)
  | type4 (observation : NativeRelationalType4Observation V e)
  | superimposed (base : NativeRelationalFullereneObservation V e policy)
      (numberingKind : FullereneNumberingKind) (handedness : FullereneHandedness)

variable {V : Type*} [DecidableEq V] {n : Nat}
  {policy : P93RelationalFullereneAuthorityPolicy}

/-! ### Encoding -/

/-- Encode one bounded source variant into the native union.  Each branch keeps its tag and every
role-bearing field; nothing is erased across tags. -/
def encodeVariant {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (observation : SourceRelationalVariantObservation policy)
    (bounded : observation.BoundedIn n) :
    NativeRelationalVariantObservation V e policy :=
  match observation with
  | .handed o =>
      .handed (relabelObservation e policy o.base bounded)
        o.numberingKind o.handedness
  | .type4 o => .type4 (encodeType4 e o bounded)
  | .superimposed o =>
      .superimposed (relabelObservation e policy o.handed.base bounded)
        o.handed.numberingKind o.handed.handedness

@[simp] theorem encodeVariant_handed {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (o : P93RelationalFullereneHandedAuthorityObservation policy)
    (bounded : (SourceRelationalVariantObservation.handed o).BoundedIn n) :
    encodeVariant e (.handed o) bounded =
      .handed (relabelObservation e policy o.base bounded)
        o.numberingKind o.handedness := rfl

@[simp] theorem encodeVariant_type4 {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (o : P93RelationalFullereneType4AuthorityObservation policy)
    (bounded : (SourceRelationalVariantObservation.type4 o).BoundedIn n) :
    encodeVariant e (.type4 o) bounded = .type4 (encodeType4 e o bounded) := rfl

@[simp] theorem encodeVariant_superimposed {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n)
    (o : P93RelationalFullereneSuperimposedAuthorityObservation policy)
    (bounded : (SourceRelationalVariantObservation.superimposed o).BoundedIn n) :
    encodeVariant e (.superimposed o) bounded =
      .superimposed (relabelObservation e policy o.handed.base bounded)
        o.handed.numberingKind o.handed.handedness := rfl

/-! ### Decoding -/

/-- Decode one native tagged observation.  The spatial channel is supplied by the shared source;
`handed` and `superimposed` decode through the approved full native base, and `type4` decodes
through the Type-4 codec without acquiring a numbering record or a turn. -/
def decodeVariant {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (spatial? : Option SpatialConfiguration) :
    NativeRelationalVariantObservation V e policy →
      SourceRelationalVariantObservation policy
  | .handed base numberingKind handedness =>
      .handed
        { base := unrelabelObservation e policy spatial? base
          numberingKind := numberingKind
          handedness := handedness }
  | .type4 observation => .type4 (decodeType4 e spatial? observation)
  | .superimposed base numberingKind handedness =>
      .superimposed
        { handed :=
            { base := unrelabelObservation e policy spatial? base
              numberingKind := numberingKind
              handedness := handedness } }

@[simp] theorem decodeVariant_handed {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (spatial? : Option SpatialConfiguration)
    (base : NativeRelationalFullereneObservation V e policy)
    (numberingKind : FullereneNumberingKind) (handedness : FullereneHandedness) :
    decodeVariant e spatial? (.handed base numberingKind handedness) =
      .handed
        { base := unrelabelObservation e policy spatial? base
          numberingKind := numberingKind
          handedness := handedness } := rfl

@[simp] theorem decodeVariant_type4 {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93RelationalFullereneAuthorityPolicy} (e : V ≃ Fin n)
    (spatial? : Option SpatialConfiguration)
    (observation : NativeRelationalType4Observation V e) :
    decodeVariant (policy := policy) e spatial? (.type4 observation) =
      .type4 (decodeType4 e spatial? observation) := rfl

@[simp] theorem decodeVariant_superimposed {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (spatial? : Option SpatialConfiguration)
    (base : NativeRelationalFullereneObservation V e policy)
    (numberingKind : FullereneNumberingKind) (handedness : FullereneHandedness) :
    decodeVariant e spatial? (.superimposed base numberingKind handedness) =
      .superimposed
        { handed :=
            { base := unrelabelObservation e policy spatial? base
              numberingKind := numberingKind
              handedness := handedness } } := rfl

/-! ### Native validity, indexed by the decoded data -/

/-- Native validity of one tagged observation: the decoded source observation is valid at the
supplied source.  The statement mentions the decoded data itself, not any stored copy of it. -/
def NativeRelationalVariantObservation.ValidFor {V : Type*} [DecidableEq V] {n : Nat}
    {e : V ≃ Fin n}
    (observation : NativeRelationalVariantObservation V e policy)
    (spatial? : Option SpatialConfiguration)
    (source : AuthoritativeChemicalInput) : Prop :=
  (decodeVariant e spatial? observation).ValidFor source

/-! ### Exact source-side recovery -/

/-- **Exact full-observation recovery for every tag.**  Every field participates: for `handed`
and `superimposed` the whole common observation (ordered input family, selected input, ordered
addends, chiral-addend set, assignment and substituent corpus) plus the numbering kind and
handedness; for `type4` the symmetry-derived input, assignment and corpus.  The only side
condition is the exact spatial-channel agreement already supplied by source validity. -/
theorem decodeVariant_encodeVariant {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (observation : SourceRelationalVariantObservation policy)
    (bounded : observation.BoundedIn n)
    (spatial? : Option SpatialConfiguration)
    (spatialExact : observation.spatial? = spatial?) :
    decodeVariant e spatial? (encodeVariant e observation bounded) = observation := by
  revert bounded spatialExact
  cases observation with
  | handed o =>
      intro bounded spatialExact
      subst spatialExact
      simp [encodeVariant_handed, decodeVariant_handed,
        SourceRelationalVariantObservation.spatial?,
        unrelabelObservation_relabelObservation]
  | type4 o =>
      intro bounded spatialExact
      subst spatialExact
      simp [encodeVariant_type4, decodeVariant_type4,
        SourceRelationalVariantObservation.spatial?, decodeType4_encodeType4]
  | superimposed o =>
      intro bounded spatialExact
      subst spatialExact
      simp [encodeVariant_superimposed, decodeVariant_superimposed,
        SourceRelationalVariantObservation.spatial?,
        unrelabelObservation_relabelObservation]

/-! ### Distinct tags are preserved -/

theorem handed_ne_type4 {V : Type*} [DecidableEq V] {n : Nat} {e : V ≃ Fin n}
    {policy : P93RelationalFullereneAuthorityPolicy}
    (base : NativeRelationalFullereneObservation V e policy)
    (numberingKind : FullereneNumberingKind) (handedness : FullereneHandedness)
    (observation : NativeRelationalType4Observation V e) :
    (NativeRelationalVariantObservation.handed base numberingKind handedness :
        NativeRelationalVariantObservation V e policy) ≠ .type4 observation := by
  intro equal
  cases equal

theorem handed_ne_superimposed {V : Type*} [DecidableEq V] {n : Nat} {e : V ≃ Fin n}
    {policy : P93RelationalFullereneAuthorityPolicy}
    (base : NativeRelationalFullereneObservation V e policy)
    (numberingKind : FullereneNumberingKind) (handedness : FullereneHandedness)
    (otherBase : NativeRelationalFullereneObservation V e policy)
    (otherNumberingKind : FullereneNumberingKind)
    (otherHandedness : FullereneHandedness) :
    (NativeRelationalVariantObservation.handed base numberingKind handedness :
        NativeRelationalVariantObservation V e policy) ≠
      .superimposed otherBase otherNumberingKind otherHandedness := by
  intro equal
  cases equal

theorem type4_ne_superimposed {V : Type*} [DecidableEq V] {n : Nat} {e : V ≃ Fin n}
    {policy : P93RelationalFullereneAuthorityPolicy}
    (observation : NativeRelationalType4Observation V e)
    (base : NativeRelationalFullereneObservation V e policy)
    (numberingKind : FullereneNumberingKind) (handedness : FullereneHandedness) :
    (NativeRelationalVariantObservation.type4 observation :
        NativeRelationalVariantObservation V e policy) ≠
      .superimposed base numberingKind handedness := by
  intro equal
  cases equal

/-! ## Bounds and spatial channel derived from source validity -/

/-- A valid source variant is bounded at the atom count of its binding. -/
theorem SourceRelationalVariantObservation.boundedIn_of_validFor
    [Fintype V] (binding : PhysicalFrameSourceBinding V)
    (observation : SourceRelationalVariantObservation policy)
    (valid : observation.ValidFor binding.source) :
    observation.BoundedIn (Fintype.card V) := by
  cases observation with
  | handed o =>
      change o.ValidFor policy binding.source at valid
      exact relationalObservationBoundedIn_of_validFor
        (relationalObservationAtomCount_eq binding o.base valid.baseValid)
        valid.baseValid
  | type4 o =>
      change o.ValidFor policy binding.source at valid
      show type4ObservationBoundedIn (Fintype.card V) o
      exact type4ObservationBoundedIn_of_validFor
        (type4ObservationAtomCount_eq binding o valid) valid
  | superimposed o =>
      change o.ValidFor policy binding.source at valid
      exact relationalObservationBoundedIn_of_validFor
        (relationalObservationAtomCount_eq binding o.handed.base
          valid.handedValid.baseValid)
        valid.handedValid.baseValid

/-- The stored spatial channel of a valid source variant is exactly the encoding of the
binding's shared spatial channel. -/
theorem SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
    [Fintype V] (binding : PhysicalFrameSourceBinding V)
    (observation : SourceRelationalVariantObservation policy)
    (valid : observation.ValidFor binding.source) :
    observation.spatial? =
      OrganicFiniteSource.encodeSpatial? binding.enumeration binding.shared.spatial? := by
  cases observation with
  | handed o =>
      change o.ValidFor policy binding.source at valid
      rw [binding.spatial_eq]
      exact valid.baseValid.structureAgreement.2.1.symm
  | type4 o =>
      change o.ValidFor policy binding.source at valid
      rw [binding.spatial_eq]
      exact valid.structureAgreement.2.1.symm
  | superimposed o =>
      change o.ValidFor policy binding.source at valid
      rw [binding.spatial_eq]
      exact valid.handedValid.baseValid.structureAgreement.2.1.symm

/-! ## Raw source, native satellite and exact recovery -/

/-- A raw variant source: one physical-frame binding and an ordered list of tagged source
observations, each certified valid at the bound source.  No boundedness data is stored; every
bound used by the codec is derived from `ValidFor` during adaptation. -/
structure RawRelationalVariantObservationSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93RelationalFullereneAuthorityPolicy) where
  binding : PhysicalFrameSourceBinding V
  observations : List (SourceRelationalVariantObservation policy)
  valid : ∀ observation ∈ observations, observation.ValidFor binding.source

/-- The native satellite.  It stores the shared finite source (graph and both optional geometry
channels) and an ordered list of native tagged observations.  It stores no original source
observation and no certified source.  The `valid` field is the source-side validity restated as
a proof about the decoded data at the encoded shared source. -/
structure NativeRelationalVariantObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (e : V ≃ Fin (Fintype.card V)) (policy : P93RelationalFullereneAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (NativeRelationalVariantObservation V e policy)
  valid : ∀ observation ∈ observations,
    observation.ValidFor
      (OrganicFiniteSource.encodeSpatial? e spatial?)
      (OrganicFiniteSource.encode
        { graph := graph, spatial? := spatial?, diagram? := diagram? } e)

namespace NativeRelationalVariantObservationSatellite

variable {V : Type*} [DecidableEq V] [Fintype V]
  {e : V ≃ Fin (Fintype.card V)}
  {policy : P93RelationalFullereneAuthorityPolicy}

/-- The shared finite source, with observations intentionally excluded. -/
def toFiniteSource (satellite : NativeRelationalVariantObservationSatellite V e policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

/-- The shared spatial channel encoded from the actual satellite source. -/
def sharedSpatial? (satellite : NativeRelationalVariantObservationSatellite V e policy) :
    Option SpatialConfiguration :=
  OrganicFiniteSource.encodeSpatial? e satellite.spatial?

/-- The authoritative source recovered from the satellite's shared finite source. -/
def source (satellite : NativeRelationalVariantObservationSatellite V e policy) :
    AuthoritativeChemicalInput :=
  satellite.toFiniteSource.encode e

/-- Satellite validity: every stored native observation decodes to a source observation valid at
the recovered satellite source. -/
def ValidFor (satellite : NativeRelationalVariantObservationSatellite V e policy) : Prop :=
  ∀ observation ∈ satellite.observations,
    observation.ValidFor satellite.sharedSpatial? satellite.source

/-- The stored native validity proof is exactly the satellite validity statement. -/
theorem validFor (satellite : NativeRelationalVariantObservationSatellite V e policy) :
    satellite.ValidFor := by
  intro observation member
  simpa only [ValidFor, sharedSpatial?, source, toFiniteSource] using
    satellite.valid observation member

end NativeRelationalVariantObservationSatellite

/-- Encode one tagged observation of a raw source.  This named function is used both for the
satellite payload list and for its validity proof, so no separate boundedness witness is
manufactured in the two places. -/
def encodeObservationOfRaw {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy)
    (observation : {observation // observation ∈ raw.observations}) :
    NativeRelationalVariantObservation V raw.binding.enumeration policy :=
  encodeVariant raw.binding.enumeration observation.1
    (SourceRelationalVariantObservation.boundedIn_of_validFor raw.binding observation.1
      (raw.valid observation.1 observation.2))

/-- Decoding one encoded raw observation recovers it exactly, at the encoded shared spatial
channel. -/
theorem decodeVariant_encodeObservationOfRaw {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy)
    (observation : {observation // observation ∈ raw.observations}) :
    decodeVariant raw.binding.enumeration
        (OrganicFiniteSource.encodeSpatial? raw.binding.enumeration
          raw.binding.shared.spatial?)
        (encodeObservationOfRaw raw observation) = observation.1 :=
  decodeVariant_encodeVariant raw.binding.enumeration observation.1
    (SourceRelationalVariantObservation.boundedIn_of_validFor raw.binding observation.1
      (raw.valid observation.1 observation.2))
    _
    (SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
      raw.binding observation.1 (raw.valid observation.1 observation.2))

/-- Adapt a raw variant source into the native satellite.  The shared finite source is retained
verbatim; every valid observation is encoded with its own tag, and the satellite validity proof
is stated about the decoded data. -/
def adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    NativeRelationalVariantObservationSatellite V raw.binding.enumeration policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map (encodeObservationOfRaw raw)
  valid := by
    intro observation member
    rw [List.mem_map] at member
    obtain ⟨sourceObservation, _sourceMember, rfl⟩ := member
    unfold NativeRelationalVariantObservation.ValidFor
    rw [decodeVariant_encodeObservationOfRaw]
    have sourceEq : OrganicFiniteSource.encode
        { graph := raw.binding.shared.graph
          spatial? := raw.binding.shared.spatial?
          diagram? := raw.binding.shared.diagram? } raw.binding.enumeration =
        raw.binding.source := raw.binding.encode_shared
    rw [sourceEq]
    exact raw.valid sourceObservation.1 sourceObservation.2

@[simp] theorem adapt_graph {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

@[simp] theorem adapt_observations {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    (adapt raw).observations = raw.observations.attach.map (encodeObservationOfRaw raw) := rfl

/-- The reconstructed shared spatial channel is tied to the actual source, not to arbitrary
payload metadata. -/
theorem sharedSpatial?_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    (adapt raw).sharedSpatial? = raw.binding.source.spatial? := by
  simp [NativeRelationalVariantObservationSatellite.sharedSpatial?, adapt_spatial?,
    raw.binding.spatial_eq]

/-- The recovered source of the adapted satellite is the binding's authored source. -/
@[simp] theorem source_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    (adapt raw).source = raw.binding.source := by
  simp only [NativeRelationalVariantObservationSatellite.source,
    NativeRelationalVariantObservationSatellite.toFiniteSource, adapt]
  exact raw.binding.encode_shared

/-- The recovered variant source record: the exact authoritative input together with the ordered
list of tagged source observations. -/
@[ext] structure RecoveredRelationalVariantObservationSource
    (policy : P93RelationalFullereneAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceRelationalVariantObservation policy)

/-- Decode a native satellite into the recovered source record.  The authoritative input is the
exact encode of the shared finite source; every observation is decoded with the explicit
enumeration and the satellite's shared spatial channel. -/
def suppliedSource {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    {e : V ≃ Fin (Fintype.card V)}
    (satellite : NativeRelationalVariantObservationSatellite V e policy) :
    RecoveredRelationalVariantObservationSource policy where
  source := satellite.source
  observations := satellite.observations.map (decodeVariant e satellite.sharedSpatial?)

/-- **Exact ordered observation-list recovery.**  Order and multiplicity are preserved, and every
tag is decoded through its own full-record inverse. -/
theorem decodedObservations_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    (suppliedSource (adapt raw)).observations = raw.observations := by
  obtain ⟨binding, observations, valid⟩ := raw
  simp only [suppliedSource]
  rw [sharedSpatial?_adapt, ← binding.spatial_eq]
  rw [adapt_observations, List.map_map]
  refine Eq.trans ?_ (List.attach_map_subtype_val observations)
  apply List.map_congr_left
  intro observation _
  obtain ⟨sourceObservation, member⟩ := observation
  exact decodeVariant_encodeVariant binding.enumeration sourceObservation
    (SourceRelationalVariantObservation.boundedIn_of_validFor binding sourceObservation
      (valid sourceObservation member))
    _
    (SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
      binding sourceObservation (valid sourceObservation member))

/-- **Exact full source recovery.**  Adapting a raw variant source and decoding it returns the
exact authoritative input and the exact ordered list of tagged source observations. -/
theorem suppliedSource_adapt {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    suppliedSource (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredRelationalVariantObservationSource.ext
  · simp only [suppliedSource]
    exact source_adapt raw
  · simp only [suppliedSource]
    exact decodedObservations_adapt raw

/-- Validity of every recovered observation at the recovered source and the same policy.  This is
the stored native validity proof, read through the exact source and list recovery.  Nothing is
re-judged at a different source and no policy predicate is assumed invariant under an atom
relabelling. -/
theorem suppliedSource_adapt_validFor {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (raw : RawRelationalVariantObservationSource V policy) :
    ∀ observation ∈ (suppliedSource (adapt raw)).observations,
      observation.ValidFor (suppliedSource (adapt raw)).source := by
  intro observation member
  simp only [suppliedSource_adapt raw] at member ⊢
  exact raw.valid observation member

/-! ## Arbitrary correlated set and ordered-list inverses at a fixed source

`S` is an arbitrary set (or list) of tagged source observations carrying, in correlation, their
validity at the fixed source and the fixed spatial channel.  Encoding and decoding the whole
tagged record is an image inverse on `S`.  The statement is about the full variant: no projection
such as the chiral-addend set alone is used. -/

/-- The set of tagged source observations valid at a fixed source and spatial channel. -/
abbrev ValidVariantAt {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V)
    (policy : P93RelationalFullereneAuthorityPolicy)
    (spatial? : Option SpatialConfiguration) : Type _ :=
  {observation : SourceRelationalVariantObservation policy //
    observation.ValidFor binding.source ∧ observation.spatial? = spatial?}

/-- Encode one valid tagged source observation. -/
def encodeValidVariant {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration)
    (observation : ValidVariantAt binding policy spatial?) :
    NativeRelationalVariantObservation V binding.enumeration policy :=
  encodeVariant binding.enumeration observation.1
    (SourceRelationalVariantObservation.boundedIn_of_validFor binding observation.1
      observation.2.1)

/-- Decoding an encoded valid tagged observation returns the exact full source record. -/
theorem decodeVariant_encodeValidVariant {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration)
    (observation : ValidVariantAt binding policy spatial?) :
    decodeVariant binding.enumeration spatial?
        (encodeValidVariant binding spatial? observation) = observation.1 :=
  decodeVariant_encodeVariant binding.enumeration observation.1
    (SourceRelationalVariantObservation.boundedIn_of_validFor binding observation.1
      observation.2.1)
    spatial? observation.2.2

/-- The native variant codec is injective on the valid correlated set at a fixed source and
spatial channel. -/
theorem encodeValidVariant_injective {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration) :
    Function.Injective (encodeValidVariant (V := V) binding (policy := policy) spatial?) := by
  intro first second equal
  have applied := congrArg (decodeVariant binding.enumeration spatial?) equal
  rw [decodeVariant_encodeValidVariant, decodeVariant_encodeValidVariant] at applied
  exact Subtype.ext applied

/-- **Arbitrary correlated set image inverse.**  For any set `S` of tagged observations valid at
the fixed source and spatial channel, decoding the encoded image returns exactly `S` as a set of
source observations.  The correlation between tag, numbering kind, handedness, input family,
addends, attachment ports, assignment and corpus is preserved because the whole tagged record is
inverted. -/
theorem set_image_decodeVariant_encodeValidVariant {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration)
    (observations : Set (ValidVariantAt (V := V) binding policy spatial?)) :
    (fun observation => decodeVariant binding.enumeration spatial?
        (encodeValidVariant binding spatial? observation)) '' observations =
      (fun observation : ValidVariantAt (V := V) binding policy spatial? =>
        observation.1) '' observations := by
  apply Set.image_congr
  intro observation _
  exact decodeVariant_encodeValidVariant binding spatial? observation

/-- **Ordered-list form of the same inverse.**  An arbitrary list of valid tagged observations is
recovered entry by entry, with order and multiplicity. -/
theorem list_map_decodeVariant_encodeValidVariant {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93RelationalFullereneAuthorityPolicy}
    (binding : PhysicalFrameSourceBinding V)
    (spatial? : Option SpatialConfiguration)
    (observations : List (ValidVariantAt (V := V) binding policy spatial?)) :
    observations.map (fun observation =>
        decodeVariant binding.enumeration spatial?
          (encodeValidVariant binding spatial? observation)) =
      observations.map (fun observation => observation.1) := by
  apply List.map_congr_left
  intro observation _
  exact decodeVariant_encodeValidVariant binding spatial? observation

/-! ## Ordered list codec without the subtype wrapper -/

/-- Encode an ordered list of bounded tagged source observations.  Order and multiplicity are
retained. -/
def encodeVariantList {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (observations : List (SourceRelationalVariantObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    List (NativeRelationalVariantObservation V e policy) :=
  observations.attach.map fun observation =>
    encodeVariant e observation.1 (bounded observation.1 observation.2)

/-- Decode an ordered list of native tagged observations at one fixed spatial channel. -/
def decodeVariantList {V : Type*} [DecidableEq V] {n : Nat} (e : V ≃ Fin n)
    (spatial? : Option SpatialConfiguration) :
    List (NativeRelationalVariantObservation V e policy) →
      List (SourceRelationalVariantObservation policy) :=
  List.map (decodeVariant e spatial?)

/-- **Exact ordered-list recovery.**  Every entry is recovered by the full tagged inverse; the
fixed spatial channel must be the one stored by every observation. -/
theorem decodeVariantList_encodeVariantList {V : Type*} [DecidableEq V] {n : Nat}
    (e : V ≃ Fin n) (observations : List (SourceRelationalVariantObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (spatial? : Option SpatialConfiguration)
    (spatialExact : ∀ observation ∈ observations, observation.spatial? = spatial?) :
    decodeVariantList e spatial? (encodeVariantList e observations bounded) = observations := by
  unfold decodeVariantList encodeVariantList
  rw [List.map_map]
  refine Eq.trans ?_ (List.attach_map_subtype_val observations)
  apply List.map_congr_left
  intro observation member
  exact decodeVariant_encodeVariant e observation.1
    (bounded observation.1 observation.2) spatial?
    (spatialExact observation.1 observation.2)

end OrganicStereoRelationalFullereneVariantIngress

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.type4ObservationBoundedIn
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.type4ObservationAtomCount_eq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.type4ObservationBoundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.NativeRelationalType4Observation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.decodeType4_encodeType4
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.NativeRelationalVariantObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.NativeRelationalVariantObservation.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.encodeVariant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.decodeVariant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.decodeVariant_encodeVariant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.handed_ne_type4
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.handed_ne_superimposed
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.type4_ne_superimposed
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation.boundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.SourceRelationalVariantObservation.spatial?_eq_encodeSpatial?_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.NativeRelationalVariantObservationSatellite
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.NativeRelationalVariantObservationSatellite.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.NativeRelationalVariantObservationSatellite.validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.sharedSpatial?_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.source_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.decodedObservations_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.suppliedSource_adapt_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.decodeVariant_encodeValidVariant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.encodeValidVariant_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.set_image_decodeVariant_encodeValidVariant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.list_map_decodeVariant_encodeValidVariant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoRelationalFullereneVariantIngress.decodeVariantList_encodeVariantList
