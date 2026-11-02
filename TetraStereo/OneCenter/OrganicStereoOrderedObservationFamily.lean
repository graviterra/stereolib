import TetraStereo.OneCenter.OrganicStereoRealConfiguration
import TetraStereo.OneCenter.CIPP94ConformationCompletePipeline
import TetraStereo.OneCenter.P94CoordinateTwistInOutPerception
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter
namespace OrganicStereoOrderedObservationFamily

open BlueBookP94
open BlueBookP94.CoordinateTorsion
open BlueBookP94.CoordinateTwistInOut

/-!
# Ordered conformer / observation families as a satellite channel

This module supplies the missing *general ordered conformer/observation-family* representation.  It
is a satellite channel parameterized by

* a certified source `source : CertifiedAuthoritativeChemicalInput`;
* an arbitrary finite atom index `V` (the only domain parameter of the family);
* a state type `State` used by the supplied P-94 conformer and twist records;
* a framework type `Framework` used by the supplied P-94 in/out records.

`OrderedObservationFamily source V State Framework` carries the supplied conformer family
(`scope`, `count`, and an ordered `Fin count → MolecularConformation V` family) and one optional
observation payload.  The payload is a bundle of independent optional channels, one for each
existing source-record family:

* `ConformerPairObservation`                     (from `P94ConformerEvidence`)
* `TorsionObservation`                           (from `P94TorsionEvidence`)
* `TwistObservation`                             (from `P94TwistEvidence`)
* `InOutObservationData`                         (from `P94InOutEvidence`)
* `CoordinateInOutData`                          (from `CoordinateInOutObservation` / `CoordinateInOutInput`)

Every atom reference in a payload is encoded over `V` through one explicit bijection
`SourceAtomIndex source ≃ V`; no atom number is copied beside an unrelated encoding.  The encoders
that consume a P-94 record take the record's own well-formedness predicate (`ValidFor`) against one
actual `RawMolecule` that is proved to convert to the certified source's `SemanticMolecule`
(`RawSourceTie`).  Consequently every decoded atom is in range of the source atom enumeration, and
every decoded conformation is a genuine `SourceConformation source`, i.e. exactly one real point per
source atom.

Absence and present-empty are kept distinct: `observation? = none` means no observation payload was
supplied; `observation? = some payload` means a payload was supplied even when all of its ordered
lists are empty (`ObservationPayload.empty`).  Inside the conformer family, `ConformerScope.empty`
(positively empty) and `ConformerScope.unknown` (no information supplied) are both retained and are
provably distinct.

The main results are exact inverses, not assumed ones:

* `EncodedConformationUnit.toUnit_ofUnit` and the per-record `toSource_ofSource` theorems decode an
  encoded payload back to the actual source record from which it was built;
* `toFiniteConformerCollection_ofFiniteConformerCollection` and
  `toCertifiedFiniteConformerCollection_ofCertifiedFiniteConformerCollection` recover the source
  conformer collection exactly, including its scope, count, order and multiplicity;
* `relabel_symm` proves that relabelling over an arbitrary `V ≃ W` and back is the identity, and
  `finDecode_finEncode` / `finEncode_finDecode` specialize this to the concrete source enumeration
  `SourceAtomIndex source = Fin source.input.molecule.atomCount`;
* `relabel_image_roundtrip` preserves an arbitrary joint set of families through the image of the
  relabelling.

The satellite is attachable without changing any existing domain record:
`attachObservation` overwrites only the observation channel and provably leaves scope, count and
the conformer family untouched.  No descriptor, physical population, trajectory, or claim of
organic-chemistry completeness is produced here.

## What the relabelling does and does not move

The encoding moves *only explicit atom references* over the common bijection
`e : SourceAtomIndex source ≃ V`.  The opaque carriers `State` and `Framework`, every relation and
predicate over them (`singleBondRotation`, `endpointConformationsDistinct`, `isBoatState`,
`isChairState`, `bridgeLongEnough`, `bicyclicSystem`, ...), and every exact geometric payload
(`SpatialConfiguration`, virtual-point `CartesianPoint3` coordinates and `interior`) are copied
verbatim.  In particular, a `SpatialConfiguration` keeps its original source-indexed position list:
it is never reindexed, normalized, lengthened or shortened, and no atom-count/position-length
equality is assumed.  Coordinate interpretation therefore requires the resolver context supplied
below.

The conformer channel is the existing concrete `FiniteConformerCollection` /
`CertifiedFiniteConformerCollection` over `SourceAtomIndex source`, whose conformers are actual
`MolecularConformation (SourceAtomIndex source)` objects with exactly one real point per source
atom; the `toFiniteConformerCollection` / `ofFiniteConformerCollection` pair maps those actual
conformations.  No claim is made that arbitrary internal atom references of an opaque `State` or
`Framework` have been transported, because no such atom reference is exposed by those carriers.

## Coordinate interpretation through the common enumeration

`EncodedCoordinateObservation.pointAt e observation atom` is the explicit resolver
`observation.spatial.positions[(e.symm atom).val]?`.  It is `Option`-valued so arbitrary source list
lengths stay admitted.  The module proves that it recovers the original source lookup after
`ofSource`, that it is invariant under relabelling with the composed enumeration
(`pointAt (e.trans r) (relabel r observation) (r atom) = pointAt e observation atom`), and that it
returns the exact source coordinate at the bridgehead and at the atom owner of the directed
participant.  `EncodedVirtualTorsionPoint.lookup` / `EncodedCoordinateObservation.virtualPointAt`
provide the corresponding encoded ledger lookup and are proved to agree exactly (including `none`
versus `some`) with the source `VirtualTorsionPointLedger.lookup` for both actual virtual
participant kinds (`lonePair` and `duplicateAtom`).
-/

/-! ## The actual source graph tie -/

/-- The exact bound carried by a primitive virtual-torsion participant.  The participant comes
first so that the bound is stated at its own carrier type. -/
def VirtualParticipantBounded : VirtualTorsionParticipant → ℕ → Prop
  | .lonePair center => fun atomCount => center < atomCount
  | .duplicateAtom original => fun atomCount => original < atomCount

/-- One actual parser molecule together with the proof that it converts to the certified source's
semantic molecule.  Every P-94 record adapted below is validated against this very molecule, and
the conversion equality fixes the atom enumeration exactly. -/
structure RawSourceTie (source : CertifiedAuthoritativeChemicalInput) where
  molecule : RawMolecule
  converted : molecule.toSemanticMolecule? = some source.input.molecule

namespace RawSourceTie

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The semantic source atom count is exactly the raw parser atom count. -/
theorem atomCountEq (tie : RawSourceTie source) :
    source.input.molecule.atomCount = tie.molecule.atomCount :=
  tie.molecule.toSemanticMolecule?_atomCount source.input.molecule tie.converted

/-- A raw atom bound transports to the source enumeration. -/
theorem atom_bound (tie : RawSourceTie source) {atom : ℕ}
    (bound : atom < tie.molecule.atomCount) :
    atom < source.input.molecule.atomCount := by
  rw [tie.atomCountEq]
  exact bound

/-- A bounded torsion participant transports to the source enumeration. -/
theorem participantBounded (tie : RawSourceTie source) {participant : TorsionParticipant ℕ}
    (bounded : P94ConformationUnit.ParticipantBounded participant tie.molecule.atomCount) :
    P94ConformationUnit.ParticipantBounded participant
      source.input.molecule.atomCount := by
  have countEq := tie.atomCountEq
  cases participant <;>
    simp [P94ConformationUnit.ParticipantBounded] at bounded ⊢
  all_goals omega

/-- A bounded virtual torsion participant transports to the source enumeration. -/
theorem virtualParticipantBounded (tie : RawSourceTie source)
    {participant : VirtualTorsionParticipant}
    (bounded : VirtualParticipantBounded participant tie.molecule.atomCount) :
    VirtualParticipantBounded participant source.input.molecule.atomCount := by
  have countEq := tie.atomCountEq
  cases participant <;> simp [VirtualParticipantBounded] at bounded ⊢
  all_goals omega

end RawSourceTie

/-! ## Atom index transport through one bijection -/

variable {source : CertifiedAuthoritativeChemicalInput}
variable {V W U State Framework : Type*}

/-- Encode one source atom number as an element of the independent index `V`.  The bound is the
source well-formedness fact; no out-of-range atom can be encoded. -/
def encodeIndex (e : SourceAtomIndex source ≃ V) (atom : ℕ)
    (bound : atom < source.input.molecule.atomCount) : V :=
  e ⟨atom, bound⟩

/-- Decode one independent index back to the source atom number. -/
def decodeIndex (e : SourceAtomIndex source ≃ V) (atom : V) : ℕ :=
  (e.symm atom).val

@[simp] theorem decodeIndex_encodeIndex (e : SourceAtomIndex source ≃ V) (atom : ℕ)
    (bound : atom < source.input.molecule.atomCount) :
    decodeIndex e (encodeIndex e atom bound) = atom := by
  simp [decodeIndex, encodeIndex]

/-- Every decoded index is an actual source atom index, not merely a natural number. -/
theorem decodeIndex_lt (e : SourceAtomIndex source ≃ V) (atom : V) :
    decodeIndex e atom < source.input.molecule.atomCount :=
  (e.symm atom).isLt

/-- Encode an ordered atom list.  Order, multiplicity and repetition are retained. -/
def encodeAtoms (e : SourceAtomIndex source ≃ V) (atoms : List ℕ)
    (bound : ∀ atom ∈ atoms, atom < source.input.molecule.atomCount) : List V :=
  atoms.attach.map fun item => e ⟨item.1, bound item.1 item.2⟩

/-- Decode an ordered atom list. -/
def decodeAtoms (e : SourceAtomIndex source ≃ V) (atoms : List V) : List ℕ :=
  atoms.map (decodeIndex e)

/-- Exact source ingress for ordered atom lists. -/
theorem decodeAtoms_encodeAtoms (e : SourceAtomIndex source ≃ V) (atoms : List ℕ)
    (bound : ∀ atom ∈ atoms, atom < source.input.molecule.atomCount) :
    decodeAtoms e (encodeAtoms e atoms bound) = atoms := by
  rw [decodeAtoms, encodeAtoms, List.map_map]
  change (atoms.attach.map fun item : { atom // atom ∈ atoms } =>
      decodeIndex e (e ⟨item.1, bound item.1 item.2⟩)) = atoms
  have pointwise : (fun item : { atom // atom ∈ atoms } =>
      decodeIndex e (e ⟨item.1, bound item.1 item.2⟩)) = (fun item => item.1) := by
    funext item
    exact decodeIndex_encodeIndex e item.1 (bound item.1 item.2)
  rw [pointwise]
  exact List.attach_map_subtype_val atoms

/-- Every decoded atom of an encoded list lies in the actual source enumeration. -/
theorem decodeAtoms_mem_bound (e : SourceAtomIndex source ≃ V) (atoms : List V) :
    ∀ atom ∈ decodeAtoms e atoms, atom < source.input.molecule.atomCount := by
  intro atom member
  rcases List.mem_map.mp member with ⟨encoded, _, rfl⟩
  exact decodeIndex_lt e encoded

/-! ## Torsion participants -/

/-- Transport one typed torsion participant along an index bijection. -/
def mapParticipant (e : V ≃ W) : TorsionParticipant V → TorsionParticipant W
  | .atom atom => .atom (e atom)
  | .lonePair center => .lonePair (e center)
  | .duplicateAtom original => .duplicateAtom (e original)

@[simp] theorem mapParticipant_symm_mapParticipant (e : V ≃ W)
    (participant : TorsionParticipant V) :
    mapParticipant e.symm (mapParticipant e participant) = participant := by
  cases participant <;> simp only [mapParticipant, Equiv.symm_apply_apply]

/-- The atom owner of one torsion participant: the ordinary atom, the lone-pair centre, or the
original atom of a multiple-bond duplicate.  Coordinates are indexed by atoms, so this is exactly
the atom index whose coordinate the participant kind is anchored to. -/
def participantOwner {Atom : Type*} : TorsionParticipant Atom → Atom
  | .atom atom => atom
  | .lonePair center => center
  | .duplicateAtom original => original

/-- Relabelling transports the participant owner by the same bijection. -/
@[simp] theorem participantOwner_mapParticipant (e : V ≃ W)
    (participant : TorsionParticipant V) :
    participantOwner (mapParticipant e participant) = e (participantOwner participant) := by
  cases participant <;> rfl

/-- A bounded source participant has a bounded owner for every participant kind. -/
theorem participantOwner_bound {participant : TorsionParticipant ℕ} {atomCount : ℕ}
    (bound : P94ConformationUnit.ParticipantBounded participant atomCount) :
    participantOwner participant < atomCount := by
  cases participant <;> exact bound

/-- Encode one bounded source participant. -/
def encodeParticipant (e : SourceAtomIndex source ≃ V) :
    (participant : TorsionParticipant ℕ) →
      P94ConformationUnit.ParticipantBounded participant
        source.input.molecule.atomCount → TorsionParticipant V
  | .atom atom, bound => .atom (encodeIndex e atom bound)
  | .lonePair center, bound => .lonePair (encodeIndex e center bound)
  | .duplicateAtom original, bound => .duplicateAtom (encodeIndex e original bound)

/-- Decode one participant back to the source atom numbers. -/
def decodeParticipant (e : SourceAtomIndex source ≃ V) :
    TorsionParticipant V → TorsionParticipant ℕ
  | .atom atom => .atom (decodeIndex e atom)
  | .lonePair center => .lonePair (decodeIndex e center)
  | .duplicateAtom original => .duplicateAtom (decodeIndex e original)

@[simp] theorem decodeParticipant_encodeParticipant (e : SourceAtomIndex source ≃ V)
    (participant : TorsionParticipant ℕ)
    (bound : P94ConformationUnit.ParticipantBounded participant
      source.input.molecule.atomCount) :
    decodeParticipant e (encodeParticipant e participant bound) = participant := by
  cases participant <;> simp [encodeParticipant, decodeParticipant]

/-- Encoding a bounded participant transports its owner to the encoded owner atom. -/
@[simp] theorem participantOwner_encodeParticipant
    (e : SourceAtomIndex source ≃ V) (participant : TorsionParticipant ℕ)
    (bound : P94ConformationUnit.ParticipantBounded participant
      source.input.molecule.atomCount) :
    participantOwner (encodeParticipant e participant bound) =
      e ⟨participantOwner participant, participantOwner_bound bound⟩ := by
  cases participant <;> rfl

/-- Decoding the owner of an encoded participant recovers the source participant owner exactly,
for all three participant kinds. -/
@[simp] theorem decodeIndex_participantOwner_encodeParticipant
    (e : SourceAtomIndex source ≃ V) (participant : TorsionParticipant ℕ)
    (bound : P94ConformationUnit.ParticipantBounded participant
      source.input.molecule.atomCount) :
    decodeIndex e (participantOwner (encodeParticipant e participant bound)) =
      participantOwner participant := by
  cases participant <;> simp [encodeParticipant, participantOwner, decodeIndex, encodeIndex]

/-! ## Virtual torsion participants and points -/

/-- The two virtual-torsion participant constructors over an independent atom index.  The shape
mirrors the primitive `VirtualTorsionParticipant` exactly; only the atom label moves. -/
inductive EncodedVirtualTorsionParticipant (V : Type*) where
  | lonePair (center : V)
  | duplicateAtom (original : V)
  deriving DecidableEq, Repr

namespace EncodedVirtualTorsionParticipant

/-- Relabel an encoded virtual participant. -/
def relabel (e : V ≃ W) : EncodedVirtualTorsionParticipant V →
    EncodedVirtualTorsionParticipant W
  | .lonePair center => .lonePair (e center)
  | .duplicateAtom original => .duplicateAtom (e original)

@[simp] theorem relabel_symm (e : V ≃ W)
    (participant : EncodedVirtualTorsionParticipant V) :
    relabel e.symm (relabel e participant) = participant := by
  cases participant <;> simp [relabel]

/-- Relabelling virtual participants is injective. -/
theorem relabel_injective (e : V ≃ W) :
    Function.Injective (relabel e) := by
  intro first second equal
  have := congrArg (relabel e.symm) equal
  simpa using this

end EncodedVirtualTorsionParticipant

/-- Encode one bounded primitive virtual participant. -/
def encodeVirtualParticipant (e : SourceAtomIndex source ≃ V) :
    (participant : VirtualTorsionParticipant) →
      VirtualParticipantBounded participant source.input.molecule.atomCount →
        EncodedVirtualTorsionParticipant V
  | .lonePair center, bound => .lonePair (encodeIndex e center bound)
  | .duplicateAtom original, bound => .duplicateAtom (encodeIndex e original bound)

/-- Decode one encoded virtual participant. -/
def decodeVirtualParticipant (e : SourceAtomIndex source ≃ V) :
    EncodedVirtualTorsionParticipant V → VirtualTorsionParticipant
  | .lonePair center => .lonePair (decodeIndex e center)
  | .duplicateAtom original => .duplicateAtom (decodeIndex e original)

@[simp] theorem decodeVirtualParticipant_encodeVirtualParticipant
    (e : SourceAtomIndex source ≃ V) (participant : VirtualTorsionParticipant)
    (bound : VirtualParticipantBounded participant source.input.molecule.atomCount) :
    decodeVirtualParticipant e (encodeVirtualParticipant e participant bound) = participant := by
  cases participant <;> simp [encodeVirtualParticipant, decodeVirtualParticipant]

/-- One encoded virtual torsion point: the exact rational point is retained and only the atom
label is transported. -/
structure EncodedVirtualTorsionPoint (V : Type*) where
  participant : EncodedVirtualTorsionParticipant V
  point : CartesianPoint3

namespace EncodedVirtualTorsionPoint

def relabel (e : V ≃ W) (point : EncodedVirtualTorsionPoint V) :
    EncodedVirtualTorsionPoint W where
  participant := point.participant.relabel e
  point := point.point

@[simp] theorem relabel_symm (e : V ≃ W) (point : EncodedVirtualTorsionPoint V) :
    relabel e.symm (relabel e point) = point := by
  cases point with
  | mk participant point =>
      simp [relabel]

/-- Look up the exact retained coordinate of one encoded participant in an encoded virtual-point
ledger.  This is the encoded mirror of `VirtualTorsionPointLedger.lookup`: it scans in the retained
order and returns the first entry naming the participant, or `none` when no entry does.  No point
is fabricated and no ledger length is assumed. -/
def lookup [DecidableEq V] (points : List (EncodedVirtualTorsionPoint V))
    (participant : EncodedVirtualTorsionParticipant V) : Option CartesianPoint3 :=
  match points with
  | [] => none
  | entry :: rest =>
      if entry.participant = participant then some entry.point
      else lookup rest participant

/-- Lookup commutes with relabelling: the exact coordinate found for a relabelled participant in a
relabelled ledger is exactly the coordinate found for the original participant. -/
@[simp] theorem lookup_relabel [DecidableEq V] [DecidableEq W] (e : V ≃ W)
    (points : List (EncodedVirtualTorsionPoint V))
    (participant : EncodedVirtualTorsionParticipant V) :
    lookup (points.map (relabel e))
        (EncodedVirtualTorsionParticipant.relabel e participant) =
      lookup points participant := by
  induction points with
  | nil => rfl
  | cons head tail tailIH =>
      simp only [List.map_cons, lookup]
      by_cases headMatch : head.participant = participant
      · subst participant
        simp [relabel]
      · have encodedNe : (relabel e head).participant ≠
            EncodedVirtualTorsionParticipant.relabel e participant := by
          intro equal
          exact headMatch (EncodedVirtualTorsionParticipant.relabel_injective e equal)
        rw [if_neg encodedNe, if_neg headMatch, tailIH]

end EncodedVirtualTorsionPoint

/-- Encode one bounded primitive virtual point. -/
def encodeVirtualPoint (e : SourceAtomIndex source ≃ V) (point : VirtualTorsionPoint)
    (bound : VirtualParticipantBounded point.participant
      source.input.molecule.atomCount) : EncodedVirtualTorsionPoint V where
  participant := encodeVirtualParticipant e point.participant bound
  point := point.point

/-- Decode one encoded virtual point. -/
def decodeVirtualPoint (e : SourceAtomIndex source ≃ V)
    (point : EncodedVirtualTorsionPoint V) : VirtualTorsionPoint where
  participant := decodeVirtualParticipant e point.participant
  point := point.point

@[simp] theorem decodeVirtualPoint_encodeVirtualPoint (e : SourceAtomIndex source ≃ V)
    (point : VirtualTorsionPoint)
    (bound : VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    decodeVirtualPoint e (encodeVirtualPoint e point bound) = point := by
  cases point with
  | mk participant point =>
      cases participant <;> simp [encodeVirtualPoint, decodeVirtualPoint]

/-- Encode an ordered virtual-point ledger; order and multiplicity are retained. -/
def encodeVirtualPoints (e : SourceAtomIndex source ≃ V) (points : List VirtualTorsionPoint)
    (bound : ∀ point ∈ points, VirtualParticipantBounded point.participant
      source.input.molecule.atomCount) : List (EncodedVirtualTorsionPoint V) :=
  points.attach.map fun item => encodeVirtualPoint e item.1 (bound item.1 item.2)

/-- Decode an ordered virtual-point ledger. -/
def decodeVirtualPoints (e : SourceAtomIndex source ≃ V)
    (points : List (EncodedVirtualTorsionPoint V)) : List VirtualTorsionPoint :=
  points.map (decodeVirtualPoint e)

@[simp] theorem decodeVirtualPoints_encodeVirtualPoints
    (e : SourceAtomIndex source ≃ V) (points : List VirtualTorsionPoint)
    (bound : ∀ point ∈ points, VirtualParticipantBounded point.participant
      source.input.molecule.atomCount) :
    decodeVirtualPoints e (encodeVirtualPoints e points bound) = points := by
  rw [decodeVirtualPoints, encodeVirtualPoints, List.map_map]
  change (points.attach.map fun item : { point // point ∈ points } =>
      decodeVirtualPoint e (encodeVirtualPoint e item.1 (bound item.1 item.2))) = points
  have pointwise : (fun item : { point // point ∈ points } =>
      decodeVirtualPoint e (encodeVirtualPoint e item.1 (bound item.1 item.2))) =
      (fun item => item.1) := by
    funext item
    exact decodeVirtualPoint_encodeVirtualPoint e item.1 (bound item.1 item.2)
  rw [pointwise]
  exact List.attach_map_subtype_val points

/-- The bound proof carried by an encoded virtual participant is propositionally irrelevant. -/
@[simp] theorem encodeVirtualParticipant_bound_irrel
    (e : SourceAtomIndex source ≃ V) (participant : VirtualTorsionParticipant)
    (firstBound secondBound : VirtualParticipantBounded participant
      source.input.molecule.atomCount) :
    encodeVirtualParticipant e participant firstBound =
      encodeVirtualParticipant e participant secondBound := by
  cases participant with
  | lonePair center =>
      have mkEqual : (⟨center, firstBound⟩ : SourceAtomIndex source) =
          ⟨center, secondBound⟩ := by
        apply Fin.ext
        rfl
      exact congrArg EncodedVirtualTorsionParticipant.lonePair (congrArg e mkEqual)
  | duplicateAtom original =>
      have mkEqual : (⟨original, firstBound⟩ : SourceAtomIndex source) =
          ⟨original, secondBound⟩ := by
        apply Fin.ext
        rfl
      exact congrArg EncodedVirtualTorsionParticipant.duplicateAtom (congrArg e mkEqual)

/-- Encoding is compatible with an equality of primitive virtual participants. -/
theorem encodeVirtualParticipant_congr
    (e : SourceAtomIndex source ≃ V)
    {first second : VirtualTorsionParticipant} (equal : first = second)
    (firstBound : VirtualParticipantBounded first source.input.molecule.atomCount)
    (secondBound : VirtualParticipantBounded second source.input.molecule.atomCount) :
    encodeVirtualParticipant e first firstBound =
      encodeVirtualParticipant e second secondBound := by
  subst second
  exact encodeVirtualParticipant_bound_irrel e first firstBound secondBound

/-- Encoding a primitive virtual participant is injective. -/
theorem encodeVirtualParticipant_injective
    (e : SourceAtomIndex source ≃ V)
    {first second : VirtualTorsionParticipant}
    (firstBound : VirtualParticipantBounded first source.input.molecule.atomCount)
    (secondBound : VirtualParticipantBounded second source.input.molecule.atomCount)
    (equal : encodeVirtualParticipant e first firstBound =
      encodeVirtualParticipant e second secondBound) :
    first = second := by
  cases first with
  | lonePair firstCenter =>
      cases second with
      | lonePair secondCenter =>
          have encodedEqual : encodeIndex e firstCenter firstBound =
              encodeIndex e secondCenter secondBound := by
            injection equal with h
          have encodedEqual' : e (⟨firstCenter, firstBound⟩ : SourceAtomIndex source) =
              e ⟨secondCenter, secondBound⟩ := encodedEqual
          have centerEqual : firstCenter = secondCenter :=
            congrArg Fin.val (e.injective encodedEqual')
          rw [centerEqual]
      | duplicateAtom secondOriginal =>
          exact absurd equal (by simp [encodeVirtualParticipant])
  | duplicateAtom firstOriginal =>
      cases second with
      | lonePair secondCenter =>
          exact absurd equal (by simp [encodeVirtualParticipant])
      | duplicateAtom secondOriginal =>
          have encodedEqual : encodeIndex e firstOriginal firstBound =
              encodeIndex e secondOriginal secondBound := by
            injection equal with h
          have encodedEqual' : e (⟨firstOriginal, firstBound⟩ : SourceAtomIndex source) =
              e ⟨secondOriginal, secondBound⟩ := encodedEqual
          have originalEqual : firstOriginal = secondOriginal :=
            congrArg Fin.val (e.injective encodedEqual')
          rw [originalEqual]

/-- Encoded virtual-point lookup at an encoded participant agrees exactly with the source ledger
lookup at the corresponding primitive participant, for both actual virtual participant kinds.
The retained list order, multiplicity and exact coordinates are those of the source ledger; the
result is an `Option`, so a missing participant stays `none` on both sides. -/
theorem lookup_encodeVirtualPoints [DecidableEq V]
    (e : SourceAtomIndex source ≃ V) (points : List VirtualTorsionPoint)
    (bound : ∀ point ∈ points, VirtualParticipantBounded point.participant
      source.input.molecule.atomCount)
    (participant : VirtualTorsionParticipant)
    (participantBound : VirtualParticipantBounded participant
      source.input.molecule.atomCount) :
    EncodedVirtualTorsionPoint.lookup (encodeVirtualPoints e points bound)
        (encodeVirtualParticipant e participant participantBound) =
      VirtualTorsionPointLedger.lookup points participant := by
  revert bound
  induction points with
  | nil =>
      intro bound
      rfl
  | cons head tail tailIH =>
      intro bound
      rw [show encodeVirtualPoints e (head :: tail) bound =
          encodeVirtualPoint e head (bound head List.mem_cons_self) ::
            encodeVirtualPoints e tail
              (fun point member => bound point (List.mem_cons_of_mem head member)) by
        simp [encodeVirtualPoints, List.attach_cons]]
      simp only [encodeVirtualPoint, EncodedVirtualTorsionPoint.lookup,
        VirtualTorsionPointLedger.lookup]
      by_cases headMatch : head.participant = participant
      · simp [headMatch]
      · have encodedNe : encodeVirtualParticipant e head.participant
            (bound head List.mem_cons_self) ≠
            encodeVirtualParticipant e participant participantBound := by
          intro equal
          exact headMatch (encodeVirtualParticipant_injective e _ _ equal)
        simp [headMatch, encodedNe,
          tailIH (fun point member => bound point (List.mem_cons_of_mem head member))]

/-- The boundedness of the selected torsion participants follows from the record's own
`ValidFor` predicate.  Only the `torsionAxis` kind carries participants, and that branch of
`ValidFor` contains their bounds. -/
theorem participantsBounded_of_validFor {molecule : RawMolecule} {unit : P94ConformationUnit}
    (valid : unit.ValidFor molecule) :
    ∀ pair, unit.torsionParticipants? = some pair →
      P94ConformationUnit.ParticipantBounded pair.1 molecule.atomCount ∧
        P94ConformationUnit.ParticipantBounded pair.2 molecule.atomCount := by
  intro pair observed
  cases unit with
  | mk kind atoms participants? =>
      cases kind <;> simp only [P94ConformationUnit.ValidFor] at valid observed
      · simp_all
      · rcases valid with
          ⟨_, _, front, rear, _, _, participantsEq, _, _, _, frontBound, rearBound, _, _⟩
        rw [participantsEq] at observed
        simp only [Option.some.injEq] at observed
        rcases observed with ⟨rfl, rfl⟩
        exact ⟨frontBound, rearBound⟩
      all_goals simp_all

/-! ## The encoded P-94 conformation unit -/

/-- The exact data fields of `P94ConformationUnit`, with its atom references transported to `V`.
The kind and the optional selected torsion participants are retained. -/
structure EncodedConformationUnit (V : Type*) where
  kind : P94ConformationUnitKind
  atoms : List V
  torsionParticipants? : Option (TorsionParticipant V × TorsionParticipant V) := none

namespace EncodedConformationUnit

def relabel (e : V ≃ W) (unit : EncodedConformationUnit V) : EncodedConformationUnit W where
  kind := unit.kind
  atoms := unit.atoms.map e
  torsionParticipants? := unit.torsionParticipants?.map fun pair =>
    (mapParticipant e pair.1, mapParticipant e pair.2)

@[simp] theorem relabel_symm (e : V ≃ W) (unit : EncodedConformationUnit V) :
    relabel e.symm (relabel e unit) = unit := by
  cases unit with
  | mk kind atoms participants? =>
      cases participants? with
      | none => simp [relabel]
      | some pair =>
          rcases pair with ⟨front, rear⟩
          simp [relabel]

/-- Encode an actual `P94ConformationUnit` that is well formed for the tied raw molecule. -/
def ofUnit (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (unit : P94ConformationUnit) (valid : unit.ValidFor tie.molecule) :
    EncodedConformationUnit V where
  kind := unit.kind
  atoms := encodeAtoms e unit.atoms (fun atom member => by
    rw [tie.atomCountEq]
    exact valid.2.1 atom member)
  torsionParticipants? :=
    match h : unit.torsionParticipants? with
    | none => none
    | some pair =>
        some (encodeParticipant e pair.1 (tie.participantBounded
                (participantsBounded_of_validFor valid pair h).1),
              encodeParticipant e pair.2 (tie.participantBounded
                (participantsBounded_of_validFor valid pair h).2))

/-- Decode a conformation unit back to the source atom numbers. -/
def toUnit (e : SourceAtomIndex source ≃ V) (unit : EncodedConformationUnit V) :
    P94ConformationUnit where
  kind := unit.kind
  atoms := decodeAtoms e unit.atoms
  torsionParticipants? := unit.torsionParticipants?.map fun pair =>
    (decodeParticipant e pair.1, decodeParticipant e pair.2)

/-- Exactly reconstruct the source conformation unit from its encoded fields. -/
theorem toUnit_ofUnit (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (unit : P94ConformationUnit) (valid : unit.ValidFor tie.molecule) :
    toUnit e (ofUnit e tie unit valid) = unit := by
  cases unit with
  | mk kind atoms participants? =>
      dsimp only [toUnit, ofUnit]
      rw [decodeAtoms_encodeAtoms e atoms (fun atom member => by
        rw [tie.atomCountEq]
        exact valid.2.1 atom member)]
      cases participants? with
      | none => rfl
      | some pair =>
          rcases pair with ⟨front, rear⟩
          simp [decodeParticipant_encodeParticipant]

/-- Every atom of a decoded unit lies in the actual source enumeration. -/
theorem toUnit_atoms_bounded (e : SourceAtomIndex source ≃ V)
    (unit : EncodedConformationUnit V) :
    ∀ atom ∈ (toUnit e unit).atoms, atom < source.input.molecule.atomCount := by
  intro atom member
  exact decodeAtoms_mem_bound e unit.atoms atom member

end EncodedConformationUnit

/-! ## Encoded torsion selection candidates -/

/-- A source priority candidate with its participant transported to `V`; the ranking data is
retained verbatim. -/
structure EncodedTorsionSelectionCandidate (V : Type*) where
  participant : TorsionParticipant V
  ranking : TorsionCandidate

namespace EncodedTorsionSelectionCandidate

def relabel (e : V ≃ W) (candidate : EncodedTorsionSelectionCandidate V) :
    EncodedTorsionSelectionCandidate W where
  participant := mapParticipant e candidate.participant
  ranking := candidate.ranking

@[simp] theorem relabel_symm (e : V ≃ W)
    (candidate : EncodedTorsionSelectionCandidate V) :
    relabel e.symm (relabel e candidate) = candidate := by
  cases candidate with
  | mk participant ranking => simp [relabel]

/-- Encode a bounded source candidate. -/
def ofSource (e : SourceAtomIndex source ≃ V)
    (candidate : P94TorsionSelectionCandidate)
    (bound : P94ConformationUnit.ParticipantBounded candidate.participant
      source.input.molecule.atomCount) : EncodedTorsionSelectionCandidate V where
  participant := encodeParticipant e candidate.participant bound
  ranking := candidate.ranking

/-- Decode a candidate to the source record. -/
def toSource (e : SourceAtomIndex source ≃ V)
    (candidate : EncodedTorsionSelectionCandidate V) : P94TorsionSelectionCandidate where
  participant := decodeParticipant e candidate.participant
  ranking := candidate.ranking

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (candidate : P94TorsionSelectionCandidate)
    (bound : P94ConformationUnit.ParticipantBounded candidate.participant
      source.input.molecule.atomCount) :
    toSource e (ofSource e candidate bound) = candidate := by
  cases candidate with
  | mk participant ranking =>
      simp [toSource, ofSource, decodeParticipant_encodeParticipant]

end EncodedTorsionSelectionCandidate

/-- Encode an ordered candidate list.  Alternatives, rankings and repetition are retained. -/
def encodeCandidates (e : SourceAtomIndex source ≃ V)
    (candidates : List P94TorsionSelectionCandidate)
    (bound : ∀ candidate ∈ candidates,
      P94ConformationUnit.ParticipantBounded candidate.participant
        source.input.molecule.atomCount) :
    List (EncodedTorsionSelectionCandidate V) :=
  candidates.attach.map fun item => EncodedTorsionSelectionCandidate.ofSource e item.1
    (bound item.1 item.2)

/-- Decode an ordered candidate list. -/
def decodeCandidates (e : SourceAtomIndex source ≃ V)
    (candidates : List (EncodedTorsionSelectionCandidate V)) :
    List P94TorsionSelectionCandidate :=
  candidates.map (EncodedTorsionSelectionCandidate.toSource e)

@[simp] theorem decodeCandidates_encodeCandidates (e : SourceAtomIndex source ≃ V)
    (candidates : List P94TorsionSelectionCandidate)
    (bound : ∀ candidate ∈ candidates,
      P94ConformationUnit.ParticipantBounded candidate.participant
        source.input.molecule.atomCount) :
    decodeCandidates e (encodeCandidates e candidates bound) = candidates := by
  rw [decodeCandidates, encodeCandidates, List.map_map]
  change (candidates.attach.map fun item : { candidate // candidate ∈ candidates } =>
      EncodedTorsionSelectionCandidate.toSource e
        (EncodedTorsionSelectionCandidate.ofSource e item.1 (bound item.1 item.2))) = candidates
  have pointwise : (fun item : { candidate // candidate ∈ candidates } =>
      EncodedTorsionSelectionCandidate.toSource e
        (EncodedTorsionSelectionCandidate.ofSource e item.1 (bound item.1 item.2))) =
      (fun item => item.1) := by
    funext item
    exact EncodedTorsionSelectionCandidate.toSource_ofSource e item.1 (bound item.1 item.2)
  rw [pointwise]
  exact List.attach_map_subtype_val candidates

/-! ## Encoded selected torsion frame -/

/-- One selected torsion frame over the independent atom index. -/
structure EncodedSelectedTorsionFrame (V : Type*) where
  front : TorsionParticipant V
  rear : TorsionParticipant V
  angle : TorsionAngle

namespace EncodedSelectedTorsionFrame

def relabel (e : V ≃ W) (frame : EncodedSelectedTorsionFrame V) :
    EncodedSelectedTorsionFrame W where
  front := mapParticipant e frame.front
  rear := mapParticipant e frame.rear
  angle := frame.angle

@[simp] theorem relabel_symm (e : V ≃ W) (frame : EncodedSelectedTorsionFrame V) :
    relabel e.symm (relabel e frame) = frame := by
  cases frame with
  | mk front rear angle => simp [relabel]

/-- Encode one actual `SelectedTorsionFrame`. -/
def ofSource (e : SourceAtomIndex source ≃ V) (frame : SelectedTorsionFrame ℕ)
    (frontBound : P94ConformationUnit.ParticipantBounded frame.front
      source.input.molecule.atomCount)
    (rearBound : P94ConformationUnit.ParticipantBounded frame.rear
      source.input.molecule.atomCount) : EncodedSelectedTorsionFrame V where
  front := encodeParticipant e frame.front frontBound
  rear := encodeParticipant e frame.rear rearBound
  angle := frame.angle

/-- Decode a selected torsion frame. -/
def toSource (e : SourceAtomIndex source ≃ V) (frame : EncodedSelectedTorsionFrame V) :
    SelectedTorsionFrame ℕ where
  front := decodeParticipant e frame.front
  rear := decodeParticipant e frame.rear
  angle := frame.angle

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (frame : SelectedTorsionFrame ℕ)
    (frontBound : P94ConformationUnit.ParticipantBounded frame.front
      source.input.molecule.atomCount)
    (rearBound : P94ConformationUnit.ParticipantBounded frame.rear
      source.input.molecule.atomCount) :
    toSource e (ofSource e frame frontBound rearBound) = frame := by
  cases frame with
  | mk front rear angle =>
      simp [toSource, ofSource, decodeParticipant_encodeParticipant]

end EncodedSelectedTorsionFrame

/-! ## Per-record-family observation channels -/

/-- A supplied P-94 conformer pair: the ordered first/second states and their independent
single-bond rotation relation, plus the unit they refer to. -/
structure ConformerPairObservation (V : Type*) (State : Type*) where
  unit : EncodedConformationUnit V
  singleBondRotation : State → State → Prop
  first : State
  second : State

namespace ConformerPairObservation

def relabel (e : V ≃ W) (record : ConformerPairObservation V State) :
    ConformerPairObservation W State where
  unit := record.unit.relabel e
  singleBondRotation := record.singleBondRotation
  first := record.first
  second := record.second

@[simp] theorem relabel_symm (e : V ≃ W) (record : ConformerPairObservation V State) :
    relabel e.symm (relabel e record) = record := by
  cases record with
  | mk unit rotation first second => simp [relabel]

/-- Adapt an actual `P94ConformerEvidence` record. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94ConformerEvidence State) (valid : record.unit.ValidFor tie.molecule) :
    ConformerPairObservation V State where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  singleBondRotation := record.singleBondRotation
  first := record.first
  second := record.second

/-- Decode the conformer-pair channel back to the source record. -/
def toSource (e : SourceAtomIndex source ≃ V) (record : ConformerPairObservation V State) :
    P94ConformerEvidence State where
  unit := record.unit.toUnit e
  singleBondRotation := record.singleBondRotation
  first := record.first
  second := record.second

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94ConformerEvidence State)
    (valid : record.unit.ValidFor tie.molecule) :
    toSource e (ofSource e tie record valid) = record := by
  cases record with
  | mk unit rotation first second =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit]

end ConformerPairObservation

/-- A supplied P-94 torsion observation: the selected frame, the complete ordered alternative
lists on both axis ends, the selected candidate at each end, and the rotation sense. -/
structure TorsionObservation (V : Type*) where
  unit : EncodedConformationUnit V
  frame : EncodedSelectedTorsionFrame V
  frontCandidates : List (EncodedTorsionSelectionCandidate V)
  rearCandidates : List (EncodedTorsionSelectionCandidate V)
  selectedFront : EncodedTorsionSelectionCandidate V
  selectedRear : EncodedTorsionSelectionCandidate V
  rotationSense : RotationSense

namespace TorsionObservation

def relabel (e : V ≃ W) (record : TorsionObservation V) : TorsionObservation W where
  unit := record.unit.relabel e
  frame := record.frame.relabel e
  frontCandidates := record.frontCandidates.map
    (EncodedTorsionSelectionCandidate.relabel e)
  rearCandidates := record.rearCandidates.map
    (EncodedTorsionSelectionCandidate.relabel e)
  selectedFront := record.selectedFront.relabel e
  selectedRear := record.selectedRear.relabel e
  rotationSense := record.rotationSense

@[simp] theorem relabel_symm (e : V ≃ W) (record : TorsionObservation V) :
    relabel e.symm (relabel e record) = record := by
  cases record with
  | mk unit frame frontCandidates rearCandidates selectedFront selectedRear rotationSense =>
      simp [relabel, List.map_map, Function.comp_def]

/-- Adapt an actual `P94TorsionEvidence` record.  The frame bounds and the complete candidate
bounds are exactly the record's own well-formedness conditions. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94TorsionEvidence) (valid : record.unit.ValidFor tie.molecule)
    (frameFrontBound : P94ConformationUnit.ParticipantBounded record.frame.front
      source.input.molecule.atomCount)
    (frameRearBound : P94ConformationUnit.ParticipantBounded record.frame.rear
      source.input.molecule.atomCount)
    (candidateBounds : record.CandidateParticipantsBounded
      source.input.molecule.atomCount) : TorsionObservation V where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  frame := EncodedSelectedTorsionFrame.ofSource e record.frame frameFrontBound frameRearBound
  frontCandidates := encodeCandidates e record.frontCandidates (fun candidate member =>
    candidateBounds.2.2 candidate (List.mem_append_left _ member))
  rearCandidates := encodeCandidates e record.rearCandidates (fun candidate member =>
    candidateBounds.2.2 candidate (List.mem_append_right _ member))
  selectedFront := EncodedTorsionSelectionCandidate.ofSource e record.selectedFront
    candidateBounds.1
  selectedRear := EncodedTorsionSelectionCandidate.ofSource e record.selectedRear
    candidateBounds.2.1
  rotationSense := record.rotationSense

/-- Decode the torsion channel back to the source record. -/
def toSource (e : SourceAtomIndex source ≃ V) (record : TorsionObservation V) :
    P94TorsionEvidence where
  unit := record.unit.toUnit e
  frame := record.frame.toSource e
  frontCandidates := decodeCandidates e record.frontCandidates
  rearCandidates := decodeCandidates e record.rearCandidates
  selectedFront := EncodedTorsionSelectionCandidate.toSource e record.selectedFront
  selectedRear := EncodedTorsionSelectionCandidate.toSource e record.selectedRear
  rotationSense := record.rotationSense

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94TorsionEvidence)
    (valid : record.unit.ValidFor tie.molecule)
    (frameFrontBound : P94ConformationUnit.ParticipantBounded record.frame.front
      source.input.molecule.atomCount)
    (frameRearBound : P94ConformationUnit.ParticipantBounded record.frame.rear
      source.input.molecule.atomCount)
    (candidateBounds : record.CandidateParticipantsBounded
      source.input.molecule.atomCount) :
    toSource e (ofSource e tie record valid frameFrontBound frameRearBound candidateBounds) =
      record := by
  cases record with
  | mk unit frame frontCandidates rearCandidates selectedFront selectedRear rotationSense =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit,
        EncodedSelectedTorsionFrame.toSource_ofSource,
        EncodedTorsionSelectionCandidate.toSource_ofSource,
        decodeCandidates_encodeCandidates]

end TorsionObservation

/-- A supplied P-94 twist observation: the candidate reference and the ordered first and second
legs, together with the record's independent state predicates. -/
structure TwistObservation (V : Type*) (State : Type*) where
  unit : EncodedConformationUnit V
  singleBondRotation : State → State → Prop
  endpointConformationsDistinct : State → State → Prop
  isBoatState : State → Prop
  isChairState : State → Prop
  candidate : State
  firstLeg : List State
  secondLeg : List State

namespace TwistObservation

def relabel (e : V ≃ W) (record : TwistObservation V State) :
    TwistObservation W State where
  unit := record.unit.relabel e
  singleBondRotation := record.singleBondRotation
  endpointConformationsDistinct := record.endpointConformationsDistinct
  isBoatState := record.isBoatState
  isChairState := record.isChairState
  candidate := record.candidate
  firstLeg := record.firstLeg
  secondLeg := record.secondLeg

@[simp] theorem relabel_symm (e : V ≃ W) (record : TwistObservation V State) :
    relabel e.symm (relabel e record) = record := by
  cases record with
  | mk unit rotation distinct boat chair candidate firstLeg secondLeg =>
      simp [relabel]

/-- Adapt an actual `P94TwistEvidence` record. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94TwistEvidence State) (valid : record.unit.ValidFor tie.molecule) :
    TwistObservation V State where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  singleBondRotation := record.singleBondRotation
  endpointConformationsDistinct := record.endpointConformationsDistinct
  isBoatState := record.isBoatState
  isChairState := record.isChairState
  candidate := record.candidate
  firstLeg := record.firstLeg
  secondLeg := record.secondLeg

/-- Decode the twist channel back to the source record. -/
def toSource (e : SourceAtomIndex source ≃ V) (record : TwistObservation V State) :
    P94TwistEvidence State where
  unit := record.unit.toUnit e
  singleBondRotation := record.singleBondRotation
  endpointConformationsDistinct := record.endpointConformationsDistinct
  isBoatState := record.isBoatState
  isChairState := record.isChairState
  candidate := record.candidate
  firstLeg := record.firstLeg
  secondLeg := record.secondLeg

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94TwistEvidence State)
    (valid : record.unit.ValidFor tie.molecule) :
    toSource e (ofSource e tie record valid) = record := by
  cases record with
  | mk unit rotation distinct boat chair candidate firstLeg secondLeg =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit]

end TwistObservation

/-- One encoded P-94 in/out site: the exact framework value, the bridgehead atom and directed
participant over `V`, the supplied bridge-length fact, and the supplied direction. -/
structure EncodedInOutSite (Framework : Type*) (V : Type*) where
  framework : Framework
  bridgehead : V
  directedParticipant : TorsionParticipant V
  bridgeLongEnough : Prop
  direction : BridgeheadDirection

namespace EncodedInOutSite

def relabel (e : V ≃ W) (site : EncodedInOutSite Framework V) :
    EncodedInOutSite Framework W where
  framework := site.framework
  bridgehead := e site.bridgehead
  directedParticipant := mapParticipant e site.directedParticipant
  bridgeLongEnough := site.bridgeLongEnough
  direction := site.direction

@[simp] theorem relabel_symm (e : V ≃ W) (site : EncodedInOutSite Framework V) :
    relabel e.symm (relabel e site) = site := by
  cases site with
  | mk framework bridgehead participant longEnough direction => simp [relabel]

/-- Encode one actual `InOutObservation`. -/
def ofSource (e : SourceAtomIndex source ≃ V)
    (observation : InOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount) :
    EncodedInOutSite Framework V where
  framework := observation.framework
  bridgehead := encodeIndex e observation.bridgehead bridgeheadBound
  directedParticipant := encodeParticipant e observation.directedParticipant participantBound
  bridgeLongEnough := observation.bridgeLongEnough
  direction := observation.direction

/-- Decode one in/out site. -/
def toSource (e : SourceAtomIndex source ≃ V) (site : EncodedInOutSite Framework V) :
    InOutObservation Framework where
  framework := site.framework
  bridgehead := decodeIndex e site.bridgehead
  directedParticipant := decodeParticipant e site.directedParticipant
  bridgeLongEnough := site.bridgeLongEnough
  direction := site.direction

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (observation : InOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount) :
    toSource e (ofSource e observation bridgeheadBound participantBound) = observation := by
  cases observation with
  | mk framework bridgehead participant longEnough direction =>
      simp [toSource, ofSource, decodeParticipant_encodeParticipant]

end EncodedInOutSite

/-- A supplied P-94 in/out pair with the two observations and the bicyclic-framework fact. -/
structure InOutObservationData (Framework : Type*) (V : Type*) where
  unit : EncodedConformationUnit V
  first : EncodedInOutSite Framework V
  second : EncodedInOutSite Framework V
  bicyclicSystem : Prop

namespace InOutObservationData

def relabel (e : V ≃ W) (record : InOutObservationData Framework V) :
    InOutObservationData Framework W where
  unit := record.unit.relabel e
  first := record.first.relabel e
  second := record.second.relabel e
  bicyclicSystem := record.bicyclicSystem

@[simp] theorem relabel_symm (e : V ≃ W) (record : InOutObservationData Framework V) :
    relabel e.symm (relabel e record) = record := by
  cases record with
  | mk unit first second bicyclic => simp [relabel]

/-- Adapt an actual `P94InOutEvidence` record.  The bridgehead and directed-participant bounds of
both supplied sites are explicit exact-validity hypotheses. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94InOutEvidence Framework) (valid : record.unit.ValidFor tie.molecule)
    (firstBridgeheadBound : record.first.bridgehead < source.input.molecule.atomCount)
    (firstParticipantBound : P94ConformationUnit.ParticipantBounded
      record.first.directedParticipant source.input.molecule.atomCount)
    (secondBridgeheadBound : record.second.bridgehead < source.input.molecule.atomCount)
    (secondParticipantBound : P94ConformationUnit.ParticipantBounded
      record.second.directedParticipant source.input.molecule.atomCount) :
    InOutObservationData Framework V where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  first := EncodedInOutSite.ofSource e record.first firstBridgeheadBound firstParticipantBound
  second := EncodedInOutSite.ofSource e record.second secondBridgeheadBound secondParticipantBound
  bicyclicSystem := record.bicyclicSystem

/-- Decode the in/out channel back to the source record. -/
def toSource (e : SourceAtomIndex source ≃ V) (record : InOutObservationData Framework V) :
    P94InOutEvidence Framework where
  unit := record.unit.toUnit e
  first := record.first.toSource e
  second := record.second.toSource e
  bicyclicSystem := record.bicyclicSystem

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94InOutEvidence Framework)
    (valid : record.unit.ValidFor tie.molecule)
    (firstBridgeheadBound : record.first.bridgehead < source.input.molecule.atomCount)
    (firstParticipantBound : P94ConformationUnit.ParticipantBounded
      record.first.directedParticipant source.input.molecule.atomCount)
    (secondBridgeheadBound : record.second.bridgehead < source.input.molecule.atomCount)
    (secondParticipantBound : P94ConformationUnit.ParticipantBounded
      record.second.directedParticipant source.input.molecule.atomCount) :
    toSource e (ofSource e tie record valid firstBridgeheadBound firstParticipantBound
      secondBridgeheadBound secondParticipantBound) = record := by
  cases record with
  | mk unit first second bicyclic =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit,
        EncodedInOutSite.toSource_ofSource]

end InOutObservationData

/-- One encoded exact coordinate observation.  The rational spatial configuration, the exact
interior point and every virtual-point coordinate are retained verbatim; only atom references are
transported to `V`. -/
structure EncodedCoordinateObservation (Framework : Type*) (V : Type*) where
  framework : Framework
  spatial : SpatialConfiguration
  virtualPoints : List (EncodedVirtualTorsionPoint V)
  bridgehead : V
  directedParticipant : TorsionParticipant V
  interior : CartesianPoint3

namespace EncodedCoordinateObservation

def relabel (e : V ≃ W) (observation : EncodedCoordinateObservation Framework V) :
    EncodedCoordinateObservation Framework W where
  framework := observation.framework
  spatial := observation.spatial
  virtualPoints := observation.virtualPoints.map
    (EncodedVirtualTorsionPoint.relabel e)
  bridgehead := e observation.bridgehead
  directedParticipant := mapParticipant e observation.directedParticipant
  interior := observation.interior

@[simp] theorem relabel_symm (e : V ≃ W)
    (observation : EncodedCoordinateObservation Framework V) :
    relabel e.symm (relabel e observation) = observation := by
  cases observation with
  | mk framework spatial virtualPoints bridgehead participant interior =>
      simp [relabel, List.map_map, Function.comp_def]

/-- Adapt one actual `CoordinateInOutObservation`. -/
def ofSource (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    EncodedCoordinateObservation Framework V where
  framework := observation.framework
  spatial := observation.spatial
  virtualPoints := encodeVirtualPoints e observation.virtualPoints virtualBound
  bridgehead := encodeIndex e observation.bridgehead bridgeheadBound
  directedParticipant := encodeParticipant e observation.directedParticipant participantBound
  interior := observation.interior

/-- Decode one coordinate observation. -/
def toSource (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V) :
    CoordinateInOutObservation Framework where
  framework := observation.framework
  spatial := observation.spatial
  virtualPoints := decodeVirtualPoints e observation.virtualPoints
  bridgehead := decodeIndex e observation.bridgehead
  directedParticipant := decodeParticipant e observation.directedParticipant
  interior := observation.interior

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    toSource e (ofSource e observation bridgeheadBound participantBound virtualBound) =
      observation := by
  cases observation with
  | mk framework spatial virtualPoints bridgehead participant interior =>
      simp [toSource, ofSource, decodeParticipant_encodeParticipant,
        decodeVirtualPoints_encodeVirtualPoints]

/-! ### Coordinate interpretation through the common enumeration

`EncodedCoordinateObservation.spatial` is deliberately still the *source-indexed* coordinate list:
the encoding transports atom references and leaves the ordered `SpatialConfiguration` positions
exactly as supplied, so arbitrary source list lengths remain admitted.  The resolver below is the
explicit interpretation bridge: it maps an encoded atom back through the same common enumeration
used by the graph/record adapters and performs the source positional lookup.  It is `Option`-valued,
so a source list with no position at that atom yields `none` rather than a fabricated coordinate.
-/

/-- Evaluate the retained source-indexed coordinate list at an encoded atom through the common
enumeration.  The list is not reindexed or normalized; only the external `V` index is decoded. -/
def pointAt (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V)
    (atom : V) : Option CartesianPoint3 :=
  observation.spatial.positions[(e.symm atom).val]?

/-- Definitional reading of the resolver: it is exactly the source-indexed positional lookup at
the decoded atom. -/
theorem pointAt_eq_source_lookup (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V) (atom : V) :
    pointAt e observation atom =
      observation.spatial.positions[(e.symm atom).val]? := rfl

/-- The resolver is absent exactly when the retained source list has no position at the decoded
atom.  Arbitrary list lengths are admitted; no global length equality is imposed. -/
theorem pointAt_eq_none_iff (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V) (atom : V) :
    pointAt e observation atom = none ↔
      observation.spatial.positions.length ≤ (e.symm atom).val := by
  simp [pointAt]

/-- When the retained source list has a position at the decoded atom, the resolver returns that
exact source point.  Nothing is moved or recomputed. -/
theorem pointAt_eq_getElem (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V) (atom : V)
    (bound : (e.symm atom).val < observation.spatial.positions.length) :
    pointAt e observation atom =
      some observation.spatial.positions[(e.symm atom).val] := by
  simp [pointAt, List.getElem?_eq_getElem bound]

/-- Source ingress lookup recovery: evaluating a coordinate observation adapted from an actual
`CoordinateInOutObservation` at an encoded source atom returns exactly the original
source-indexed coordinate lookup.  The spatial list itself is the unchanged source list. -/
@[simp] theorem pointAt_ofSource (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (index : SourceAtomIndex source) :
    pointAt e (ofSource e observation bridgeheadBound participantBound virtualBound)
        (e index) =
      observation.spatial.positions[index.val]? := by
  simp [pointAt, ofSource]

/-- Source ingress lookup recovery stated at a bounded source atom number. -/
@[simp] theorem pointAt_ofSource_encodeIndex (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (atom : ℕ) (bound : atom < source.input.molecule.atomCount) :
    pointAt e (ofSource e observation bridgeheadBound participantBound virtualBound)
        (encodeIndex e atom bound) =
      observation.spatial.positions[atom]? := by
  simp [encodeIndex]

/-- Coordinate interpretation is invariant under relabelling with the composed enumeration: the
left side uses `SourceAtomIndex source ≃ V ≃ W` and the relabelled observation, the right side
uses the original enumeration. -/
@[simp] theorem pointAt_relabel (e : SourceAtomIndex source ≃ V) (r : V ≃ W)
    (observation : EncodedCoordinateObservation Framework V) (atom : V) :
    pointAt (e.trans r) (relabel r observation) (r atom) = pointAt e observation atom := by
  simp [pointAt, relabel]

/-- Exact source bridgehead decoding: the decoded bridgehead of any encoded coordinate observation
is the source number of the encoded bridgehead. -/
@[simp] theorem toSource_bridgehead (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V) :
    (toSource e observation).bridgehead = decodeIndex e observation.bridgehead := rfl

/-- Exact bridgehead lookup: resolving the coordinate at the encoded bridgehead of a source-adapted
observation returns exactly the source bridgehead coordinate. -/
@[simp] theorem pointAt_bridgehead_ofSource (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    pointAt e (ofSource e observation bridgeheadBound participantBound virtualBound)
        (encodeIndex e observation.bridgehead bridgeheadBound) =
      observation.spatial.positions[observation.bridgehead]? := by
  simp [encodeIndex]

/-- Exact directed-participant owner decoding: the owner atom of the decoded participant is the
source number of the encoded participant owner. -/
@[simp] theorem toSource_directedParticipant_owner (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V) :
    participantOwner (toSource e observation).directedParticipant =
      decodeIndex e (participantOwner observation.directedParticipant) := by
  cases observation with
  | mk framework spatial virtualPoints bridgehead participant interior =>
      cases participant <;> rfl

/-- Exact directed-participant owner lookup: resolving the coordinate at the atom owner of the
encoded directed participant returns exactly the source coordinate at the source participant's
owner.  This covers all three actual participant kinds (`atom`, `lonePair`, `duplicateAtom`). -/
@[simp] theorem pointAt_directedParticipant_ofSource (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    pointAt e (ofSource e observation bridgeheadBound participantBound virtualBound)
        (participantOwner
          (encodeParticipant e observation.directedParticipant participantBound)) =
      observation.spatial.positions[participantOwner observation.directedParticipant]? := by
  cases observation with
  | mk framework spatial virtualPoints bridgehead participant interior =>
      cases participant <;>
        simp [pointAt, ofSource, encodeParticipant, participantOwner, encodeIndex]

/-- Owner lookup for an ordinary atom participant resolves at the encoded atom itself. -/
@[simp] theorem pointAt_owner_atom (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V)
    (atom : ℕ) (bound : atom < source.input.molecule.atomCount) :
    pointAt e observation
        (participantOwner (encodeParticipant e (.atom atom) bound)) =
      pointAt e observation (encodeIndex e atom bound) := by
  simp [encodeParticipant, participantOwner]

/-- Owner lookup for a lone-pair participant resolves at its encoded centre atom. -/
@[simp] theorem pointAt_owner_lonePair (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V)
    (center : ℕ) (bound : center < source.input.molecule.atomCount) :
    pointAt e observation
        (participantOwner (encodeParticipant e (.lonePair center) bound)) =
      pointAt e observation (encodeIndex e center bound) := by
  simp [encodeParticipant, participantOwner]

/-- Owner lookup for a duplicate-atom participant resolves at its encoded original atom. -/
@[simp] theorem pointAt_owner_duplicateAtom (e : SourceAtomIndex source ≃ V)
    (observation : EncodedCoordinateObservation Framework V)
    (original : ℕ) (bound : original < source.input.molecule.atomCount) :
    pointAt e observation
        (participantOwner (encodeParticipant e (.duplicateAtom original) bound)) =
      pointAt e observation (encodeIndex e original bound) := by
  simp [encodeParticipant, participantOwner]

/-- Look up the exact retained coordinate of one virtual point in an encoded coordinate
observation.  The ledger is the unchanged ordered source ledger with only participant labels
transported, so this is the encoded mirror of `VirtualTorsionPointLedger.lookup`; a missing
participant yields `none` and no point is fabricated. -/
def virtualPointAt [DecidableEq V]
    (observation : EncodedCoordinateObservation Framework V)
    (participant : EncodedVirtualTorsionParticipant V) : Option CartesianPoint3 :=
  EncodedVirtualTorsionPoint.lookup observation.virtualPoints participant

/-- Source ingress virtual-point lookup recovery: the encoded ledger lookup at an encoded virtual
participant returns exactly the source ledger lookup at the corresponding primitive participant,
for both actual virtual participant kinds. -/
@[simp] theorem virtualPointAt_ofSource [DecidableEq V]
    (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (participant : VirtualTorsionParticipant)
    (participantBound' : VirtualParticipantBounded participant
      source.input.molecule.atomCount) :
    virtualPointAt (ofSource e observation bridgeheadBound participantBound virtualBound)
        (encodeVirtualParticipant e participant participantBound') =
      VirtualTorsionPointLedger.lookup observation.virtualPoints participant := by
  simp [virtualPointAt, ofSource, lookup_encodeVirtualPoints]

/-- Virtual-point lookup recovery for a lone-pair phantom: the encoded ledger returns exactly the
source ledger point at the corresponding source lone-pair centre. -/
@[simp] theorem virtualPointAt_ofSource_lonePair [DecidableEq V]
    (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (center : ℕ) (centerBound : center < source.input.molecule.atomCount) :
    virtualPointAt (ofSource e observation bridgeheadBound participantBound virtualBound)
        (.lonePair (encodeIndex e center centerBound)) =
      VirtualTorsionPointLedger.lookup observation.virtualPoints (.lonePair center) := by
  simpa [encodeVirtualParticipant] using
    virtualPointAt_ofSource e observation bridgeheadBound participantBound virtualBound
      (.lonePair center) centerBound

/-- Virtual-point lookup recovery for a multiple-bond duplicate: the encoded ledger returns exactly
the source ledger point at the corresponding source original atom. -/
@[simp] theorem virtualPointAt_ofSource_duplicateAtom [DecidableEq V]
    (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (original : ℕ) (originalBound : original < source.input.molecule.atomCount) :
    virtualPointAt (ofSource e observation bridgeheadBound participantBound virtualBound)
        (.duplicateAtom (encodeIndex e original originalBound)) =
      VirtualTorsionPointLedger.lookup observation.virtualPoints
        (.duplicateAtom original) := by
  simpa [encodeVirtualParticipant] using
    virtualPointAt_ofSource e observation bridgeheadBound participantBound virtualBound
      (.duplicateAtom original) originalBound

/-- The encoded virtual-point lookup preserves present-versus-absent status exactly: it is `some`
on the encoded side exactly when the source ledger lookup is `some`. -/
@[simp] theorem virtualPointAt_ofSource_isSome [DecidableEq V]
    (e : SourceAtomIndex source ≃ V)
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (virtualBound : ∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (participant : VirtualTorsionParticipant)
    (participantBound' : VirtualParticipantBounded participant
      source.input.molecule.atomCount) :
    (virtualPointAt (ofSource e observation bridgeheadBound participantBound virtualBound)
        (encodeVirtualParticipant e participant participantBound')).isSome =
      (VirtualTorsionPointLedger.lookup observation.virtualPoints participant).isSome := by
  rw [virtualPointAt_ofSource]

/-- Virtual-point lookup is invariant under relabelling: the coordinate found for a relabelled
participant in the relabelled ledger is the coordinate found for the original participant. -/
@[simp] theorem virtualPointAt_relabel [DecidableEq V] [DecidableEq W]
    (observation : EncodedCoordinateObservation Framework V) (r : V ≃ W)
    (participant : EncodedVirtualTorsionParticipant V) :
    virtualPointAt (relabel r observation)
        (EncodedVirtualTorsionParticipant.relabel r participant) =
      virtualPointAt observation participant := by
  simp [virtualPointAt, relabel, EncodedVirtualTorsionPoint.lookup_relabel]

end EncodedCoordinateObservation

/-- The paired coordinate in/out observation channel: the unit together with both exact
framework observations. -/
structure CoordinateInOutData (Framework : Type*) (V : Type*) where
  unit : EncodedConformationUnit V
  first : EncodedCoordinateObservation Framework V
  second : EncodedCoordinateObservation Framework V

namespace CoordinateInOutData

def relabel (e : V ≃ W) (record : CoordinateInOutData Framework V) :
    CoordinateInOutData Framework W where
  unit := record.unit.relabel e
  first := record.first.relabel e
  second := record.second.relabel e

@[simp] theorem relabel_symm (e : V ≃ W) (record : CoordinateInOutData Framework V) :
    relabel e.symm (relabel e record) = record := by
  cases record with
  | mk unit first second => simp [relabel]

/-- Adapt an actual `CoordinateInOutInput`. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (input : CoordinateInOutInput Framework) (valid : input.unit.ValidFor tie.molecule)
    (firstBridgeheadBound : input.first.bridgehead < source.input.molecule.atomCount)
    (firstParticipantBound : P94ConformationUnit.ParticipantBounded
      input.first.directedParticipant source.input.molecule.atomCount)
    (firstVirtualBound : ∀ point ∈ input.first.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (secondBridgeheadBound : input.second.bridgehead < source.input.molecule.atomCount)
    (secondParticipantBound : P94ConformationUnit.ParticipantBounded
      input.second.directedParticipant source.input.molecule.atomCount)
    (secondVirtualBound : ∀ point ∈ input.second.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    CoordinateInOutData Framework V where
  unit := EncodedConformationUnit.ofUnit e tie input.unit valid
  first := EncodedCoordinateObservation.ofSource e input.first
    firstBridgeheadBound firstParticipantBound firstVirtualBound
  second := EncodedCoordinateObservation.ofSource e input.second
    secondBridgeheadBound secondParticipantBound secondVirtualBound

/-- Decode the coordinate in/out channel back to the source input. -/
def toSource (e : SourceAtomIndex source ≃ V) (record : CoordinateInOutData Framework V) :
    CoordinateInOutInput Framework where
  unit := record.unit.toUnit e
  first := record.first.toSource e
  second := record.second.toSource e

@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (input : CoordinateInOutInput Framework)
    (valid : input.unit.ValidFor tie.molecule)
    (firstBridgeheadBound : input.first.bridgehead < source.input.molecule.atomCount)
    (firstParticipantBound : P94ConformationUnit.ParticipantBounded
      input.first.directedParticipant source.input.molecule.atomCount)
    (firstVirtualBound : ∀ point ∈ input.first.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (secondBridgeheadBound : input.second.bridgehead < source.input.molecule.atomCount)
    (secondParticipantBound : P94ConformationUnit.ParticipantBounded
      input.second.directedParticipant source.input.molecule.atomCount)
    (secondVirtualBound : ∀ point ∈ input.second.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    toSource e (ofSource e tie input valid firstBridgeheadBound firstParticipantBound
      firstVirtualBound secondBridgeheadBound secondParticipantBound secondVirtualBound) =
      input := by
  cases input with
  | mk unit first second =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit,
        EncodedCoordinateObservation.toSource_ofSource]

end CoordinateInOutData

/-! ## The optional observation payload: absence versus present-empty -/

/-- One independent observation payload.  Each channel is optional: `none` means that no such
observation was supplied, while `some` records a supplied observation even when its ordered lists
are empty.  Channels are independent so a caller can attach exactly what the source records
provide. -/
structure ObservationPayload (V : Type*) (State : Type*) (Framework : Type*) where
  conformerPair? : Option (ConformerPairObservation V State) := none
  torsion? : Option (TorsionObservation V) := none
  twist? : Option (TwistObservation V State) := none
  inOut? : Option (InOutObservationData Framework V) := none
  coordinateInOut? : Option (CoordinateInOutData Framework V) := none

namespace ObservationPayload

/-- The supplied-but-empty payload.  It is a genuine payload, not an absent channel. -/
def empty : ObservationPayload V State Framework := {}

/-- Relabel every atom reference in every present channel.  Absent channels stay absent. -/
def relabel (e : V ≃ W) (payload : ObservationPayload V State Framework) :
    ObservationPayload W State Framework where
  conformerPair? := payload.conformerPair?.map (ConformerPairObservation.relabel e)
  torsion? := payload.torsion?.map (TorsionObservation.relabel e)
  twist? := payload.twist?.map (TwistObservation.relabel e)
  inOut? := payload.inOut?.map (InOutObservationData.relabel e)
  coordinateInOut? := payload.coordinateInOut?.map (CoordinateInOutData.relabel e)

@[simp] theorem relabel_symm (e : V ≃ W) (payload : ObservationPayload V State Framework) :
    relabel e.symm (relabel e payload) = payload := by
  cases payload with
  | mk conformerPair? torsion? twist? inOut? coordinateInOut? =>
      cases conformerPair? <;> cases torsion? <;> cases twist? <;> cases inOut? <;>
        cases coordinateInOut? <;> simp [relabel]

@[simp] theorem empty_conformerPair? :
    (empty : ObservationPayload V State Framework).conformerPair? = none := rfl

@[simp] theorem empty_torsion? :
    (empty : ObservationPayload V State Framework).torsion? = none := rfl

@[simp] theorem empty_twist? :
    (empty : ObservationPayload V State Framework).twist? = none := rfl

@[simp] theorem empty_inOut? :
    (empty : ObservationPayload V State Framework).inOut? = none := rfl

@[simp] theorem empty_coordinateInOut? :
    (empty : ObservationPayload V State Framework).coordinateInOut? = none := rfl

/-- A supplied empty payload is provably not the absence of a payload. -/
theorem present_empty_ne_absent :
    (some (empty : ObservationPayload V State Framework) :
      Option (ObservationPayload V State Framework)) ≠ none := by
  simp

end ObservationPayload

/-! ## The ordered conformer/observation family -/

/-- Scope/count agreement, stated exactly as the existing
`FiniteConformerCollection.WellScoped` predicate on the decoded collection. -/
def ConformerScopeRespected (scope : ConformerScope) (count : ℕ) : Prop :=
  match scope with
  | ConformerScope.empty => count = 0
  | ConformerScope.unknown => count = 0
  | ConformerScope.selected => True

/-- An ordered family of real conformations of one certified source, over an arbitrary atom index
`V`, together with one optional observation payload.  The `Fin count →` indexing retains order and
multiplicity exactly: repeated conformations at distinct positions are not deduplicated. -/
structure OrderedObservationFamily (source : CertifiedAuthoritativeChemicalInput)
    (V : Type*) (State : Type*) (Framework : Type*) where
  scope : ConformerScope
  count : ℕ
  conformer : Fin count → MolecularConformation V
  wellScoped : ConformerScopeRespected scope count
  observation? : Option (ObservationPayload V State Framework) := none

namespace OrderedObservationFamily

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The supplied conformer family as an ordered list.  Its length is the declared count. -/
def conformerList (family : OrderedObservationFamily source V State Framework) :
    List (MolecularConformation V) :=
  List.ofFn family.conformer

@[simp] theorem conformerList_length (family : OrderedObservationFamily source V State Framework) :
    family.conformerList.length = family.count := by
  simp [conformerList]

/-- The ordered list is exactly the indexed family, position by position. -/
theorem conformerList_getElem (family : OrderedObservationFamily source V State Framework)
    (index : ℕ) (bound : index < family.count) :
    family.conformerList[index]' (by simpa using bound) = family.conformer ⟨index, bound⟩ := by
  simp [conformerList]

/-- Relabel every atom-referencing field, including every conformation and every present
observation channel. -/
def relabel (e : V ≃ W) (family : OrderedObservationFamily source V State Framework) :
    OrderedObservationFamily source W State Framework where
  scope := family.scope
  count := family.count
  conformer := fun index => MolecularConformation.reindex e (family.conformer index)
  wellScoped := family.wellScoped
  observation? := family.observation?.map (ObservationPayload.relabel e)

@[simp] theorem relabel_scope (e : V ≃ W)
    (family : OrderedObservationFamily source V State Framework) :
    (relabel e family).scope = family.scope := rfl

@[simp] theorem relabel_count (e : V ≃ W)
    (family : OrderedObservationFamily source V State Framework) :
    (relabel e family).count = family.count := rfl

@[simp] theorem relabel_conformer (e : V ≃ W)
    (family : OrderedObservationFamily source V State Framework) (index : Fin family.count) :
    (relabel e family).conformer index =
      MolecularConformation.reindex e (family.conformer index) := rfl

@[simp] theorem relabel_observation? (e : V ≃ W)
    (family : OrderedObservationFamily source V State Framework) :
    (relabel e family).observation? =
      family.observation?.map (ObservationPayload.relabel e) := rfl

/-- Relabelling by an equivalence and then by its inverse is the identity on the whole family,
including scope, count, order/multiplicity and every observation channel. -/
@[simp] theorem relabel_symm (e : V ≃ W)
    (family : OrderedObservationFamily source V State Framework) :
    relabel e.symm (relabel e family) = family := by
  cases family with
  | mk scope count conformer wellScoped observation? =>
      cases observation? with
      | none =>
          simp [relabel, MolecularConformation.reindex_reindex]
      | some payload =>
          simp [relabel, MolecularConformation.reindex_reindex,
            ObservationPayload.relabel_symm]

/-- Relabelling is injective. -/
theorem relabel_injective (e : V ≃ W) :
    Function.Injective
      (relabel (source := source) (State := State) (Framework := Framework) e) := by
  intro first second equal
  have := congrArg (relabel (source := source) (State := State) (Framework := Framework) e.symm)
    equal
  simpa using this

/-- Relabelling is surjective. -/
theorem relabel_surjective (e : V ≃ W) :
    Function.Surjective
      (relabel (source := source) (State := State) (Framework := Framework) e) := by
  intro family
  exact ⟨relabel e.symm family, by
    simpa using (relabel_symm (e := e.symm) (source := source) (State := State)
      (Framework := Framework) family)⟩

/-- Relabelling is bijective. -/
theorem relabel_bijective (e : V ≃ W) :
    Function.Bijective
      (relabel (source := source) (State := State) (Framework := Framework) e) :=
  ⟨relabel_injective e, relabel_surjective e⟩

/-! ### Concrete Fin encoding through the actual source enumeration -/

/-- Encode a family over an arbitrary `V` into the concrete source enumeration
`SourceAtomIndex source = Fin source.input.molecule.atomCount`. -/
def finEncode (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source V State Framework) :
    OrderedObservationFamily source (SourceAtomIndex source) State Framework :=
  relabel e.symm family

/-- Decode a family from the concrete source enumeration back to `V`. -/
def finDecode (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source (SourceAtomIndex source) State Framework) :
    OrderedObservationFamily source V State Framework :=
  relabel e family

@[simp] theorem finDecode_finEncode (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source V State Framework) :
    finDecode e (finEncode e family) = family := by
  simpa [finEncode, finDecode] using
    (relabel_symm (source := source) (State := State) (Framework := Framework) e.symm family)

@[simp] theorem finEncode_finDecode (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source (SourceAtomIndex source) State Framework) :
    finEncode e (finDecode e family) = family := by
  simp [finEncode, finDecode]

/-- A general cardinality-based Fin encoding for any finite `V`. -/
def finEncodeCard [Fintype V] (e : V ≃ Fin (Fintype.card V))
    (family : OrderedObservationFamily source V State Framework) :
    OrderedObservationFamily source (Fin (Fintype.card V)) State Framework :=
  relabel e family

/-- Decoding a cardinality-based Fin encoding returns the original family. -/
@[simp] theorem finEncodeCard_symm [Fintype V] (e : V ≃ Fin (Fintype.card V))
    (family : OrderedObservationFamily source V State Framework) :
    relabel e.symm (finEncodeCard e family) = family := by
  simp [finEncodeCard]

/-! ### Exact source ingress for the conformer family -/

/-- Decode the family to an actual `FiniteConformerCollection` over the source atom index.  The
conformer is `MolecularConformation (SourceAtomIndex source)`, i.e. exactly one real point per
source atom; only the atom labels are transported. -/
def toFiniteConformerCollection (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source V State Framework) :
    FiniteConformerCollection source where
  scope := family.scope
  count := family.count
  conformer := fun index => MolecularConformation.reindex e.symm (family.conformer index)

@[simp] theorem toFiniteConformerCollection_scope (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source V State Framework) :
    (toFiniteConformerCollection e family).scope = family.scope := rfl

@[simp] theorem toFiniteConformerCollection_count (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source V State Framework) :
    (toFiniteConformerCollection e family).count = family.count := rfl

@[simp] theorem toFiniteConformerCollection_conformer (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source V State Framework) (index : Fin family.count) :
    (toFiniteConformerCollection e family).conformer index =
      MolecularConformation.reindex e.symm (family.conformer index) := rfl

/-- Encoding an arbitrary finite conformer collection into the family.  The declared scope,
count, order and multiplicity are retained verbatim; no conformer is dropped or deduplicated. -/
def ofFiniteConformerCollection (e : SourceAtomIndex source ≃ V)
    (collection : FiniteConformerCollection source) (wellScoped : collection.WellScoped) :
    OrderedObservationFamily source V State Framework where
  scope := collection.scope
  count := collection.count
  conformer := fun index => MolecularConformation.reindex e (collection.conformer index)
  wellScoped := wellScoped

/-- Exact source ingress: decoding after encoding recovers the whole finite collection. -/
@[simp] theorem toFiniteConformerCollection_ofFiniteConformerCollection
    (e : SourceAtomIndex source ≃ V) (collection : FiniteConformerCollection source)
    (wellScoped : collection.WellScoped) :
    toFiniteConformerCollection e
        (ofFiniteConformerCollection (State := State) (Framework := Framework) e collection
          wellScoped) = collection := by
  cases collection with
  | mk scope count conformer =>
      change (⟨scope, count, fun index => MolecularConformation.reindex e.symm
        (MolecularConformation.reindex e (conformer index))⟩ :
          FiniteConformerCollection source) = ⟨scope, count, conformer⟩
      apply congrArg (fun family : Fin count → MolecularConformation (SourceAtomIndex source) =>
        (⟨scope, count, family⟩ : FiniteConformerCollection source))
      funext index
      exact MolecularConformation.reindex_reindex e (conformer index)

/-- The conformer-collection ingress supplies no observation payload: absence is `none`. -/
@[simp] theorem ofFiniteConformerCollection_observation?
    (e : SourceAtomIndex source ≃ V) (collection : FiniteConformerCollection source)
    (wellScoped : collection.WellScoped) :
    (ofFiniteConformerCollection (State := State) (Framework := Framework) e collection
      wellScoped).observation? = none := rfl

/-- Certified ingress: the certified collection's scope proof is carried into the family. -/
def ofCertifiedFiniteConformerCollection (e : SourceAtomIndex source ≃ V)
    (certified : CertifiedFiniteConformerCollection source) :
    OrderedObservationFamily source V State Framework :=
  ofFiniteConformerCollection (State := State) (Framework := Framework) e
    certified.collection certified.wellScoped

/-- Decode to a certified finite collection.  The family's scope proof is exactly the decoded
collection's `WellScoped` proof, so the scope metadata is not discarded. -/
def toCertifiedFiniteConformerCollection (e : SourceAtomIndex source ≃ V)
    (family : OrderedObservationFamily source V State Framework) :
    CertifiedFiniteConformerCollection source where
  collection := toFiniteConformerCollection e family
  wellScoped := family.wellScoped

/-- Exact certified source ingress, including the scope proof. -/
@[simp] theorem toCertifiedFiniteConformerCollection_ofCertifiedFiniteConformerCollection
    (e : SourceAtomIndex source ≃ V) (certified : CertifiedFiniteConformerCollection source) :
    toCertifiedFiniteConformerCollection e
        (ofCertifiedFiniteConformerCollection (State := State) (Framework := Framework) e
          certified) = certified := by
  cases certified with
  | mk collection wellScoped =>
      change (⟨toFiniteConformerCollection e
          (ofFiniteConformerCollection (State := State) (Framework := Framework) e
            collection wellScoped), wellScoped⟩ :
            CertifiedFiniteConformerCollection source) = ⟨collection, wellScoped⟩
      simp [toFiniteConformerCollection_ofFiniteConformerCollection]

/-! ### Satellite attachment of one payload -/

/-- Attach one observation payload to a family, overwriting only the observation channel.  Scope,
count and every conformer are provably unchanged, so this channel can be composed onto an
arbitrary existing family over `V`. -/
def attachObservation (family : OrderedObservationFamily source V State Framework)
    (payload : ObservationPayload V State Framework) :
    OrderedObservationFamily source V State Framework :=
  { family with observation? := some payload }

@[simp] theorem attachObservation_scope (family : OrderedObservationFamily source V State Framework)
    (payload : ObservationPayload V State Framework) :
    (attachObservation family payload).scope = family.scope := rfl

@[simp] theorem attachObservation_count (family : OrderedObservationFamily source V State Framework)
    (payload : ObservationPayload V State Framework) :
    (attachObservation family payload).count = family.count := rfl

@[simp] theorem attachObservation_conformer
    (family : OrderedObservationFamily source V State Framework)
    (payload : ObservationPayload V State Framework) (index : Fin family.count) :
    (attachObservation family payload).conformer index = family.conformer index := rfl

/-- The attached payload is recovered exactly, including a supplied empty payload. -/
@[simp] theorem attachObservation_observation?
    (family : OrderedObservationFamily source V State Framework)
    (payload : ObservationPayload V State Framework) :
    (attachObservation family payload).observation? = some payload := rfl

/-- Attaching the present-empty payload is still a present observation channel. -/
@[simp] theorem attachObservation_empty
    (family : OrderedObservationFamily source V State Framework) :
    (attachObservation family ObservationPayload.empty).observation? =
      some ObservationPayload.empty := rfl

/-- A family with no supplied conformers; used by the record adapters that supply observations
but no conformer collection.  The scope is `unknown` (no information), not a positive emptiness
claim. -/
def emptyObservationalFamily (source : CertifiedAuthoritativeChemicalInput)
    (V State Framework : Type*) : OrderedObservationFamily source V State Framework where
  scope := ConformerScope.unknown
  count := 0
  conformer := Fin.elim0
  wellScoped := rfl

@[simp] theorem emptyObservationalFamily_scope (source : CertifiedAuthoritativeChemicalInput)
    (V State Framework : Type*) :
    (emptyObservationalFamily source V State Framework).scope = ConformerScope.unknown := rfl

@[simp] theorem emptyObservationalFamily_count (source : CertifiedAuthoritativeChemicalInput)
    (V State Framework : Type*) :
    (emptyObservationalFamily source V State Framework).count = 0 := rfl

@[simp] theorem emptyObservationalFamily_observation?
    (source : CertifiedAuthoritativeChemicalInput) (V State Framework : Type*) :
    (emptyObservationalFamily source V State Framework).observation? = none := rfl

/-! ### Record-family adapters into the satellite channel -/

/-- Adapt a `P94ConformerEvidence` record into the satellite family. -/
def ofConformerEvidence (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94ConformerEvidence State) (valid : record.unit.ValidFor tie.molecule) :
    OrderedObservationFamily source V State Framework :=
  attachObservation (emptyObservationalFamily source V State Framework)
    { conformerPair? := some (ConformerPairObservation.ofSource e tie record valid) }

/-- Adapt a `P94TwistEvidence` record, retaining its candidate reference and ordered legs. -/
def ofTwistEvidence (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94TwistEvidence State) (valid : record.unit.ValidFor tie.molecule) :
    OrderedObservationFamily source V State Framework :=
  attachObservation (emptyObservationalFamily source V State Framework)
    { twist? := some (TwistObservation.ofSource e tie record valid) }

/-- Adapt a `P94TorsionEvidence` record, retaining alternative lists, rankings and selections. -/
def ofTorsionEvidence (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94TorsionEvidence) (valid : record.unit.ValidFor tie.molecule)
    (frameFrontBound : P94ConformationUnit.ParticipantBounded record.frame.front
      source.input.molecule.atomCount)
    (frameRearBound : P94ConformationUnit.ParticipantBounded record.frame.rear
      source.input.molecule.atomCount)
    (candidateBounds : record.CandidateParticipantsBounded
      source.input.molecule.atomCount) :
    OrderedObservationFamily source V State Framework :=
  attachObservation (emptyObservationalFamily source V State Framework)
    { torsion? := some (TorsionObservation.ofSource e tie record valid
        frameFrontBound frameRearBound candidateBounds) }

/-- Adapt a `P94InOutEvidence` record, retaining both paired observations. -/
def ofInOutEvidence (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94InOutEvidence Framework) (valid : record.unit.ValidFor tie.molecule)
    (firstBridgeheadBound : record.first.bridgehead < source.input.molecule.atomCount)
    (firstParticipantBound : P94ConformationUnit.ParticipantBounded
      record.first.directedParticipant source.input.molecule.atomCount)
    (secondBridgeheadBound : record.second.bridgehead < source.input.molecule.atomCount)
    (secondParticipantBound : P94ConformationUnit.ParticipantBounded
      record.second.directedParticipant source.input.molecule.atomCount) :
    OrderedObservationFamily source V State Framework :=
  attachObservation (emptyObservationalFamily source V State Framework)
    { inOut? := some (InOutObservationData.ofSource e tie record valid
        firstBridgeheadBound firstParticipantBound
        secondBridgeheadBound secondParticipantBound) }

/-- Adapt a paired coordinate in/out input, retaining both exact spatial configurations, both
interior points and both virtual-point ledgers. -/
def ofCoordinateInOutInput (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (input : CoordinateInOutInput Framework) (valid : input.unit.ValidFor tie.molecule)
    (firstBridgeheadBound : input.first.bridgehead < source.input.molecule.atomCount)
    (firstParticipantBound : P94ConformationUnit.ParticipantBounded
      input.first.directedParticipant source.input.molecule.atomCount)
    (firstVirtualBound : ∀ point ∈ input.first.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)
    (secondBridgeheadBound : input.second.bridgehead < source.input.molecule.atomCount)
    (secondParticipantBound : P94ConformationUnit.ParticipantBounded
      input.second.directedParticipant source.input.molecule.atomCount)
    (secondVirtualBound : ∀ point ∈ input.second.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount) :
    OrderedObservationFamily source V State Framework :=
  attachObservation (emptyObservationalFamily source V State Framework)
    { coordinateInOut? := some (CoordinateInOutData.ofSource e tie input valid
        firstBridgeheadBound firstParticipantBound firstVirtualBound
        secondBridgeheadBound secondParticipantBound secondVirtualBound) }

@[simp] theorem ofTwistEvidence_scope (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94TwistEvidence State)
    (valid : record.unit.ValidFor tie.molecule) :
    (ofTwistEvidence (Framework := Framework) e tie record valid).scope =
      ConformerScope.unknown := rfl

@[simp] theorem ofTwistEvidence_observation?_isSome (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94TwistEvidence State)
    (valid : record.unit.ValidFor tie.molecule) :
    ((ofTwistEvidence (Framework := Framework) e tie record valid).observation?).isSome = true := rfl

/-- The conformer channel of a record adapter is exactly the unknown collection: no conformers
were supplied by the record, and this is not a claim that none exist. -/
@[simp] theorem toFiniteConformerCollection_ofTwistEvidence (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94TwistEvidence State)
    (valid : record.unit.ValidFor tie.molecule) :
    toFiniteConformerCollection e
        (ofTwistEvidence (State := State) (Framework := Framework) e tie record valid) =
      FiniteConformerCollection.unknown source := by
  change (⟨ConformerScope.unknown, 0,
      (fun index : Fin 0 => MolecularConformation.reindex e.symm (Fin.elim0 index))⟩ :
        FiniteConformerCollection source) =
    ⟨ConformerScope.unknown, 0,
      (Fin.elim0 : Fin 0 → MolecularConformation (SourceAtomIndex source))⟩
  apply congrArg (fun conformer : Fin 0 → MolecularConformation (SourceAtomIndex source) =>
    (⟨ConformerScope.unknown, 0, conformer⟩ : FiniteConformerCollection source))
  funext index
  exact Fin.elim0 index

/-! ### Payload recovery from the encoded family -/

/-- The twist payload decoded from an adapter is exactly the source record. -/
theorem ofTwistEvidence_payload_toSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94TwistEvidence State)
    (valid : record.unit.ValidFor tie.molecule) :
    ∃ payload : ObservationPayload V State Framework,
      (ofTwistEvidence (Framework := Framework) e tie record valid).observation? = some payload ∧
        ∃ encoded : TwistObservation V State,
          payload.twist? = some encoded ∧ encoded.toSource e = record := by
  refine ⟨{ twist? := some (TwistObservation.ofSource e tie record valid) }, rfl,
    TwistObservation.ofSource e tie record valid, rfl, ?_⟩
  exact TwistObservation.toSource_ofSource e tie record valid

/-- The conformer-pair payload decoded from an adapter is exactly the source record. -/
theorem ofConformerEvidence_payload_toSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94ConformerEvidence State)
    (valid : record.unit.ValidFor tie.molecule) :
    ∃ payload : ObservationPayload V State Framework,
      (ofConformerEvidence (Framework := Framework) e tie record valid).observation? = some payload ∧
        ∃ encoded : ConformerPairObservation V State,
          payload.conformerPair? = some encoded ∧
            encoded.toSource e = record := by
  refine ⟨{ conformerPair? := some (ConformerPairObservation.ofSource e tie record valid) }, rfl,
    ConformerPairObservation.ofSource e tie record valid, rfl, ?_⟩
  exact ConformerPairObservation.toSource_ofSource e tie record valid

/-! ## Set-level image roundtrip -/

/-- An arbitrary joint set of families survives relabelling and inverse relabelling exactly. -/
theorem relabel_image_roundtrip (e : V ≃ W)
    (families : Set (OrderedObservationFamily source V State Framework)) :
    relabel (source := source) (State := State) (Framework := Framework) e.symm ''
        (relabel (source := source) (State := State) (Framework := Framework) e '' families) =
      families := by
  rw [Set.image_image]
  have composeIdentity :
      (fun family : OrderedObservationFamily source V State Framework =>
        relabel (source := source) (State := State) (Framework := Framework) e.symm
          (relabel (source := source) (State := State) (Framework := Framework) e family)) =
        id := by
    funext family
    exact relabel_symm e family
  rw [composeIdentity, Set.image_id]

/-- The same set-level roundtrip stated with the concrete `Fin` encoding through the actual source
enumeration. -/
theorem finDecode_image_finEncode (e : SourceAtomIndex source ≃ V)
    (families : Set (OrderedObservationFamily source V State Framework)) :
    finDecode (source := source) (State := State) (Framework := Framework) e ''
        (finEncode (source := source) (State := State) (Framework := Framework) e '' families) =
      families := by
  simpa [finEncode, finDecode] using
    (relabel_image_roundtrip (source := source) (State := State) (Framework := Framework)
      e.symm families)

/-! ## Distinguishing absence from present-empty explicitly -/

/-- Positive emptiness and missing information are distinct scopes. -/
theorem empty_scope_ne_unknown : ConformerScope.empty ≠ ConformerScope.unknown := by
  decide

/-- Both non-selected scopes force count zero, but they retain their distinct meaning. -/
theorem nonselected_scope_count_zero (scope : ConformerScope) (count : ℕ)
    (respected : ConformerScopeRespected scope count) (nonselected : scope ≠ .selected) :
    count = 0 := by
  cases scope with
  | empty => exact respected
  | selected => exact absurd rfl nonselected
  | unknown => exact respected

/-- An absent observation channel is not a supplied empty payload. -/
theorem absent_ne_present_empty :
    (none : Option (ObservationPayload V State Framework)) ≠
      some ObservationPayload.empty := by
  simp

end OrderedObservationFamily
end OrganicStereoOrderedObservationFamily
end TetraStereo.OneCenter
