import TetraStereo.OneCenter.IUPACP94AuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoP94CompleteEvidenceIngress

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Exact source ingress for the P-94 authority observation

`IUPACP94AuthorityCarrier.P94AuthorityObservation` (line 214) is the authority boundary: one raw
parser molecule, one complete `P94ConformationEvidence Nat ThetaFramework` record, one typed
`P94AuthorityClaim`, and an optional ordered pair of exact `CoordinateInOutObservation
ThetaFramework` certificates.  This module gives that *whole* type an exact encoded
representation over an arbitrary finite atom index `V`, and proves that decoding recovers the
original observation from `ValidFor` alone.

The nine-constructor evidence codec is the approved
`OrganicStereoP94CompleteEvidenceIngress.EncodedConformationEvidence` API; it is imported and
consumed, not duplicated.

The representation is structural, not a sidecar:

* the raw molecule is retained verbatim and bound to the certified source by the exact conversion
  proof `molecule.toSemanticMolecule? = some source.input.molecule` (a `RawSourceTie`); no graph
  inverse is invented and no atom-count heuristic replaces molecule equality;
* every atom reference of the evidence and of both coordinate certificates is rewritten through
  the single bijection `SourceAtomIndex source ≃ V`; opaque geometric payloads (angles, plane
  sides, virtual points, exact rational configurations, proposition witnesses) are copied
  verbatim;
* the claim stays a typed `P94AuthorityClaim`, not a descriptor string;
* `inOutCertificate?` is retained as an `Option` of an *ordered pair*, so `none`, `some` and the
  first/second order are all preserved.

## Total virtual-ledger references

`VirtualTorsionPointLedger.Valid` is only `(keys ledger).Nodup` (`P94MoleculeCoordinateTorsion`,
line 47).  It says nothing about atom numbers, so an authority observation satisfying `ValidFor`
may legally carry unused or out-of-range virtual entries.  Requiring a global atom bound would
therefore silently strengthen the original predicate.

Instead the certificate codec uses a *total* reference carrier:

* a virtual participant whose owner is a physical source atom (`owner < source.atomCount`) is
  transported natively through the common enumeration `e` to `V`;
* any other virtual participant keeps its exact source `Nat` owner, its virtual kind, and the
  proof that it is not a physical source atom.  Such an entry is retained source metadata, never
  treated as a physical atom;
* every virtual point keeps its exact rational coordinate, and the ledger keeps its exact list
  order and multiplicity.

Decoding maps native references back through the same enumeration and returns unresolved source
references unchanged.  Hence every ledger is recovered exactly, including unused out-of-range
entries.  The bridgehead and the selected directed participant of each certificate *are* physical
atoms, and their `V`-native form is derived from the actual authority premises (the concrete
certificate's direction judgments contain `InOutParticipantChemicallyValid`).

## Derived bounds

Torsion frame/candidate bounds are derived from `unit.ValidFor` and `MolecularRolesValid` via the
approved `rawBounded_torsion_of_validFor_of_roles`.  The two `P94InOutEvidence` bridge sites are
derived from the certificate equalities and direction judgments.  The seven remaining evidence
constructors need no extra atom bounds.

No assumption is made that policy satisfaction is invariant under an arbitrary permutation of
atom numbers: every recovery theorem is at the same `e`, policy and source, and returns the
original fields.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoP94AuthorityObservationIngress

open BlueBookP94
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.CoordinateTorsion
open BlueBookP94.P94MolecularBicyclicFramework
open BlueBookP94.P94MolecularBridgeSufficiency
open OrganicStereoOrderedObservationFamily
open OrganicStereoP94CompleteEvidenceIngress

variable {source : CertifiedAuthoritativeChemicalInput}
variable {policy : P94AuthorityPolicy}
variable {V W : Type*}
variable {State Framework : Type*}

/-! ## The evidence ingress witness -/

/-- Ingress condition for one evidence record: the record's own unit validity plus the exact
`RawBounded` facts consumed by the approved nine-constructor codec.  `RawBounded` is `True` for
the seven constructors whose only atom references are the unit's. -/
def EvidenceEncodable (source : CertifiedAuthoritativeChemicalInput) (molecule : RawMolecule)
    (converted : molecule.toSemanticMolecule? = some source.input.molecule)
    (record : P94ConformationEvidence State Framework) : Prop :=
  record.unit.ValidFor molecule ∧
    RawBounded (⟨molecule, converted⟩ : RawSourceTie source) record

/-! ## Bounded certificate codec (specialization retained from the approved family adapter) -/

/-- Source-side ingress condition for one exact coordinate observation with a globally bounded
virtual ledger.  This is the stronger specialization retained for callers that already have the
virtual atom bounds; the authority representation itself uses the total codec below. -/
def CoordinateObservationEncodable (source : CertifiedAuthoritativeChemicalInput)
    (observation : CoordinateInOutObservation Framework) : Prop :=
  observation.bridgehead < source.input.molecule.atomCount ∧
    P94ConformationUnit.ParticipantBounded observation.directedParticipant
      source.input.molecule.atomCount ∧
    (∀ point ∈ observation.virtualPoints,
      VirtualParticipantBounded point.participant source.input.molecule.atomCount)

/-- Ingress condition for the optional ordered certificate pair in the bounded specialization.
`none` needs nothing; `some` keeps both observations and their order. -/
def CertificateEncodable (source : CertifiedAuthoritativeChemicalInput) :
    Option (CoordinateInOutObservation Framework ×
      CoordinateInOutObservation Framework) → Prop
  | none => True
  | some (first, second) =>
      CoordinateObservationEncodable source first ∧
        CoordinateObservationEncodable source second

/-- The explicit source context needed by the bounded specialization: virtual-ledger entries are
physical source atoms.  It is *not* a consequence of `ValidFor` and is not used by the authority
representation below. -/
def VirtualCertificateSourceAnchored (source : CertifiedAuthoritativeChemicalInput) :
    Option (CoordinateInOutObservation Framework ×
      CoordinateInOutObservation Framework) → Prop
  | none => True
  | some (first, second) =>
      (∀ point ∈ first.virtualPoints,
        VirtualParticipantBounded point.participant source.input.molecule.atomCount) ∧
      (∀ point ∈ second.virtualPoints,
        VirtualParticipantBounded point.participant source.input.molecule.atomCount)

/-- Encode the optional ordered certificate pair with the bounded virtual codec. -/
def encodeCertificate (e : SourceAtomIndex source ≃ V) :
    (certificate : Option (CoordinateInOutObservation Framework ×
      CoordinateInOutObservation Framework)) →
      CertificateEncodable source certificate →
        Option (EncodedCoordinateObservation Framework V ×
          EncodedCoordinateObservation Framework V)
  | none, _ => none
  | some (first, second), witness =>
      some (EncodedCoordinateObservation.ofSource e first
          witness.1.1 witness.1.2.1 witness.1.2.2,
        EncodedCoordinateObservation.ofSource e second
          witness.2.1 witness.2.2.1 witness.2.2.2)

/-- Decode the optional ordered bounded certificate pair. -/
def decodeCertificate (e : SourceAtomIndex source ≃ V) :
    Option (EncodedCoordinateObservation Framework V ×
      EncodedCoordinateObservation Framework V) →
      Option (CoordinateInOutObservation Framework ×
        CoordinateInOutObservation Framework)
  | none => none
  | some (first, second) => some (first.toSource e, second.toSource e)

/-- Exact recovery of the optional ordered certificate pair in the bounded specialization. -/
@[simp] theorem decodeCertificate_encodeCertificate (e : SourceAtomIndex source ≃ V) :
    ∀ (certificate : Option (CoordinateInOutObservation Framework ×
        CoordinateInOutObservation Framework))
      (witness : CertificateEncodable source certificate),
      decodeCertificate e (encodeCertificate e certificate witness) = certificate
  | none, _ => rfl
  | some (first, second), witness => by
      simp [encodeCertificate, decodeCertificate,
        EncodedCoordinateObservation.toSource_ofSource]

/-- Presence of a bounded certificate is preserved exactly by the codec. -/
@[simp] theorem decodeCertificate_isSome (e : SourceAtomIndex source ≃ V)
    (certificate : Option (EncodedCoordinateObservation Framework V ×
      EncodedCoordinateObservation Framework V)) :
    (decodeCertificate e certificate).isSome = certificate.isSome := by
  cases certificate with
  | none => rfl
  | some pair =>
      rcases pair with ⟨first, second⟩
      rfl

/-- Absence on the bounded encoded side is exactly absence on the source side. -/
@[simp] theorem decodeCertificate_eq_none_iff (e : SourceAtomIndex source ≃ V)
    (certificate : Option (EncodedCoordinateObservation Framework V ×
      EncodedCoordinateObservation Framework V)) :
    decodeCertificate e certificate = none ↔ certificate = none := by
  cases certificate with
  | none => simp [decodeCertificate]
  | some pair =>
      rcases pair with ⟨first, second⟩
      simp [decodeCertificate]

/-! ## Total virtual-ledger reference carrier

The owner of a primitive virtual participant is the atom number carried by its constructor.
Physical source atoms are transported natively; all other entries keep their exact source
reference and the proof that they lie outside the physical atom range. -/

/-- One total virtual participant reference.  `native` is a `V`-indexed physical atom; the source
enumeration is recovered through `e`.  `unresolved` keeps the exact source participant and the
proof that it is not a physical source atom; it is never decoded through `e`. -/
inductive TotalVirtualTorsionParticipant (source : CertifiedAuthoritativeChemicalInput)
    (V : Type*) where
  | native (participant : EncodedVirtualTorsionParticipant V)
  | unresolved (participant : VirtualTorsionParticipant)
      (outOfRange : ¬ VirtualParticipantBounded participant
        source.input.molecule.atomCount)

/-- Encode one virtual participant totally: native below the source atom count, unresolved
otherwise.  The match keeps the participant kind (`lonePair` versus `duplicateAtom`) separate
from the owner number, so two different keys with the same owner remain distinct. -/
def encodeTotalVirtualParticipant (e : SourceAtomIndex source ≃ V) :
    VirtualTorsionParticipant → TotalVirtualTorsionParticipant source V
  | .lonePair center =>
      if bounded : center < source.input.molecule.atomCount then
        .native (.lonePair (encodeIndex e center bounded))
      else
        .unresolved (.lonePair center) bounded
  | .duplicateAtom original =>
      if bounded : original < source.input.molecule.atomCount then
        .native (.duplicateAtom (encodeIndex e original bounded))
      else
        .unresolved (.duplicateAtom original) bounded

/-- Decode one total virtual participant. -/
def decodeTotalVirtualParticipant (e : SourceAtomIndex source ≃ V) :
    TotalVirtualTorsionParticipant source V → VirtualTorsionParticipant
  | .native participant => decodeVirtualParticipant e participant
  | .unresolved participant _ => participant

/-- Every virtual participant is recovered exactly, both native and unresolved, and with its
kind preserved. -/
@[simp] theorem decodeTotalVirtualParticipant_encodeTotalVirtualParticipant
    (e : SourceAtomIndex source ≃ V) (participant : VirtualTorsionParticipant) :
    decodeTotalVirtualParticipant e (encodeTotalVirtualParticipant e participant) =
      participant := by
  cases participant with
  | lonePair center =>
      by_cases bounded : center < source.input.molecule.atomCount
      · simp [encodeTotalVirtualParticipant, bounded, decodeTotalVirtualParticipant,
          decodeVirtualParticipant]
      · simp [encodeTotalVirtualParticipant, bounded, decodeTotalVirtualParticipant]
  | duplicateAtom original =>
      by_cases bounded : original < source.input.molecule.atomCount
      · simp [encodeTotalVirtualParticipant, bounded, decodeTotalVirtualParticipant,
          decodeVirtualParticipant]
      · simp [encodeTotalVirtualParticipant, bounded, decodeTotalVirtualParticipant]

/-- The key codec is injective: the participant kind and owner together determine the encoded
reference, and decoding is a left inverse. -/
theorem encodeTotalVirtualParticipant_injective (e : SourceAtomIndex source ≃ V) :
    Function.Injective (encodeTotalVirtualParticipant (source := source) e) := by
  intro first second equal
  have decoded := congrArg (decodeTotalVirtualParticipant e) equal
  simpa using decoded

/-- One total virtual point: the exact rational point is retained, only the atom reference is
resolved or explicitly left as source metadata. -/
structure TotalVirtualTorsionPoint (source : CertifiedAuthoritativeChemicalInput)
    (V : Type*) where
  participant : TotalVirtualTorsionParticipant source V
  point : CartesianPoint3

/-- Encode one virtual point totally. -/
def encodeTotalVirtualPoint (e : SourceAtomIndex source ≃ V)
    (point : VirtualTorsionPoint) : TotalVirtualTorsionPoint source V where
  participant := encodeTotalVirtualParticipant e point.participant
  point := point.point

/-- Decode one total virtual point. -/
def decodeTotalVirtualPoint (e : SourceAtomIndex source ≃ V) :
    TotalVirtualTorsionPoint source V → VirtualTorsionPoint
  | ⟨participant, point⟩ => ⟨decodeTotalVirtualParticipant e participant, point⟩

/-- Every virtual point is recovered exactly, including its coordinate. -/
@[simp] theorem decodeTotalVirtualPoint_encodeTotalVirtualPoint
    (e : SourceAtomIndex source ≃ V) (point : VirtualTorsionPoint) :
    decodeTotalVirtualPoint e (encodeTotalVirtualPoint e point) = point := by
  cases point with
  | mk participant point =>
      simp [encodeTotalVirtualPoint, decodeTotalVirtualPoint]

/-- Point encoding is injective: the key and the exact coordinate are both preserved. -/
theorem encodeTotalVirtualPoint_injective (e : SourceAtomIndex source ≃ V) :
    Function.Injective (encodeTotalVirtualPoint (source := source) e) := by
  intro first second equal
  have decoded := congrArg (decodeTotalVirtualPoint e) equal
  simpa using decoded

/-- Encode an ordered virtual-point ledger totally.  List order and multiplicity are retained. -/
def encodeTotalVirtualPoints (e : SourceAtomIndex source ≃ V)
    (points : List VirtualTorsionPoint) : List (TotalVirtualTorsionPoint source V) :=
  points.map (encodeTotalVirtualPoint e)

/-- Decode an ordered total virtual-point ledger. -/
def decodeTotalVirtualPoints (e : SourceAtomIndex source ≃ V)
    (points : List (TotalVirtualTorsionPoint source V)) : List VirtualTorsionPoint :=
  points.map (decodeTotalVirtualPoint e)

/-- Exact ledger recovery: order, multiplicity, unresolved entries and coordinates all return
unchanged. -/
@[simp] theorem decodeTotalVirtualPoints_encodeTotalVirtualPoints
    (e : SourceAtomIndex source ≃ V) (points : List VirtualTorsionPoint) :
    decodeTotalVirtualPoints e (encodeTotalVirtualPoints e points) = points := by
  simp [decodeTotalVirtualPoints, encodeTotalVirtualPoints, Function.comp_def]

/-- The key list of a total ledger: the ordered participant references, including unresolved
source references. -/
def totalVirtualPointKeys (points : List (TotalVirtualTorsionPoint source V)) :
    List (TotalVirtualTorsionParticipant source V) :=
  points.map TotalVirtualTorsionPoint.participant

/-- The encoded key list is exactly the image of the source key list under the participant
codec; the participant kind is retained in the encoded key, so `lonePair` and `duplicateAtom`
entries with the same owner remain distinct. -/
@[simp] theorem totalVirtualPointKeys_encodeTotalVirtualPoints
    (e : SourceAtomIndex source ≃ V) (points : List VirtualTorsionPoint) :
    totalVirtualPointKeys (encodeTotalVirtualPoints e points) =
      (VirtualTorsionPointLedger.keys points).map
        (encodeTotalVirtualParticipant e) := by
  induction points with
  | nil => rfl
  | cons head tail ih =>
      simp [totalVirtualPointKeys, encodeTotalVirtualPoints, encodeTotalVirtualPoint,
        VirtualTorsionPointLedger.keys]

/-- Key-codec injectivity preserves `Nodup`, including the keys of unused and unresolved
entries. -/
theorem encodeTotalVirtualPoints_nodup (e : SourceAtomIndex source ≃ V)
    (points : List VirtualTorsionPoint)
    (nodup : (VirtualTorsionPointLedger.keys points).Nodup) :
    (totalVirtualPointKeys (encodeTotalVirtualPoints e points)).Nodup := by
  rw [totalVirtualPointKeys_encodeTotalVirtualPoints]
  exact nodup.map (encodeTotalVirtualParticipant_injective e)

/-- `Nodup` is preserved in both directions: the total key codec is injective on participant
kind and owner, so a ledger is duplicate-free exactly when its encoding is. -/
theorem encodeTotalVirtualPoints_nodup_iff (e : SourceAtomIndex source ≃ V)
    (points : List VirtualTorsionPoint) :
    (totalVirtualPointKeys (encodeTotalVirtualPoints e points)).Nodup ↔
      (VirtualTorsionPointLedger.keys points).Nodup := by
  rw [totalVirtualPointKeys_encodeTotalVirtualPoints]
  exact List.nodup_map_iff (encodeTotalVirtualParticipant_injective e)

/-- First-match lookup on the total encoded ledger, keyed by the *source* participant.  The
predicate is the decoded participant, so unresolved entries participate under their exact source
key, not as molecular atoms. -/
def lookupTotalVirtualPoints (e : SourceAtomIndex source ≃ V)
    (points : List (TotalVirtualTorsionPoint source V))
    (participant : VirtualTorsionParticipant) : Option CartesianPoint3 :=
  match points with
  | [] => none
  | entry :: rest =>
      if decodeTotalVirtualParticipant e entry.participant = participant then
        some entry.point
      else
        lookupTotalVirtualPoints e rest participant

/-- First-match lookup is preserved exactly: scanning the total encoded ledger for a source
participant returns the same coordinate as scanning the decoded source ledger, for every source
key, native or unresolved. -/
theorem lookupTotalVirtualPoints_decode (e : SourceAtomIndex source ≃ V)
    (points : List (TotalVirtualTorsionPoint source V))
    (participant : VirtualTorsionParticipant) :
    VirtualTorsionPointLedger.lookup (decodeTotalVirtualPoints e points) participant =
      lookupTotalVirtualPoints e points participant := by
  induction points with
  | nil => rfl
  | cons entry rest ih =>
      simp only [decodeTotalVirtualPoints, List.map_cons,
        VirtualTorsionPointLedger.lookup, lookupTotalVirtualPoints,
        decodeTotalVirtualPoint]
      by_cases found : decodeTotalVirtualParticipant e entry.participant = participant
      · simp [found]
      · simpa [found, decodeTotalVirtualPoints] using ih

/-! ## Total coordinate observations -/

/-- One exact coordinate observation with total virtual-ledger references.  Everything except the
atom references is retained verbatim. -/
structure TotalEncodedCoordinateObservation (source : CertifiedAuthoritativeChemicalInput)
    (Framework : Type*) (V : Type*) where
  framework : Framework
  spatial : SpatialConfiguration
  virtualPoints : List (TotalVirtualTorsionPoint source V)
  bridgehead : V
  directedParticipant : TorsionParticipant V
  interior : CartesianPoint3

namespace TotalEncodedCoordinateObservation

variable (e : SourceAtomIndex source ≃ V)

/-- Adapt one actual coordinate observation.  Only the bridgehead and the selected directed
participant need physical atom bounds; the virtual ledger is handled totally. -/
def ofSource (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount) :
    TotalEncodedCoordinateObservation source Framework V where
  framework := observation.framework
  spatial := observation.spatial
  virtualPoints := encodeTotalVirtualPoints e observation.virtualPoints
  bridgehead := encodeIndex e observation.bridgehead bridgeheadBound
  directedParticipant := encodeParticipant e observation.directedParticipant participantBound
  interior := observation.interior

/-- Decode one total coordinate observation. -/
def toSource (observation : TotalEncodedCoordinateObservation source Framework V) :
    CoordinateInOutObservation Framework where
  framework := observation.framework
  spatial := observation.spatial
  virtualPoints := decodeTotalVirtualPoints e observation.virtualPoints
  bridgehead := decodeIndex e observation.bridgehead
  directedParticipant := decodeParticipant e observation.directedParticipant
  interior := observation.interior

/-- Exact recovery of one coordinate observation from the total codec, with no virtual atom bound
hypothesis. -/
@[simp] theorem toSource_ofSource (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount) :
    toSource e (ofSource e observation bridgeheadBound participantBound) = observation := by
  cases observation with
  | mk framework spatial virtualPoints bridgehead participant interior =>
      simp [toSource, ofSource, decodeParticipant_encodeParticipant,
        decodeTotalVirtualPoints_encodeTotalVirtualPoints]

/-- The decoded virtual ledger is exactly the original ledger.  This is the field-level form of
"first-match lookup semantics are preserved": `VirtualTorsionPointLedger.lookup` scans this list
in order, and the list is unchanged. -/
@[simp] theorem virtualPoints_toSource_ofSource
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount) :
    (toSource e (ofSource e observation bridgeheadBound participantBound)).virtualPoints =
      observation.virtualPoints := by
  simp [toSource, ofSource, decodeTotalVirtualPoints_encodeTotalVirtualPoints]

/-- First-match virtual lookup of the decoded certificate is exactly first-match lookup of the
original ledger.  The total codec neither reorders nor deduplicates entries. -/
theorem lookup_virtualPoints_toSource_ofSource
    (observation : CoordinateInOutObservation Framework)
    (bridgeheadBound : observation.bridgehead < source.input.molecule.atomCount)
    (participantBound : P94ConformationUnit.ParticipantBounded
      observation.directedParticipant source.input.molecule.atomCount)
    (participant : VirtualTorsionParticipant) :
    VirtualTorsionPointLedger.lookup
        (toSource e (ofSource e observation bridgeheadBound participantBound)).virtualPoints
        participant =
      VirtualTorsionPointLedger.lookup observation.virtualPoints participant := by
  rw [virtualPoints_toSource_ofSource]

end TotalEncodedCoordinateObservation

/-! ## Total certificate pair codec -/

/-- Ingress condition for the optional ordered certificate pair under the total codec.  It
contains exactly the physical atom bounds that `ValidFor` provides for the bridgehead and the
selected directed participant of each certificate; no virtual-ledger premise occurs. -/
def TotalCertificateEncodable (source : CertifiedAuthoritativeChemicalInput) :
    Option (CoordinateInOutObservation Framework ×
      CoordinateInOutObservation Framework) → Prop
  | none => True
  | some (first, second) =>
      first.bridgehead < source.input.molecule.atomCount ∧
      P94ConformationUnit.ParticipantBounded first.directedParticipant
        source.input.molecule.atomCount ∧
      second.bridgehead < source.input.molecule.atomCount ∧
      P94ConformationUnit.ParticipantBounded second.directedParticipant
        source.input.molecule.atomCount

/-- Encode the optional ordered certificate pair with the total virtual codec. -/
def encodeTotalCertificate (e : SourceAtomIndex source ≃ V) :
    (certificate : Option (CoordinateInOutObservation Framework ×
      CoordinateInOutObservation Framework)) →
      TotalCertificateEncodable source certificate →
        Option (TotalEncodedCoordinateObservation source Framework V ×
          TotalEncodedCoordinateObservation source Framework V)
  | none, _ => none
  | some (first, second), witness =>
      some (TotalEncodedCoordinateObservation.ofSource e first witness.1 witness.2.1,
        TotalEncodedCoordinateObservation.ofSource e second witness.2.2.1 witness.2.2.2)

/-- Decode the optional ordered certificate pair with the total virtual codec. -/
def decodeTotalCertificate (e : SourceAtomIndex source ≃ V) :
    Option (TotalEncodedCoordinateObservation source Framework V ×
      TotalEncodedCoordinateObservation source Framework V) →
      Option (CoordinateInOutObservation Framework ×
        CoordinateInOutObservation Framework)
  | none => none
  | some (first, second) => some (first.toSource e, second.toSource e)

/-- Exact recovery of the optional ordered certificate pair, including `none`/`some`, both
observations, their order and every virtual-ledger entry. -/
@[simp] theorem decodeTotalCertificate_encodeTotalCertificate
    (e : SourceAtomIndex source ≃ V) :
    ∀ (certificate : Option (CoordinateInOutObservation Framework ×
        CoordinateInOutObservation Framework))
      (witness : TotalCertificateEncodable source certificate),
      decodeTotalCertificate e (encodeTotalCertificate e certificate witness) =
        certificate
  | none, _ => rfl
  | some (first, second), witness => by
      simp [encodeTotalCertificate, decodeTotalCertificate,
        TotalEncodedCoordinateObservation.toSource_ofSource]

/-- Presence is preserved exactly by the total certificate codec. -/
@[simp] theorem decodeTotalCertificate_isSome (e : SourceAtomIndex source ≃ V)
    (certificate : Option (TotalEncodedCoordinateObservation source Framework V ×
      TotalEncodedCoordinateObservation source Framework V)) :
    (decodeTotalCertificate e certificate).isSome = certificate.isSome := by
  cases certificate with
  | none => rfl
  | some pair =>
      rcases pair with ⟨first, second⟩
      rfl

/-- Absence on the encoded side is exactly absence on the source side. -/
@[simp] theorem decodeTotalCertificate_eq_none_iff (e : SourceAtomIndex source ≃ V)
    (certificate : Option (TotalEncodedCoordinateObservation source Framework V ×
      TotalEncodedCoordinateObservation source Framework V)) :
    decodeTotalCertificate e certificate = none ↔ certificate = none := by
  cases certificate with
  | none => simp [decodeTotalCertificate]
  | some pair =>
      rcases pair with ⟨first, second⟩
      simp [decodeTotalCertificate]

/-! ## The encoded authority observation -/

/-- Exact encoded counterpart of `P94AuthorityObservation policy`: the molecule is retained
verbatim with its exact conversion to the certified source, the evidence is the approved
nine-constructor native payload, the claim stays typed, and the optional coordinate certificate
stays an ordered pair over the total virtual codec. -/
structure EncodedP94AuthorityObservation (policy : P94AuthorityPolicy)
    (source : CertifiedAuthoritativeChemicalInput) (V : Type*) where
  molecule : RawMolecule
  converted : molecule.toSemanticMolecule? = some source.input.molecule
  evidence : EncodedConformationEvidence V Nat ThetaFramework
  claim : P94AuthorityClaim
  inOutCertificate? : Option
    (TotalEncodedCoordinateObservation source ThetaFramework V ×
      TotalEncodedCoordinateObservation source ThetaFramework V) := none

namespace EncodedP94AuthorityObservation

/-- The actual source graph tie carried by the encoded observation. -/
def tie (enc : EncodedP94AuthorityObservation policy source V) : RawSourceTie source :=
  ⟨enc.molecule, enc.converted⟩

@[simp] theorem tie_molecule (enc : EncodedP94AuthorityObservation policy source V) :
    enc.tie.molecule = enc.molecule := rfl

/-- Decode an encoded authority observation back to the actual authority type.  Each field is
read from the encoding; no original whole observation is consulted. -/
def toAuthority (e : SourceAtomIndex source ≃ V)
    (enc : EncodedP94AuthorityObservation policy source V) :
    P94AuthorityObservation policy where
  molecule := enc.molecule
  evidence := toSource e enc.evidence
  claim := enc.claim
  inOutCertificate? := decodeTotalCertificate e enc.inOutCertificate?

@[simp] theorem toAuthority_molecule (e : SourceAtomIndex source ≃ V)
    (enc : EncodedP94AuthorityObservation policy source V) :
    (toAuthority e enc).molecule = enc.molecule := rfl

@[simp] theorem toAuthority_evidence (e : SourceAtomIndex source ≃ V)
    (enc : EncodedP94AuthorityObservation policy source V) :
    (toAuthority e enc).evidence =
      toSource e enc.evidence := rfl

@[simp] theorem toAuthority_claim (e : SourceAtomIndex source ≃ V)
    (enc : EncodedP94AuthorityObservation policy source V) :
    (toAuthority e enc).claim = enc.claim := rfl

@[simp] theorem toAuthority_inOutCertificate? (e : SourceAtomIndex source ≃ V)
    (enc : EncodedP94AuthorityObservation policy source V) :
    (toAuthority e enc).inOutCertificate? =
      decodeTotalCertificate e enc.inOutCertificate? := rfl

/-- Encode an actual authority observation, given the explicit evidence witness and the physical
bridgehead/participant bounds of the optional certificate pair. -/
def ofAuthority (e : SourceAtomIndex source ≃ V)
    (observation : P94AuthorityObservation policy)
    (converted : observation.molecule.toSemanticMolecule? = some source.input.molecule)
    (evidenceWitness : EvidenceEncodable source observation.molecule converted
      observation.evidence)
    (certificateWitness : TotalCertificateEncodable source observation.inOutCertificate?) :
    EncodedP94AuthorityObservation policy source V where
  molecule := observation.molecule
  converted := converted
  evidence := ofSource e ⟨observation.molecule, converted⟩
    observation.evidence evidenceWitness.1 evidenceWitness.2
  claim := observation.claim
  inOutCertificate? := encodeTotalCertificate e observation.inOutCertificate? certificateWitness

/-- Full recovery of the preexisting authority observation: decoding the encoded fields returns
the original molecule, evidence, typed claim and optional ordered certificate (with every virtual
entry), at the same enumeration `e`. -/
@[simp] theorem toAuthority_ofAuthority (e : SourceAtomIndex source ≃ V)
    (observation : P94AuthorityObservation policy)
    (converted : observation.molecule.toSemanticMolecule? = some source.input.molecule)
    (evidenceWitness : EvidenceEncodable source observation.molecule converted
      observation.evidence)
    (certificateWitness : TotalCertificateEncodable source observation.inOutCertificate?) :
    (ofAuthority e observation converted evidenceWitness certificateWitness).toAuthority e =
      observation := by
  cases evidenceWitness with
  | intro valid bounded =>
      cases observation with
      | mk molecule evidence claim certificate =>
          simp [ofAuthority, toAuthority,
            toSource_ofSource]

end EncodedP94AuthorityObservation

/-! ## Bounds derived from the actual authority validity premises -/

/-- A valid torsion conformation unit that carries selected participants has `torsionAxis` kind:
every other kind's `ValidFor` branch forces the participant option to be `none`. -/
theorem torsionAxisKind_of_valid {molecule : RawMolecule} {unit : P94ConformationUnit}
    (valid : unit.ValidFor molecule)
    {front rear : TorsionParticipant ℕ}
    (observed : unit.torsionParticipants? = some (front, rear)) :
    unit.kind = .torsionAxis := by
  cases unit with
  | mk kind atoms participants? =>
      cases kind <;> simp only [P94ConformationUnit.ValidFor] at valid observed
      · simp_all
      · rfl
      all_goals simp_all

/-- Every chemically admitted in/out directed participant lies inside the molecule atom range,
and so does the bridgehead it is attached to.  A `duplicateAtom` directed participant is refused
by `InOutParticipantChemicallyValid`, so no bound is invented for it. -/
theorem inOutParticipantChemicallyValid_bounds {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : Framework) (bridgehead : ℕ)
    (participant : TorsionParticipant ℕ)
    (valid : InOutParticipantChemicallyValid premises molecule unit framework bridgehead
      participant) :
    bridgehead < molecule.atomCount ∧
      P94ConformationUnit.ParticipantBounded participant molecule.atomCount := by
  cases participant with
  | atom atom => exact ⟨valid.2.2.1, valid.2.2.2.1⟩
  | lonePair center =>
      exact ⟨valid.2.2.1, by
        simpa [P94ConformationUnit.ParticipantBounded, valid.2.2.2.1] using valid.2.2.1⟩
  | duplicateAtom original => exact False.elim valid

/-- The direction judgment of one exact coordinate observation yields its bridgehead and
selected directed-participant atom bounds.  This is the premise the authority certificate links
give to the evidence record. -/
theorem directionJudgment_bounds {Framework : Type*}
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) (observation : CoordinateInOutObservation Framework)
    (direction : BridgeheadDirection)
    (judgment : CoordinateInOutDirectionJudgment premises molecule unit observation direction) :
    observation.bridgehead < molecule.atomCount ∧
      P94ConformationUnit.ParticipantBounded observation.directedParticipant
        molecule.atomCount :=
  inOutParticipantChemicallyValid_bounds premises molecule unit observation.framework
    observation.bridgehead observation.directedParticipant judgment.2.2.1

namespace EncodedP94AuthorityObservation

/-- Every `RawBounded` fact needed by the approved evidence codec follows from the actual
authority validity predicate.  Torsion is derived from `ValidFor`/`MolecularRolesValid`; the two
in/out bridge sites are derived from the concrete certificate's direction judgments and their
exact field equalities.  The seven remaining constructors need nothing extra. -/
theorem rawBounded_of_validFor
    (observation : P94AuthorityObservation policy)
    (converted : observation.molecule.toSemanticMolecule? = some source.input.molecule)
    (valid : observation.ValidFor policy source.input) :
    RawBounded (⟨observation.molecule, converted⟩ : RawSourceTie source)
      observation.evidence := by
  cases observation with
  | mk molecule evidence claim certificate =>
      simp only [P94AuthorityObservation.ValidFor] at valid
      obtain ⟨_agreement, _observed, unitValid, roles, _claimMatch, _supports,
        certificateMatches⟩ := valid
      cases evidence with
      | conformer record => trivial
      | torsion record =>
          have rolesCopy := roles
          obtain ⟨_candidateBounds, front, rear, _axisFront, _axisRear, participantsEq,
            frameFrontEq, frameRearEq, _endpoints, _frontAttached, _rearAttached⟩ := roles
          have observedPair : record.unit.torsionParticipants? =
              some (record.frame.front, record.frame.rear) := by
            rw [frameFrontEq, frameRearEq]
            exact participantsEq
          have kindEq := torsionAxisKind_of_valid unitValid observedPair
          exact rawBounded_torsion_of_validFor_of_roles (State := Nat)
            (Framework := ThetaFramework) ⟨molecule, converted⟩ record kindEq unitValid
            rolesCopy
      | eclipsedStaggered record => trivial
      | trigonal record => trivial
      | conjugated record => trivial
      | ringPlane record => trivial
      | twist record => trivial
      | halfChair record => trivial
      | inOut record =>
          obtain ⟨firstCoordinate, secondCoordinate, _certificateEq, _pairObserved,
            _firstLength, _secondLength, _firstFramework, _secondFramework,
            firstBridgeheadEq, secondBridgeheadEq, firstParticipantEq, secondParticipantEq,
            _firstFrameworkValid, _secondFrameworkValid, firstDirection, secondDirection,
            _bicyclicFact, _firstBridgeFact, _secondBridgeFact⟩ := certificateMatches
          have firstBounds := directionJudgment_bounds
            (bridgeDerivedPremises (policy.inOutBasePremises source.input molecule))
            molecule record.unit firstCoordinate record.first.direction firstDirection
          have secondBounds := directionJudgment_bounds
            (bridgeDerivedPremises (policy.inOutBasePremises source.input molecule))
            molecule record.unit secondCoordinate record.second.direction secondDirection
          exact ⟨by rw [← firstBridgeheadEq]; exact firstBounds.1,
            by rw [← firstParticipantEq]; exact firstBounds.2,
            by rw [← secondBridgeheadEq]; exact secondBounds.1,
            by rw [← secondParticipantEq]; exact secondBounds.2⟩

/-- The total certificate ingress witness follows from authority validity alone: for non-`inOut`
evidence the validity predicate forces `none`; for `inOut` evidence it provides the ordered pair,
and both direction judgments give the bridgehead and selected directed-participant bounds.  No
virtual-ledger bound is required. -/
theorem totalCertificateEncodable_of_validFor
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy source.input) :
    TotalCertificateEncodable source observation.inOutCertificate? := by
  cases observation with
  | mk molecule evidence claim certificate =>
      simp only [P94AuthorityObservation.ValidFor] at valid
      obtain ⟨agreement, _observed, _unitValid, _roles, _claimMatch, _supports,
        certificateMatches⟩ := valid
      cases evidence with
      | inOut record =>
          obtain ⟨firstCoordinate, secondCoordinate, certificateEq, _pairObserved,
            _firstLength, _secondLength, _firstFramework, _secondFramework,
            _firstBridgeheadEq, _secondBridgeheadEq, _firstParticipantEq, _secondParticipantEq,
            _firstFrameworkValid, _secondFrameworkValid, firstDirection, secondDirection,
            _bicyclicFact, _firstBridgeFact, _secondBridgeFact⟩ := certificateMatches
          have firstBounds := directionJudgment_bounds
            (bridgeDerivedPremises (policy.inOutBasePremises source.input molecule))
            molecule record.unit firstCoordinate record.first.direction firstDirection
          have secondBounds := directionJudgment_bounds
            (bridgeDerivedPremises (policy.inOutBasePremises source.input molecule))
            molecule record.unit secondCoordinate record.second.direction secondDirection
          let tie : RawSourceTie source := ⟨molecule, agreement.1⟩
          rw [certificateEq]
          exact ⟨tie.atom_bound firstBounds.1, tie.participantBounded firstBounds.2,
            tie.atom_bound secondBounds.1, tie.participantBounded secondBounds.2⟩
      | conformer record =>
          rw [certificateMatches]
          exact True.intro
      | torsion record =>
          rw [certificateMatches]
          exact True.intro
      | eclipsedStaggered record =>
          rw [certificateMatches]
          exact True.intro
      | trigonal record =>
          rw [certificateMatches]
          exact True.intro
      | conjugated record =>
          rw [certificateMatches]
          exact True.intro
      | ringPlane record =>
          rw [certificateMatches]
          exact True.intro
      | twist record =>
          rw [certificateMatches]
          exact True.intro
      | halfChair record =>
          rw [certificateMatches]
          exact True.intro

/-! ## Validity at the same policy and source, from `ValidFor` alone -/

/-- Encode a valid authority observation.  The evidence witness and the total certificate witness
are both derived from the actual validity predicate; there is no extra representability
hypothesis. -/
def ofAuthorityValid (e : SourceAtomIndex source ≃ V)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy source.input) :
    EncodedP94AuthorityObservation policy source V :=
  ofAuthority e observation valid.1.1
    ⟨valid.2.2.1, rawBounded_of_validFor observation valid.1.1 valid⟩
    (totalCertificateEncodable_of_validFor observation valid)

/-- Recovery for a valid authority observation, from `ValidFor` alone. -/
@[simp] theorem toAuthority_ofAuthorityValid (e : SourceAtomIndex source ≃ V)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy source.input) :
    (ofAuthorityValid e observation valid).toAuthority e = observation := by
  unfold ofAuthorityValid
  exact toAuthority_ofAuthority e observation valid.1.1 _ _

/-- The recovered source satisfies exactly the same validity statement, at the same policy and
the same source.  No invariance under an arbitrary permutation of atom numbers is used or
claimed: the evidence, molecule and certificate returned by the decoder are the original ones. -/
theorem ofAuthorityValid_validFor_iff (e : SourceAtomIndex source ≃ V)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy source.input) :
    ((ofAuthorityValid e observation valid).toAuthority e).ValidFor policy source.input ↔
      observation.ValidFor policy source.input := by
  rw [toAuthority_ofAuthorityValid]

/-- The recovered source satisfies exactly the same provision-specific authority statement, at
the same policy, source and manifest provision. -/
theorem ofAuthorityValid_validForProvision_iff (e : SourceAtomIndex source ≃ V)
    (observation : P94AuthorityObservation policy)
    (valid : observation.ValidFor policy source.input)
    (provision : IUPACNormativeProvision) :
    ((ofAuthorityValid e observation valid).toAuthority e).ValidForProvision
        policy provision source.input ↔
      observation.ValidForProvision policy provision source.input := by
  rw [toAuthority_ofAuthorityValid]

end EncodedP94AuthorityObservation

/-! ## Explicit `None` versus `Some` distinctions -/

/-- A non-`inOut` evidence record that satisfies the certificate match has no certificate. -/
theorem certificate_eq_none_of_matches_of_not_inOut
    (policy : P94AuthorityPolicy) (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule) (evidence : P94ConformationEvidence Nat ThetaFramework)
    (certificate : Option (CoordinateInOutObservation ThetaFramework ×
      CoordinateInOutObservation ThetaFramework))
    (notInOut : ∀ record, evidence ≠ .inOut record)
    (certificateMatch : P94InOutCertificateMatches policy source molecule evidence certificate) :
    certificate = none := by
  cases evidence with
  | inOut record => exact absurd rfl (notInOut record)
  | conformer record => exact certificateMatch
  | torsion record => exact certificateMatch
  | eclipsedStaggered record => exact certificateMatch
  | trigonal record => exact certificateMatch
  | conjugated record => exact certificateMatch
  | ringPlane record => exact certificateMatch
  | twist record => exact certificateMatch
  | halfChair record => exact certificateMatch

/-- An `inOut` evidence record that satisfies the certificate match has an ordered certificate
pair.  This is the exact `some` side of the distinction preserved by the codec. -/
theorem certificate_eq_some_of_matches_of_inOut
    (policy : P94AuthorityPolicy) (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule) (record : P94InOutEvidence ThetaFramework)
    (certificate : Option (CoordinateInOutObservation ThetaFramework ×
      CoordinateInOutObservation ThetaFramework))
    (certificateMatch : P94InOutCertificateMatches policy source molecule
      (.inOut record) certificate) :
    ∃ first second, certificate = some (first, second) := by
  rcases certificateMatch with ⟨first, second, observed, _⟩
  exact ⟨first, second, observed⟩

/-! ## Correlated-set and ordered-list inverse (consuming the approved evidence codec) -/

/-- The approved codec preserves an arbitrary correlated set of evidence records: decoding the
encoded image returns exactly the original set, with no record deduplicated or dropped.  This
re-exports the correlated-set inverse at the authority ingress boundary under the same source
tie. -/
theorem evidence_correlatedSet_inverse (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source)
    (records : Set (P94ConformationEvidence State Framework))
    (valid : ∀ record ∈ records, record.unit.ValidFor tie.molecule)
    (bounded : ∀ record ∈ records, RawBounded tie record) :
    toSource e '' encodeSet e tie records valid bounded = records :=
  toSource_image_encodeSet e tie records valid bounded

/-- Ordered-list inverse: decoding the encoded list of evidence records returns the original
list, in the same order and with the same multiplicity.  This re-exports the approved list
adapter at the authority ingress boundary. -/
theorem evidence_orderedList_inverse (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source)
    (records : List (P94ConformationEvidence State Framework))
    (valid : ∀ record ∈ records, record.unit.ValidFor tie.molecule)
    (bounded : ∀ record ∈ records, RawBounded tie record) :
    (encodeList e tie records valid bounded).map (toSource e) = records :=
  toSource_map_encodeList e tie records valid bounded

end OrganicStereoP94AuthorityObservationIngress
end TetraStereo.OneCenter
