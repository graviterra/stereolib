import TetraStereo.OneCenter.OrganicStereoOrderedObservationFamily

set_option autoImplicit false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter
namespace OrganicStereoP94CompleteEvidenceIngress

open BlueBookP94
open OrganicStereoOrderedObservationFamily

/-!
# Total native ingress for the pre-existing P-94 conformation evidence inductive

`P94ConformationEvidence State Framework` (from
`CIPP94ConformationCompletePipeline`) has exactly nine constructors:

```
conformer | torsion | eclipsedStaggered | trigonal | conjugated | ringPlane |
twist | halfChair | inOut
```

`OrganicStereoOrderedObservationFamily` supplied native V-indexed payloads for four of them
(`ConformerPairObservation`, `TorsionObservation`, `TwistObservation`, `InOutObservationData`,
plus the separate coordinate in/out channel).  This module closes the remaining gap by

* reusing those four payloads verbatim, and
* adding native carriers for the five missing constructors
  (`EncodedEclipsedStaggeredObservation`, `EncodedTrigonalObservation`,
  `EncodedConjugatedObservation`, `EncodedRingPlaneObservation`,
  `EncodedHalfChairObservation`),

and bundling them into one tagged payload `EncodedConformationEvidence V State Framework`.  The
tags are exactly the nine constructors of the pre-existing inductive; `ofSource`, `toSource`,
`unit`, `RawBounded` and the round-trip proof all pattern match on all nine constructors with no
wildcard, so constructor coverage is checked by the compiler.

## What is transported

* Every explicit atom reference of a record's `P94ConformationUnit`: its ordered atom list, its
  kind, and its optional selected torsion participants.  This is the existing
  `EncodedConformationUnit` codec, reused unchanged.
* Every ordered list bound to atoms keeps its order, multiplicity and repetition: the two torsion
  candidate lists (with their `TorsionCandidate` ranking data), both twist legs, and the in/out
  sites.  Ordered lists of non-atom values (`PlaneSide` side lists, `List State` legs) are copied
  verbatim.
* Every angle, `ConjugatedSystemKind`, `StaggeredContext`, `TrigonalConformationObservation`,
  `HalfChairObservation`, `InOutObservation Framework` value, and every `Prop`-valued field is
  copied literally.  Proposition-valued data (`saturatedCyclic`, `symmetricallyEquivalent`,
  `carbohydrateFiveRing`, `bicyclicSystem`, `bridgeLongEnough`, `allLigandsIdentical`,
  `isR3CCYXGrouping`, `doubleBondBisectsRCRAngle`, `admissible`, ...) is retained as the *actual*
  proposition; nothing is substituted by `True` and no applicability proposition is claimed to
  hold.
* The opaque carriers `State` and `Framework` and every relation/predicate over them
  (`singleBondRotation`, `endpointConformationsDistinct`, `isBoatState`, `isChairState`) are copied
  verbatim.  No internal atom reference of an opaque carrier is relabelled, because none is
  exposed.

## What is *not* claimed

Nothing here decides a descriptor, classifies a geometry, or derives molecular validity.  Atom
transport consumes `record.unit.ValidFor tie.molecule`; the extra boundedness needed by the torsion
frame/candidate references and by the two in/out bridge sites is isolated in `RawBounded`.  The
torsion part of `RawBounded` is *derived* from existing `ValidFor` and `MolecularRolesValid`
(`rawBounded_torsion_of_validFor_of_roles`); the in/out site bounds are explicit hypotheses because
no existing predicate constrains those `InOutObservation` fields.  Decoding returns the original
record exactly; `Supports` and `MolecularRolesValid` are recovered through that exact equality
(`supports_toSource_ofSource`, `molecularRolesValid_toSource_ofSource`) rather than proved to hold
for arbitrary encoded payloads.
-/

variable {source : CertifiedAuthoritativeChemicalInput}
variable {V State Framework : Type*}

/-! ## Native carriers for the five constructors that had no payload

Each carrier is the exact field list of the corresponding pre-existing source record, with only
`unit : P94ConformationUnit` replaced by `unit : EncodedConformationUnit V`.  Everything else is
copied verbatim, including proposition-valued fields. -/

/-- The exact fields of `P94EclipsedStaggeredEvidence`, with the unit atom references transported
to `V`.  The retained angle and the complete `StaggeredContext` (its admissibility predicate, its
exact separation functional and its ligand-identity proposition) are copied literally. -/
structure EncodedEclipsedStaggeredObservation (V : Type*) where
  unit : EncodedConformationUnit V
  angle : TorsionAngle
  staggeredContext : StaggeredContext

namespace EncodedEclipsedStaggeredObservation

/-- Encode one actual `P94EclipsedStaggeredEvidence` record. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94EclipsedStaggeredEvidence) (valid : record.unit.ValidFor tie.molecule) :
    EncodedEclipsedStaggeredObservation V where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  angle := record.angle
  staggeredContext := record.staggeredContext

/-- Decode one eclipsed/staggered observation back to the source atom numbers. -/
def toSource (e : SourceAtomIndex source ≃ V)
    (record : EncodedEclipsedStaggeredObservation V) : P94EclipsedStaggeredEvidence where
  unit := record.unit.toUnit e
  angle := record.angle
  staggeredContext := record.staggeredContext

/-- Exact source ingress: decoding an encoded record recovers every source field. -/
@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94EclipsedStaggeredEvidence)
    (valid : record.unit.ValidFor tie.molecule) :
    toSource e (ofSource e tie record valid) = record := by
  cases record with
  | mk unit angle staggeredContext =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit]

end EncodedEclipsedStaggeredObservation

/-- The exact fields of `P94TrigonalConformationEvidence`, with the unit transported to `V`.  The
complete `TrigonalConformationObservation` keeps both applicability propositions and the exact
`xToSomeR` angle. -/
structure EncodedTrigonalObservation (V : Type*) where
  unit : EncodedConformationUnit V
  observation : TrigonalConformationObservation

namespace EncodedTrigonalObservation

/-- Encode one actual `P94TrigonalConformationEvidence` record. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94TrigonalConformationEvidence) (valid : record.unit.ValidFor tie.molecule) :
    EncodedTrigonalObservation V where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  observation := record.observation

/-- Decode one trigonal observation back to the source atom numbers. -/
def toSource (e : SourceAtomIndex source ≃ V)
    (record : EncodedTrigonalObservation V) : P94TrigonalConformationEvidence where
  unit := record.unit.toUnit e
  observation := record.observation

/-- Exact source ingress: decoding an encoded record recovers every source field. -/
@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94TrigonalConformationEvidence)
    (valid : record.unit.ValidFor tie.molecule) :
    toSource e (ofSource e tie record valid) = record := by
  cases record with
  | mk unit observation =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit]

end EncodedTrigonalObservation

/-- The exact fields of `P94ConjugatedSystemEvidence`, with the unit transported to `V`. -/
structure EncodedConjugatedObservation (V : Type*) where
  unit : EncodedConformationUnit V
  system : ConjugatedSystemKind
  angle : TorsionAngle

namespace EncodedConjugatedObservation

/-- Encode one actual `P94ConjugatedSystemEvidence` record. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94ConjugatedSystemEvidence) (valid : record.unit.ValidFor tie.molecule) :
    EncodedConjugatedObservation V where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  system := record.system
  angle := record.angle

/-- Decode one conjugated-system observation back to the source atom numbers. -/
def toSource (e : SourceAtomIndex source ≃ V)
    (record : EncodedConjugatedObservation V) : P94ConjugatedSystemEvidence where
  unit := record.unit.toUnit e
  system := record.system
  angle := record.angle

/-- Exact source ingress: decoding an encoded record recovers every source field. -/
@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94ConjugatedSystemEvidence)
    (valid : record.unit.ValidFor tie.molecule) :
    toSource e (ofSource e tie record valid) = record := by
  cases record with
  | mk unit system angle =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit]

end EncodedConjugatedObservation

/-- The exact fields of `P94RingPlaneEvidence`, with the unit transported to `V`.  The ordered
`PlaneSide` list is copied verbatim and the three proposition-valued fields are retained as the
actual source propositions (including the carbohydrate five-ring applicability flag, whose source
default is `False`). -/
structure EncodedRingPlaneObservation (V : Type*) where
  unit : EncodedConformationUnit V
  sides : List PlaneSide
  saturatedCyclic : Prop
  symmetricallyEquivalent : Prop
  /-- Explicit applicability of the carbohydrate-specific five-ring twist convention. -/
  carbohydrateFiveRing : Prop := False

namespace EncodedRingPlaneObservation

/-- Encode one actual `P94RingPlaneEvidence` record. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94RingPlaneEvidence) (valid : record.unit.ValidFor tie.molecule) :
    EncodedRingPlaneObservation V where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  sides := record.sides
  saturatedCyclic := record.saturatedCyclic
  symmetricallyEquivalent := record.symmetricallyEquivalent
  carbohydrateFiveRing := record.carbohydrateFiveRing

/-- Decode one ring-plane observation back to the source atom numbers. -/
def toSource (e : SourceAtomIndex source ≃ V)
    (record : EncodedRingPlaneObservation V) : P94RingPlaneEvidence where
  unit := record.unit.toUnit e
  sides := record.sides
  saturatedCyclic := record.saturatedCyclic
  symmetricallyEquivalent := record.symmetricallyEquivalent
  carbohydrateFiveRing := record.carbohydrateFiveRing

/-- Exact source ingress: decoding an encoded record recovers every source field, including all
three retained propositions. -/
@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94RingPlaneEvidence)
    (valid : record.unit.ValidFor tie.molecule) :
    toSource e (ofSource e tie record valid) = record := by
  cases record with
  | mk unit sides saturatedCyclic symmetricallyEquivalent carbohydrateFiveRing =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit]

end EncodedRingPlaneObservation

/-- The exact fields of `P94HalfChairEvidence`, with the unit transported to `V`.  The complete
`HalfChairObservation` (ring size, double-bond ledger value and the two remote-side labels) is
copied literally. -/
structure EncodedHalfChairObservation (V : Type*) where
  unit : EncodedConformationUnit V
  observation : HalfChairObservation

namespace EncodedHalfChairObservation

/-- Encode one actual `P94HalfChairEvidence` record. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94HalfChairEvidence) (valid : record.unit.ValidFor tie.molecule) :
    EncodedHalfChairObservation V where
  unit := EncodedConformationUnit.ofUnit e tie record.unit valid
  observation := record.observation

/-- Decode one half-chair observation back to the source atom numbers. -/
def toSource (e : SourceAtomIndex source ≃ V)
    (record : EncodedHalfChairObservation V) : P94HalfChairEvidence where
  unit := record.unit.toUnit e
  observation := record.observation

/-- Exact source ingress: decoding an encoded record recovers every source field. -/
@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94HalfChairEvidence)
    (valid : record.unit.ValidFor tie.molecule) :
    toSource e (ofSource e tie record valid) = record := by
  cases record with
  | mk unit observation =>
      simp [toSource, ofSource, EncodedConformationUnit.toUnit_ofUnit]

end EncodedHalfChairObservation

/-! ## The total tagged native payload

The tag set is exactly the constructor set of `P94ConformationEvidence`; the four reused payloads
are `ConformerPairObservation`, `TorsionObservation`, `TwistObservation` and
`InOutObservationData`. -/

/-- A total V-native payload for every constructor of the pre-existing
`P94ConformationEvidence State Framework` inductive.  Exactly one constructor is carried; no
source record is stored beside an unrelated encoding. -/
inductive EncodedConformationEvidence (V : Type*) (State : Type*) (Framework : Type*) where
  | conformer (record : ConformerPairObservation V State)
  | torsion (record : TorsionObservation V)
  | eclipsedStaggered (record : EncodedEclipsedStaggeredObservation V)
  | trigonal (record : EncodedTrigonalObservation V)
  | conjugated (record : EncodedConjugatedObservation V)
  | ringPlane (record : EncodedRingPlaneObservation V)
  | twist (record : TwistObservation V State)
  | halfChair (record : EncodedHalfChairObservation V)
  | inOut (record : InOutObservationData Framework V)

/-- The transported conformation unit of an encoded payload. -/
def EncodedConformationEvidence.unit {V : Type*} {State : Type*} {Framework : Type*} :
    EncodedConformationEvidence V State Framework → EncodedConformationUnit V
  | .conformer record => record.unit
  | .torsion record => record.unit
  | .eclipsedStaggered record => record.unit
  | .trigonal record => record.unit
  | .conjugated record => record.unit
  | .ringPlane record => record.unit
  | .twist record => record.unit
  | .halfChair record => record.unit
  | .inOut record => record.unit

/-! ## The extra atom boundedness required by the adapters

`ValidFor` bounds the unit's own atom list and (for `torsionAxis`) its selected unit participants.
It does not mention the torsion *frame* participants, the priority candidate lists, or the
`InOutObservation` bridge sites; those are the only extra references.  `RawBounded` states exactly
them, at the tied raw molecule's atom count, and is `True` for the seven constructors whose only
atom references are the unit's. -/

/-- Extra raw-atom boundedness required to transport one source evidence record into `V`.
Dispatched on all nine constructors. -/
def RawBounded (tie : RawSourceTie source) :
    P94ConformationEvidence State Framework → Prop
  | .conformer _ => True
  | .torsion record =>
      P94ConformationUnit.ParticipantBounded record.frame.front tie.molecule.atomCount ∧
      P94ConformationUnit.ParticipantBounded record.frame.rear tie.molecule.atomCount ∧
      record.CandidateParticipantsBounded tie.molecule.atomCount
  | .eclipsedStaggered _ => True
  | .trigonal _ => True
  | .conjugated _ => True
  | .ringPlane _ => True
  | .twist _ => True
  | .halfChair _ => True
  | .inOut record =>
      record.first.bridgehead < tie.molecule.atomCount ∧
      P94ConformationUnit.ParticipantBounded record.first.directedParticipant
        tie.molecule.atomCount ∧
      record.second.bridgehead < tie.molecule.atomCount ∧
      P94ConformationUnit.ParticipantBounded record.second.directedParticipant
        tie.molecule.atomCount

/-! ## Bounds derived from existing predicates

The torsion case of `RawBounded` is not an assumption: `ValidFor` supplies the bounds of the
selected unit participants, and `MolecularRolesValid` identifies those participants with the
frame's front/rear participants (and bounds every priority candidate).  `RawSourceTie`
transports the raw bounds to the source enumeration used by the existing adapters. -/

/-- Candidate-list boundedness at the raw molecule transports to the source enumeration. -/
theorem candidateParticipantsBounded_source (tie : RawSourceTie source)
    (record : P94TorsionEvidence) :
    record.CandidateParticipantsBounded tie.molecule.atomCount →
      record.CandidateParticipantsBounded source.input.molecule.atomCount := by
  intro bounded
  obtain ⟨frontBound, rearBound, allBounds⟩ := bounded
  exact ⟨tie.participantBounded frontBound, tie.participantBounded rearBound,
    fun candidate member => tie.participantBounded (allBounds candidate member)⟩

/-- The full torsion part of `RawBounded` follows from the record's own `ValidFor` predicate, its
`MolecularRolesValid` predicate for the tied molecule, and the actual `torsionAxis` kind.  No
inverse relation or fabricated bound is used: `ValidFor` bounds the selected participants and
`AxisParticipantsValid` proves the frame names those very participants. -/
theorem rawBounded_torsion_of_validFor_of_roles (tie : RawSourceTie source)
    (record : P94TorsionEvidence) (kind : record.unit.kind = .torsionAxis)
    (valid : record.unit.ValidFor tie.molecule)
    (roles : (P94ConformationEvidence.torsion record :
      P94ConformationEvidence State Framework).MolecularRolesValid tie.molecule) :
    RawBounded (State := State) (Framework := Framework) tie (.torsion record) := by
  obtain ⟨candidateBounds, front, rear, axisFront, axisRear, participantsEq,
    frameFrontEq, frameRearEq, _endpoints, _frontAttached, _rearAttached⟩ :=
    (P94TorsionEvidence.molecularRolesValid_iff_axisParticipants
      (State := State) (Framework := Framework) record tie.molecule).mp roles
  obtain ⟨_nodup, _atomsBounded, front', rear', axisFront', axisRear', participantsEq',
    _endpoints', _twoLe, _consecutive, frontBound, rearBound, _frontAttached', _rearAttached'⟩ :=
    (P94ConformationUnit.torsionAxis_validFor_iff record.unit tie.molecule kind).mp valid
  have someEq : some (front, rear) = some (front', rear') := by
    rw [← participantsEq, participantsEq']
  have pairEq : (front, rear) = (front', rear') := by
    simpa using someEq
  have frontEq : front = front' := by
    simpa using congrArg Prod.fst pairEq
  have rearEq : rear = rear' := by
    simpa using congrArg Prod.snd pairEq
  refine ⟨?_, ?_, candidateBounds⟩
  · rw [frameFrontEq, frontEq]
    exact frontBound
  · rw [frameRearEq, rearEq]
    exact rearBound

/-! ## Encoding and decoding -/

/-- Encode one actual source evidence record into the total native payload.  The record's own
`ValidFor` predicate supplies the unit bounds; `RawBounded` supplies exactly the remaining torsion
and in/out references. -/
def ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94ConformationEvidence State Framework)
    (valid : record.unit.ValidFor tie.molecule)
    (bounded : RawBounded tie record) : EncodedConformationEvidence V State Framework :=
  match record with
  | .conformer rec =>
      .conformer (ConformerPairObservation.ofSource e tie rec valid)
  | .torsion rec =>
      .torsion (TorsionObservation.ofSource e tie rec valid
        (tie.participantBounded bounded.1)
        (tie.participantBounded bounded.2.1)
        (candidateParticipantsBounded_source tie rec bounded.2.2))
  | .eclipsedStaggered rec =>
      .eclipsedStaggered (EncodedEclipsedStaggeredObservation.ofSource e tie rec valid)
  | .trigonal rec =>
      .trigonal (EncodedTrigonalObservation.ofSource e tie rec valid)
  | .conjugated rec =>
      .conjugated (EncodedConjugatedObservation.ofSource e tie rec valid)
  | .ringPlane rec =>
      .ringPlane (EncodedRingPlaneObservation.ofSource e tie rec valid)
  | .twist rec =>
      .twist (TwistObservation.ofSource e tie rec valid)
  | .halfChair rec =>
      .halfChair (EncodedHalfChairObservation.ofSource e tie rec valid)
  | .inOut rec =>
      .inOut (InOutObservationData.ofSource e tie rec valid
        (tie.atom_bound bounded.1)
        (tie.participantBounded bounded.2.1)
        (tie.atom_bound bounded.2.2.1)
        (tie.participantBounded bounded.2.2.2))

/-- Decode one native payload back to the source evidence inductive.  Every constructor is
dispatched; no payload is left undecoded. -/
def toSource (e : SourceAtomIndex source ≃ V) :
    EncodedConformationEvidence V State Framework → P94ConformationEvidence State Framework
  | .conformer record => .conformer (record.toSource e)
  | .torsion record => .torsion (record.toSource e)
  | .eclipsedStaggered record => .eclipsedStaggered (record.toSource e)
  | .trigonal record => .trigonal (record.toSource e)
  | .conjugated record => .conjugated (record.toSource e)
  | .ringPlane record => .ringPlane (record.toSource e)
  | .twist record => .twist (record.toSource e)
  | .halfChair record => .halfChair (record.toSource e)
  | .inOut record => .inOut (record.toSource e)

/-- Exact decode-after-encode for all nine constructors: every field of the original record,
including every ordered list, every selected candidate and every proposition, is recovered. -/
@[simp] theorem toSource_ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94ConformationEvidence State Framework)
    (valid : record.unit.ValidFor tie.molecule)
    (bounded : RawBounded tie record) :
    toSource e (ofSource e tie record valid bounded) = record := by
  cases record with
  | conformer rec =>
      simp [ofSource, toSource, ConformerPairObservation.toSource_ofSource]
  | torsion rec =>
      simp [ofSource, toSource, TorsionObservation.toSource_ofSource]
  | eclipsedStaggered rec =>
      simp [ofSource, toSource, EncodedEclipsedStaggeredObservation.toSource_ofSource]
  | trigonal rec =>
      simp [ofSource, toSource, EncodedTrigonalObservation.toSource_ofSource]
  | conjugated rec =>
      simp [ofSource, toSource, EncodedConjugatedObservation.toSource_ofSource]
  | ringPlane rec =>
      simp [ofSource, toSource, EncodedRingPlaneObservation.toSource_ofSource]
  | twist rec =>
      simp [ofSource, toSource, TwistObservation.toSource_ofSource]
  | halfChair rec =>
      simp [ofSource, toSource, EncodedHalfChairObservation.toSource_ofSource]
  | inOut rec =>
      simp [ofSource, toSource, InOutObservationData.toSource_ofSource]

/-- Encoding is a section of decoding: it is injective on records carrying their own validity and
boundedness witnesses. -/
theorem ofSource_injective (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    {first second : P94ConformationEvidence State Framework}
    (firstValid : first.unit.ValidFor tie.molecule) (firstBounded : RawBounded tie first)
    (secondValid : second.unit.ValidFor tie.molecule) (secondBounded : RawBounded tie second)
    (equal : ofSource e tie first firstValid firstBounded =
      ofSource e tie second secondValid secondBounded) : first = second := by
  have decoded := congrArg (toSource e) equal
  simpa [toSource_ofSource] using decoded

/-! ## Unit coherence of the encode/decode pair -/

/-- The encoded unit is exactly the existing `EncodedConformationUnit.ofUnit` image of the source
unit. -/
@[simp] theorem ofSource_unit (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94ConformationEvidence State Framework)
    (valid : record.unit.ValidFor tie.molecule)
    (bounded : RawBounded tie record) :
    (ofSource e tie record valid bounded).unit =
      EncodedConformationUnit.ofUnit e tie record.unit valid := by
  cases record with
  | conformer rec => rfl
  | torsion rec => rfl
  | eclipsedStaggered rec => rfl
  | trigonal rec => rfl
  | conjugated rec => rfl
  | ringPlane rec => rfl
  | twist rec => rfl
  | halfChair rec => rfl
  | inOut rec => rfl

/-- Decoding commutes with the unit projection. -/
@[simp] theorem toSource_unit (e : SourceAtomIndex source ≃ V)
    (payload : EncodedConformationEvidence V State Framework) :
    (toSource e payload).unit = EncodedConformationUnit.toUnit e payload.unit := by
  cases payload with
  | conformer record => rfl
  | torsion record => rfl
  | eclipsedStaggered record => rfl
  | trigonal record => rfl
  | conjugated record => rfl
  | ringPlane record => rfl
  | twist record => rfl
  | halfChair record => rfl
  | inOut record => rfl

/-- Optional selection is preserved exactly: a `none` selected-participant pair stays `none`, and
a `some` pair is decoded participant by participant. -/
@[simp] theorem toSource_unit_torsionParticipants? (e : SourceAtomIndex source ≃ V)
    (payload : EncodedConformationEvidence V State Framework) :
    (toSource e payload).unit.torsionParticipants? =
      payload.unit.torsionParticipants?.map (fun pair =>
        (decodeParticipant e pair.1, decodeParticipant e pair.2)) := by
  rw [toSource_unit]
  rfl

/-- Every atom of a decoded unit lies in the actual source enumeration. -/
theorem toSource_unit_atoms_bounded (e : SourceAtomIndex source ≃ V)
    (payload : EncodedConformationEvidence V State Framework) :
    ∀ atom ∈ (toSource e payload).unit.atoms,
      atom < source.input.molecule.atomCount := by
  intro atom member
  rw [toSource_unit] at member
  exact EncodedConformationUnit.toUnit_atoms_bounded e payload.unit atom member

/-- Every decoded torsion participant of a decoded unit is bounded by the source atom count, for
all three participant kinds. -/
theorem decodeParticipant_bounded (e : SourceAtomIndex source ≃ V)
    (participant : TorsionParticipant V) :
    P94ConformationUnit.ParticipantBounded (decodeParticipant e participant)
      source.input.molecule.atomCount := by
  cases participant with
  | atom atom => exact decodeIndex_lt e atom
  | lonePair center => exact decodeIndex_lt e center
  | duplicateAtom original => exact decodeIndex_lt e original

/-- The decoded unit's optional selected participants, when present, are bounded. -/
theorem toSource_unit_participants_bounded (e : SourceAtomIndex source ≃ V)
    (payload : EncodedConformationEvidence V State Framework) :
    ∀ pair, (toSource e payload).unit.torsionParticipants? = some pair →
      P94ConformationUnit.ParticipantBounded pair.1 source.input.molecule.atomCount ∧
      P94ConformationUnit.ParticipantBounded pair.2 source.input.molecule.atomCount := by
  intro pair present
  rw [toSource_unit] at present
  change (payload.unit.torsionParticipants?.map
    (fun pair => (decodeParticipant e pair.1, decodeParticipant e pair.2))) = some pair at present
  cases encoded? : payload.unit.torsionParticipants? with
  | none =>
      rw [encoded?] at present
      simp at present
  | some encodedPair =>
      rw [encoded?] at present
      obtain ⟨first, second⟩ := pair
      have pairEq :
          (decodeParticipant e encodedPair.1, decodeParticipant e encodedPair.2) =
            (first, second) := by
        simpa using present
      have firstEq : decodeParticipant e encodedPair.1 = first := by
        simpa using congrArg Prod.fst pairEq
      have secondEq : decodeParticipant e encodedPair.2 = second := by
        simpa using congrArg Prod.snd pairEq
      rw [← firstEq, ← secondEq]
      exact ⟨decodeParticipant_bounded e encodedPair.1,
        decodeParticipant_bounded e encodedPair.2⟩

/-! ## Recovery of the source predicates through the exact decoded equality

These are the only sense in which `Supports` and `MolecularRolesValid` are "transported": the
decoded record is literally the source record, so its source predicates are the original ones.
Nothing here asserts that an arbitrary encoded payload is valid. -/

/-- The descriptor-support relation of the decoded record is exactly that of the source record. -/
theorem supports_toSource_ofSource (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (record : P94ConformationEvidence State Framework)
    (valid : record.unit.ValidFor tie.molecule)
    (bounded : RawBounded tie record)
    (descriptor : P94ConformationDescriptor) :
    (toSource e (ofSource e tie record valid bounded)).Supports descriptor ↔
      record.Supports descriptor := by
  rw [toSource_ofSource]

/-- The molecule-relative role-validity predicate of the decoded record is exactly that of the
source record, for every molecule. -/
theorem molecularRolesValid_toSource_ofSource (e : SourceAtomIndex source ≃ V)
    (tie : RawSourceTie source) (record : P94ConformationEvidence State Framework)
    (valid : record.unit.ValidFor tie.molecule)
    (bounded : RawBounded tie record) (molecule : RawMolecule) :
    (toSource e (ofSource e tie record valid bounded)).MolecularRolesValid molecule ↔
      record.MolecularRolesValid molecule := by
  rw [toSource_ofSource]

/-! ## Set-level image roundtrip

An arbitrary set of source evidence records that share one source tie and one boundedness witness
is preserved exactly: decoding the encoded image returns the original set.  No record is
deduplicated and no set element is silently dropped. -/

/-- The encoded image of a set of source evidence records.  Each element carries its own validity
and boundedness witness drawn from the supplied family-wide functions; the resulting encoded
payloads form a genuine set, so correlated record families are preserved as a correlated set. -/
def encodeSet (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (records : Set (P94ConformationEvidence State Framework))
    (valid : ∀ record ∈ records, record.unit.ValidFor tie.molecule)
    (bounded : ∀ record ∈ records, RawBounded tie record) :
    Set (EncodedConformationEvidence V State Framework) :=
  { payload | ∃ record, ∃ member : record ∈ records,
      ofSource e tie record (valid record member) (bounded record member) = payload }

/-- Exact set-level roundtrip: the decoded image of the encoded set is the original set. -/
theorem toSource_image_encodeSet (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (records : Set (P94ConformationEvidence State Framework))
    (valid : ∀ record ∈ records, record.unit.ValidFor tie.molecule)
    (bounded : ∀ record ∈ records, RawBounded tie record) :
    toSource e '' encodeSet e tie records valid bounded = records := by
  ext record
  constructor
  · rintro ⟨payload, ⟨sourceRecord, member, rfl⟩, decoded⟩
    rw [toSource_ofSource] at decoded
    rw [← decoded]
    exact member
  · intro member
    exact ⟨ofSource e tie record (valid record member) (bounded record member),
      ⟨record, member, rfl⟩,
      toSource_ofSource e tie record (valid record member) (bounded record member)⟩

/-! ## Ordered list-of-evidence ingress and exact source mirror

An arbitrary ordered list of source evidence records is transported member by member.  The encoder
is a dependent partial map (`List.pmap`): each member is encoded by the concrete `ofSource` above
using *that member's own* `ValidFor` and `RawBounded` witnesses.  `List.pmap` distinguishes list
members by their position, so repetitions of the same record are encoded as separate payloads in
the same positions; nothing is deduplicated, reordered or collapsed.

The inverse is the actual `toSource` decoder applied elementwise.  `toSource_map_encodeList` proves
that mapping `toSource` over the encoder output is *exactly* the original list — not merely
equal-length, equal-count, or equal as a set.  Consequently order, multiplicity and every repeated
element are recovered, and the ordered list endpoint composes with the per-record theorems above.

The boundedness discipline is unchanged and explicit at this endpoint: the caller supplies, for
every member of the list, the record's actual `record.unit.ValidFor tie.molecule` predicate and its
`RawBounded tie record` predicate.  `RawBounded` is *not* derived from bare `ValidFor` here: the
`inOut` bridge sites (`first.bridgehead`, `first.directedParticipant`, `second.bridgehead`,
`second.directedParticipant`) have no constraining `ValidFor` branch and remain explicit
hypotheses, while the torsion branch is the one that can be obtained from `ValidFor` together with
`MolecularRolesValid` and the `.torsionAxis` kind via `rawBounded_torsion_of_validFor_of_roles`.
-/

/-- Encode an arbitrary ordered list of source evidence records.  The dependent bounded map uses
`List.pmap`, so each member is encoded by the concrete `ofSource` with its own validity and
boundedness witnesses; the output list is positionwise aligned with the input list. -/
def encodeList (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (records : List (P94ConformationEvidence State Framework))
    (valid : ∀ record ∈ records, record.unit.ValidFor tie.molecule)
    (bounded : ∀ record ∈ records, RawBounded tie record) :
    List (EncodedConformationEvidence V State Framework) :=
  records.pmap
    (fun record (witness : record.unit.ValidFor tie.molecule ∧ RawBounded tie record) =>
      ofSource e tie record witness.1 witness.2)
    (fun record member => ⟨valid record member, bounded record member⟩)

/-- Exact ordered list roundtrip: mapping the actual decoder `toSource` over the encoded list
returns the original list, in the original order and with the original multiplicity.  This is an
equality of lists, so every repeated evidence record maps to a distinct encoded payload and back
to the same position. -/
theorem toSource_map_encodeList (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (records : List (P94ConformationEvidence State Framework))
    (valid : ∀ record ∈ records, record.unit.ValidFor tie.molecule)
    (bounded : ∀ record ∈ records, RawBounded tie record) :
    (encodeList e tie records valid bounded).map (toSource e) = records := by
  unfold encodeList
  rw [List.map_pmap]
  have hdecode :
      (fun (record : P94ConformationEvidence State Framework)
          (witness : record.unit.ValidFor tie.molecule ∧ RawBounded tie record) =>
        toSource e (ofSource e tie record witness.1 witness.2)) =
      (fun (record : P94ConformationEvidence State Framework) _ => record) := by
    funext record witness
    exact toSource_ofSource e tie record witness.1 witness.2
  rw [hdecode, List.pmap_eq_map]
  simp

/-- The encoded ordered list has exactly as many members as the source list: no evidence record is
dropped, merged or duplicated by the list encoder. -/
theorem length_encodeList (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (records : List (P94ConformationEvidence State Framework))
    (valid : ∀ record ∈ records, record.unit.ValidFor tie.molecule)
    (bounded : ∀ record ∈ records, RawBounded tie record) :
    (encodeList e tie records valid bounded).length = records.length := by
  have h := congrArg List.length (toSource_map_encodeList e tie records valid bounded)
  simpa [List.length_map] using h

/-- Every occurrence of a source record produces an encoded payload in the encoded list whose
decoding is that occurrence.  This is the elementwise form of the ordered list roundtrip; repeated
occurrences yield (possibly repeated) payloads, and no member is lost. -/
theorem exists_mem_encodeList_of_mem (e : SourceAtomIndex source ≃ V) (tie : RawSourceTie source)
    (records : List (P94ConformationEvidence State Framework))
    (valid : ∀ record ∈ records, record.unit.ValidFor tie.molecule)
    (bounded : ∀ record ∈ records, RawBounded tie record)
    {record : P94ConformationEvidence State Framework} (member : record ∈ records) :
    ∃ payload ∈ encodeList e tie records valid bounded, toSource e payload = record := by
  have hmember : record ∈ (encodeList e tie records valid bounded).map (toSource e) := by
    rw [toSource_map_encodeList]
    exact member
  exact List.mem_map.mp hmember

end OrganicStereoP94CompleteEvidenceIngress
end TetraStereo.OneCenter
