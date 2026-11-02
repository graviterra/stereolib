import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.P93PracticalSpatialUnitPerception
import TetraStereo.OneCenter.IUPACP93RingAssemblyAuthorityCarrier
import TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

set_option autoImplicit false















































namespace TetraStereo.OneCenter

open BlueBookP93.PracticalSpatialUnitPerception
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

namespace OrganicStereoAxialFrameEncoding

/-! ## Exact source incidences -/

/-- One reference atom attached to an axis endpoint by an exact source interaction occurrence.

`interactionIndex` selects the occurrence in `source.molecule.interactions`; `interaction` stores
its full semantic content (participants and interaction kind).  The index matters when the source
contains duplicate interaction records: the frame keeps only the reference atom, while this ledger
entry keeps the occurrence identity. -/
structure SourceAxialIncidence where
  referenceAtom : Nat
  interactionIndex : Nat
  interaction : SemanticInteraction
  deriving DecidableEq, Repr

/-- Executable mirror of `P93AuthorityBinaryInteractionKind`.  Keeping the incidence predicate
computable lets concrete source records be checked without introducing a decidability instance for
the authority predicate. -/
def P93AuthorityBinaryInteractionKindBool : SemanticInteractionKind → Bool
  | .unspecifiedCovalent => true
  | .covalent _ => true
  | .aromatic => true
  | .delocalized _ => true
  | .coordinate => true
  | .multicenter _ => false
  | .ionic => false
  | .metallic => false
  | .hydrogenBond => false
  | .other _ => false

@[simp] theorem p93AuthorityBinaryInteractionKindBool_eq_true_iff
    (kind : SemanticInteractionKind) :
    P93AuthorityBinaryInteractionKindBool kind = true ↔
      P93AuthorityBinaryInteractionKind kind := by
  cases kind <;>
    simp [P93AuthorityBinaryInteractionKindBool, P93AuthorityBinaryInteractionKind]

/-- The exact source interaction occurrence `incidence` attaches reference atom
`incidence.referenceAtom` to `endpoint`.

The endpoint/reference pair is an actual binary interaction: the recorded occurrence exists at its
claimed index, its semantic kind is a binary constitutional kind, and its participant list is the
unordered endpoint/reference pair.  Nothing else (ring membership, aromaticity, element identity,
bond order) is required. -/
def SourceAxialIncidence.AttachedTo
    (source : AuthoritativeChemicalInput) (endpoint : Nat)
    (incidence : SourceAxialIncidence) : Prop :=
  source.molecule.interactions[incidence.interactionIndex]? = some incidence.interaction ∧
    endpoint ≠ incidence.referenceAtom ∧
    P93AuthorityBinaryInteractionKindBool incidence.interaction.kind = true ∧
    (incidence.interaction.participants = [endpoint, incidence.referenceAtom] ∨
      incidence.interaction.participants = [incidence.referenceAtom, endpoint])

/-- An exact source incidence yields the existing authority binary-bond predicate. -/
theorem p93AuthorityBinaryBond_of_attached
    (source : AuthoritativeChemicalInput) (endpoint : Nat)
    (incidence : SourceAxialIncidence)
    (attached : incidence.AttachedTo source endpoint) :
    P93AuthorityBinaryBond source endpoint incidence.referenceAtom := by
  rcases attached with ⟨lookupEq, distinct, kindBool, participants⟩
  refine ⟨distinct, incidence.interaction, ?_, ?_, participants⟩
  · exact List.mem_of_getElem? lookupEq
  · exact (p93AuthorityBinaryInteractionKindBool_eq_true_iff
      incidence.interaction.kind).mp kindBool

/-! ## The independent input: generic endpoint frame -/

/-- Independently specified, source-indexed endpoint data.

The six atom indices are the bounded axis endpoints and four reference atoms.  Each reference atom
is paired with the exact source interaction occurrence that attaches it to its endpoint.  The
structure contains no sense, descriptor, priority or geometry field.

This structure is *generic*: it does not assert that `axisStart` and `axisEnd` are directly bonded,
so it also describes longer-path axial units such as cumulenes.  The binary-bond axis layer below
adds that evidence separately. -/
structure SourceIndexedAxialFrame where
  source : AuthoritativeChemicalInput
  axisStart : Nat
  axisEnd : Nat
  startFirst : SourceAxialIncidence
  startSecond : SourceAxialIncidence
  endFirst : SourceAxialIncidence
  endSecond : SourceAxialIncidence
  deriving DecidableEq, Repr

/-- The six source atom indices are real atoms of the source molecule. -/
def SourceIndexedAxialFrame.Bounded (frame : SourceIndexedAxialFrame) : Prop :=
  frame.axisStart < frame.source.molecule.atomCount ∧
    frame.axisEnd < frame.source.molecule.atomCount ∧
    frame.startFirst.referenceAtom < frame.source.molecule.atomCount ∧
    frame.startSecond.referenceAtom < frame.source.molecule.atomCount ∧
    frame.endFirst.referenceAtom < frame.source.molecule.atomCount ∧
    frame.endSecond.referenceAtom < frame.source.molecule.atomCount

/-- Exactly the distinctness required by the practical axial frame.

Only the two endpoints, the two references within each endpoint, and the crossing pairs
reference-versus-opposite-endpoint are separated.  References on *different* endpoints may be the
same atom; this is intentional and is exercised by an example below.  The separate `AttachedTo`
witnesses additionally carry the intrinsic distinctness of the two participants of each actual
binary interaction, but no six-way pairwise distinctness is imposed. -/
def SourceIndexedAxialFrame.DistinctEndpointReferences
    (frame : SourceIndexedAxialFrame) : Prop :=
  frame.axisStart ≠ frame.axisEnd ∧
    frame.startFirst.referenceAtom ≠ frame.startSecond.referenceAtom ∧
    frame.endFirst.referenceAtom ≠ frame.endSecond.referenceAtom ∧
    frame.startFirst.referenceAtom ≠ frame.axisEnd ∧
    frame.startSecond.referenceAtom ≠ frame.axisEnd ∧
    frame.endFirst.referenceAtom ≠ frame.axisStart ∧
    frame.endSecond.referenceAtom ≠ frame.axisStart

/-- The four exact source interaction witnesses of the frame. -/
def SourceIndexedAxialFrame.SourceInteractionWitnesses
    (frame : SourceIndexedAxialFrame) : Prop :=
  frame.startFirst.AttachedTo frame.source frame.axisStart ∧
    frame.startSecond.AttachedTo frame.source frame.axisStart ∧
    frame.endFirst.AttachedTo frame.source frame.axisEnd ∧
    frame.endSecond.AttachedTo frame.source frame.axisEnd

/-- Meaningful independent validity of a source-indexed axis: bounded real atoms, exactly the
destination frame's distinctness, and four actual source interaction occurrences.

The two axis endpoints need not be bonded; see `BinaryBondAxisFrame` for the binary-bond layer. -/
def ActualAxialIncidence (frame : SourceIndexedAxialFrame) : Prop :=
  frame.Bounded ∧
    frame.DistinctEndpointReferences ∧
    frame.SourceInteractionWitnesses

/-! ## Direct semantic-neighbour validity (no parser assumption)

This layer is stated entirely on the supplied source constitution.  It requires no parser, no
normalization result, no coordinates and no descriptor. -/

/-- Semantic binary adjacency in a source constitution: some actual binary interaction occurrence
has exactly the unordered participant pair.  This is weaker than `P93AuthorityBinaryBond` only in
that it does not repeat the endpoint-distinctness side condition. -/
def SemanticBinaryAdjacent (molecule : SemanticMolecule) (left right : Nat) : Prop :=
  ∃ interaction ∈ molecule.interactions,
    P93AuthorityBinaryInteractionKind interaction.kind ∧
      (interaction.participants = [left, right] ∨
        interaction.participants = [right, left])

/-- An exact source incidence gives semantic adjacency directly. -/
theorem semanticBinaryAdjacent_of_attached
    (source : AuthoritativeChemicalInput) (endpoint : Nat)
    (incidence : SourceAxialIncidence)
    (attached : incidence.AttachedTo source endpoint) :
    SemanticBinaryAdjacent source.molecule endpoint incidence.referenceAtom := by
  rcases attached with ⟨lookupEq, _, kindBool, participants⟩
  exact ⟨incidence.interaction, List.mem_of_getElem? lookupEq,
    (p93AuthorityBinaryInteractionKindBool_eq_true_iff
      incidence.interaction.kind).mp kindBool,
    participants⟩

/-- The authority binary-bond predicate gives semantic adjacency. -/
theorem semanticBinaryAdjacent_of_authorityBinaryBond
    (source : AuthoritativeChemicalInput) {left right : Nat}
    (bond : P93AuthorityBinaryBond source left right) :
    SemanticBinaryAdjacent source.molecule left right := by
  rcases bond with ⟨_, interaction, member, kind, participants⟩
  exact ⟨interaction, member, kind, participants⟩

/-- Each reference atom is a semantic binary neighbour of its endpoint in the source. -/
def SourceIndexedAxialFrame.SemanticAxialFrameNeighbors
    (frame : SourceIndexedAxialFrame) : Prop :=
  SemanticBinaryAdjacent frame.source.molecule frame.axisStart
      frame.startFirst.referenceAtom ∧
    SemanticBinaryAdjacent frame.source.molecule frame.axisStart
      frame.startSecond.referenceAtom ∧
    SemanticBinaryAdjacent frame.source.molecule frame.axisEnd
      frame.endFirst.referenceAtom ∧
    SemanticBinaryAdjacent frame.source.molecule frame.axisEnd
      frame.endSecond.referenceAtom

/-- Direct source-level validity of a generic endpoint frame.

This is the semantic-neighbour analogue of the practical frame judgment and is proved below from
actual incidences without any parser bridge.  It is deliberately *not* claimed equivalent to the
practical frame judgment; that upgrade needs the optional parser bridge, whose scope is qualified in
the next section. -/
def SemanticAxialFrameFieldValidity (frame : SourceIndexedAxialFrame) : Prop :=
  frame.Bounded ∧
    frame.DistinctEndpointReferences ∧
    frame.SemanticAxialFrameNeighbors

/-- Actual source incidences imply direct semantic-neighbour validity, with no parser,
normalization, coordinate or descriptor hypothesis. -/
theorem semanticAxialFrameFieldValidity_of_actualAxialIncidence
    (frame : SourceIndexedAxialFrame)
    (actual : ActualAxialIncidence frame) :
    SemanticAxialFrameFieldValidity frame := by
  rcases actual with ⟨bounded, distinct, startFirst, startSecond, endFirst, endSecond⟩
  exact ⟨bounded, distinct,
    ⟨semanticBinaryAdjacent_of_attached frame.source frame.axisStart
        frame.startFirst startFirst,
      semanticBinaryAdjacent_of_attached frame.source frame.axisStart
        frame.startSecond startSecond,
      semanticBinaryAdjacent_of_attached frame.source frame.axisEnd
        frame.endFirst endFirst,
      semanticBinaryAdjacent_of_attached frame.source frame.axisEnd
        frame.endSecond endSecond⟩⟩

/-! ## Encoding into the existing practical record -/

/-- The existing sense-free practical axial record. -/
def SourceIndexedAxialFrame.toPracticalCandidate
    (frame : SourceIndexedAxialFrame) : PracticalAxialCandidate :=
  { axisStart := frame.axisStart
    axisEnd := frame.axisEnd
    startFirst := frame.startFirst.referenceAtom
    startSecond := frame.startSecond.referenceAtom
    endFirst := frame.endFirst.referenceAtom
    endSecond := frame.endSecond.referenceAtom }

/-- The existing indexed axial observation, with the separately supplied orientation sense. -/
def SourceIndexedAxialFrame.toObservation
    (frame : SourceIndexedAxialFrame) (sense : StereoSense) :
    IndexedAxialGeometryObservation :=
  frame.toPracticalCandidate.toObservation sense

@[simp] theorem toPracticalCandidate_axisStart (frame : SourceIndexedAxialFrame) :
    frame.toPracticalCandidate.axisStart = frame.axisStart := rfl

@[simp] theorem toPracticalCandidate_axisEnd (frame : SourceIndexedAxialFrame) :
    frame.toPracticalCandidate.axisEnd = frame.axisEnd := rfl

@[simp] theorem toPracticalCandidate_startFirst (frame : SourceIndexedAxialFrame) :
    frame.toPracticalCandidate.startFirst = frame.startFirst.referenceAtom := rfl

@[simp] theorem toPracticalCandidate_startSecond (frame : SourceIndexedAxialFrame) :
    frame.toPracticalCandidate.startSecond = frame.startSecond.referenceAtom := rfl

@[simp] theorem toPracticalCandidate_endFirst (frame : SourceIndexedAxialFrame) :
    frame.toPracticalCandidate.endFirst = frame.endFirst.referenceAtom := rfl

@[simp] theorem toPracticalCandidate_endSecond (frame : SourceIndexedAxialFrame) :
    frame.toPracticalCandidate.endSecond = frame.endSecond.referenceAtom := rfl

@[simp] theorem toObservation_axisStart (frame : SourceIndexedAxialFrame)
    (sense : StereoSense) :
    (frame.toObservation sense).axisStart = frame.axisStart := rfl

@[simp] theorem toObservation_axisEnd (frame : SourceIndexedAxialFrame)
    (sense : StereoSense) :
    (frame.toObservation sense).axisEnd = frame.axisEnd := rfl

@[simp] theorem toObservation_startFirst (frame : SourceIndexedAxialFrame)
    (sense : StereoSense) :
    (frame.toObservation sense).startFirst = frame.startFirst.referenceAtom := rfl

@[simp] theorem toObservation_startSecond (frame : SourceIndexedAxialFrame)
    (sense : StereoSense) :
    (frame.toObservation sense).startSecond = frame.startSecond.referenceAtom := rfl

@[simp] theorem toObservation_endFirst (frame : SourceIndexedAxialFrame)
    (sense : StereoSense) :
    (frame.toObservation sense).endFirst = frame.endFirst.referenceAtom := rfl

@[simp] theorem toObservation_endSecond (frame : SourceIndexedAxialFrame)
    (sense : StereoSense) :
    (frame.toObservation sense).endSecond = frame.endSecond.referenceAtom := rfl

/-! ## Source-attached ledger

The practical record stores only atom indices.  It does not store interaction indices, interaction
records, or even the source molecule.  The ledger retains exactly that forgotten source-side data.
-/

/-- The information forgotten by the practical frame, attached to the full source input. -/
structure SourceAxialInteractionLedger where
  source : AuthoritativeChemicalInput
  startFirst : SourceAxialIncidence
  startSecond : SourceAxialIncidence
  endFirst : SourceAxialIncidence
  endSecond : SourceAxialIncidence
  deriving DecidableEq, Repr

def SourceIndexedAxialFrame.ledger
    (frame : SourceIndexedAxialFrame) : SourceAxialInteractionLedger :=
  { source := frame.source
    startFirst := frame.startFirst
    startSecond := frame.startSecond
    endFirst := frame.endFirst
    endSecond := frame.endSecond }

/-- The practical record together with its source-attached ledger. -/
structure EncodedPracticalAxialFrame where
  source : AuthoritativeChemicalInput
  candidate : PracticalAxialCandidate
  ledger : SourceAxialInteractionLedger
  deriving DecidableEq, Repr

def SourceIndexedAxialFrame.encode
    (frame : SourceIndexedAxialFrame) : EncodedPracticalAxialFrame :=
  { source := frame.source
    candidate := frame.toPracticalCandidate
    ledger := frame.ledger }

/-- Encoding leaves the full source projection unchanged. -/
@[simp] theorem encode_source (frame : SourceIndexedAxialFrame) :
    frame.encode.source = frame.source := rfl

/-- Encoding leaves the ledger's source projection unchanged. -/
@[simp] theorem encode_ledger_source (frame : SourceIndexedAxialFrame) :
    frame.encode.ledger.source = frame.source := rfl

/-- The encoded candidate is literally the existing practical record. -/
@[simp] theorem encode_candidate (frame : SourceIndexedAxialFrame) :
    frame.encode.candidate = frame.toPracticalCandidate := rfl

/-- The ledger retains the exact incidence records used by the frame. -/
@[simp] theorem encode_ledger_startFirst (frame : SourceIndexedAxialFrame) :
    frame.encode.ledger.startFirst = frame.startFirst := rfl

@[simp] theorem encode_ledger_startSecond (frame : SourceIndexedAxialFrame) :
    frame.encode.ledger.startSecond = frame.startSecond := rfl

@[simp] theorem encode_ledger_endFirst (frame : SourceIndexedAxialFrame) :
    frame.encode.ledger.endFirst = frame.endFirst := rfl

@[simp] theorem encode_ledger_endSecond (frame : SourceIndexedAxialFrame) :
    frame.encode.ledger.endSecond = frame.endSecond := rfl

/-- Under actual incidence the ledger stores exact source occurrences: each incidence's full
interaction record really is the interaction at the recorded source-list position. -/
theorem interaction_lookups_of_actualAxialIncidence
    (frame : SourceIndexedAxialFrame)
    (actual : ActualAxialIncidence frame) :
    frame.source.molecule.interactions[frame.startFirst.interactionIndex]? =
        some frame.startFirst.interaction ∧
      frame.source.molecule.interactions[frame.startSecond.interactionIndex]? =
        some frame.startSecond.interaction ∧
      frame.source.molecule.interactions[frame.endFirst.interactionIndex]? =
        some frame.endFirst.interaction ∧
      frame.source.molecule.interactions[frame.endSecond.interactionIndex]? =
        some frame.endSecond.interaction := by
  rcases actual with ⟨_, _, startFirst, startSecond, endFirst, endSecond⟩
  exact ⟨startFirst.1, startSecond.1, endFirst.1, endSecond.1⟩

/-! ## Actual binary-bond axis incidence layer

The generic endpoint frame above deliberately does not force a direct bond between the two axis
endpoints; that keeps it usable for cumulene-type or longer-path units.  When a caller really does
have an actual binary-bond axis, the following separate layer records the exact source interaction
occurrence joining the endpoints, retaining its index and full semantic record. -/

/-- One exact source interaction occurrence selected as the axis bond itself. -/
structure SourceAxisInteraction where
  interactionIndex : Nat
  interaction : SemanticInteraction
  deriving DecidableEq, Repr

/-- The exact axis-bond condition: the recorded occurrence exists at its claimed source position,
the endpoints are distinct, the interaction kind is a binary constitutional kind, and the
participants are exactly the unordered endpoint pair.

There is no aromatic, carbon, ring or localized-bond restriction; `.delocalized` and `.coordinate`
interactions are accepted here.  Such broad interactions cannot in general be supplied by the raw
parser, which is why the parser bridge is a separate, explicitly qualified route. -/
def SourceAxisInteraction.IsBinaryBond
    (source : AuthoritativeChemicalInput) (axisStart axisEnd : Nat)
    (axis : SourceAxisInteraction) : Prop :=
  source.molecule.interactions[axis.interactionIndex]? = some axis.interaction ∧
    axisStart ≠ axisEnd ∧
    P93AuthorityBinaryInteractionKindBool axis.interaction.kind = true ∧
    (axis.interaction.participants = [axisStart, axisEnd] ∨
      axis.interaction.participants = [axisEnd, axisStart])

/-- An actual axis occurrence is an existing authority binary bond between the endpoints. -/
theorem p93AuthorityBinaryBond_of_axisBond
    (source : AuthoritativeChemicalInput) (axisStart axisEnd : Nat)
    (axis : SourceAxisInteraction)
    (bond : SourceAxisInteraction.IsBinaryBond source axisStart axisEnd axis) :
    P93AuthorityBinaryBond source axisStart axisEnd := by
  rcases bond with ⟨lookupEq, distinct, kindBool, participants⟩
  exact ⟨distinct, axis.interaction, List.mem_of_getElem? lookupEq,
    (p93AuthorityBinaryInteractionKindBool_eq_true_iff axis.interaction.kind).mp kindBool,
    participants⟩

/-- Independently specified actual binary-bond axis: the generic endpoint/reference frame together
with one exact source interaction occurrence joining the two axis endpoints.

The generic frame is a field, not a strengthening of its own predicate: `frame.endpoints` may still
represent a longer-path unit when the axis occurrence is supplied separately. -/
structure BinaryBondAxisFrame where
  endpoints : SourceIndexedAxialFrame
  axisInteraction : SourceAxisInteraction
  deriving DecidableEq, Repr

/-- Meaningful independent validity of a binary-bond axis: the four endpoint/reference incidences
are actual, and the axis occurrence is an actual source binary interaction joining the endpoints. -/
def BinaryBondAxisFrame.Actual (frame : BinaryBondAxisFrame) : Prop :=
  ActualAxialIncidence frame.endpoints ∧
    SourceAxisInteraction.IsBinaryBond frame.endpoints.source
      frame.endpoints.axisStart frame.endpoints.axisEnd frame.axisInteraction

/-- The binary-bond layer projects to the generic actual layer; no generic conclusion is lost. -/
theorem actualAxialIncidence_of_actualBinaryAxis
    (frame : BinaryBondAxisFrame) (actual : frame.Actual) :
    ActualAxialIncidence frame.endpoints :=
  actual.1

/-- The axis occurrence is an existing authority binary bond between the endpoints. -/
theorem p93AuthorityBinaryBond_axisStart_axisEnd_of_actual
    (frame : BinaryBondAxisFrame) (actual : frame.Actual) :
    P93AuthorityBinaryBond frame.endpoints.source
      frame.endpoints.axisStart frame.endpoints.axisEnd :=
  p93AuthorityBinaryBond_of_axisBond frame.endpoints.source frame.endpoints.axisStart
    frame.endpoints.axisEnd frame.axisInteraction actual.2

/-- The binary-bond layer encodes to the same existing practical record (the axis occurrence is
not a field of the destination record). -/
def BinaryBondAxisFrame.toPracticalCandidate
    (frame : BinaryBondAxisFrame) : PracticalAxialCandidate :=
  frame.endpoints.toPracticalCandidate

/-- The binary-bond layer's indexed observation, with separately supplied orientation sense. -/
def BinaryBondAxisFrame.toObservation
    (frame : BinaryBondAxisFrame) (sense : StereoSense) :
    IndexedAxialGeometryObservation :=
  frame.endpoints.toObservation sense

@[simp] theorem binaryToPracticalCandidate_axisStart (frame : BinaryBondAxisFrame) :
    frame.toPracticalCandidate.axisStart = frame.endpoints.axisStart := rfl

@[simp] theorem binaryToPracticalCandidate_axisEnd (frame : BinaryBondAxisFrame) :
    frame.toPracticalCandidate.axisEnd = frame.endpoints.axisEnd := rfl

@[simp] theorem binaryToPracticalCandidate_startFirst (frame : BinaryBondAxisFrame) :
    frame.toPracticalCandidate.startFirst =
      frame.endpoints.startFirst.referenceAtom := rfl

@[simp] theorem binaryToPracticalCandidate_startSecond (frame : BinaryBondAxisFrame) :
    frame.toPracticalCandidate.startSecond =
      frame.endpoints.startSecond.referenceAtom := rfl

@[simp] theorem binaryToPracticalCandidate_endFirst (frame : BinaryBondAxisFrame) :
    frame.toPracticalCandidate.endFirst =
      frame.endpoints.endFirst.referenceAtom := rfl

@[simp] theorem binaryToPracticalCandidate_endSecond (frame : BinaryBondAxisFrame) :
    frame.toPracticalCandidate.endSecond =
      frame.endpoints.endSecond.referenceAtom := rfl

/-! ### Binary-bond ledger

The axis occurrence itself is also forgotten by the practical record, so it is retained alongside
the four reference incidences. -/

/-- Full source-side information of an actual binary-bond axis. -/
structure BinaryBondAxisLedger where
  source : AuthoritativeChemicalInput
  axisInteraction : SourceAxisInteraction
  startFirst : SourceAxialIncidence
  startSecond : SourceAxialIncidence
  endFirst : SourceAxialIncidence
  endSecond : SourceAxialIncidence
  deriving DecidableEq, Repr

def BinaryBondAxisFrame.ledger
    (frame : BinaryBondAxisFrame) : BinaryBondAxisLedger :=
  { source := frame.endpoints.source
    axisInteraction := frame.axisInteraction
    startFirst := frame.endpoints.startFirst
    startSecond := frame.endpoints.startSecond
    endFirst := frame.endpoints.endFirst
    endSecond := frame.endpoints.endSecond }

/-- The practical record together with the full binary-bond ledger. -/
structure EncodedBinaryBondAxisFrame where
  source : AuthoritativeChemicalInput
  candidate : PracticalAxialCandidate
  ledger : BinaryBondAxisLedger
  deriving DecidableEq, Repr

def BinaryBondAxisFrame.encode
    (frame : BinaryBondAxisFrame) : EncodedBinaryBondAxisFrame :=
  { source := frame.endpoints.source
    candidate := frame.toPracticalCandidate
    ledger := frame.ledger }

@[simp] theorem binaryEncode_source (frame : BinaryBondAxisFrame) :
    frame.encode.source = frame.endpoints.source := rfl

@[simp] theorem binaryEncode_ledger_source (frame : BinaryBondAxisFrame) :
    frame.encode.ledger.source = frame.endpoints.source := rfl

@[simp] theorem binaryEncode_candidate (frame : BinaryBondAxisFrame) :
    frame.encode.candidate = frame.toPracticalCandidate := rfl

@[simp] theorem binaryEncode_ledger_axisInteraction (frame : BinaryBondAxisFrame) :
    frame.encode.ledger.axisInteraction = frame.axisInteraction := rfl

/-- The ledger retains the exact axis occurrence index, which the practical record forgets. -/
@[simp] theorem binaryEncode_ledger_axisInteractionIndex (frame : BinaryBondAxisFrame) :
    frame.encode.ledger.axisInteraction.interactionIndex =
      frame.axisInteraction.interactionIndex := rfl

/-- The ledger retains the exact axis interaction record, which the practical record forgets. -/
@[simp] theorem binaryEncode_ledger_axisInteractionRecord (frame : BinaryBondAxisFrame) :
    frame.encode.ledger.axisInteraction.interaction =
      frame.axisInteraction.interaction := rfl

@[simp] theorem binaryEncode_ledger_startFirst (frame : BinaryBondAxisFrame) :
    frame.encode.ledger.startFirst = frame.endpoints.startFirst := rfl

@[simp] theorem binaryEncode_ledger_startSecond (frame : BinaryBondAxisFrame) :
    frame.encode.ledger.startSecond = frame.endpoints.startSecond := rfl

@[simp] theorem binaryEncode_ledger_endFirst (frame : BinaryBondAxisFrame) :
    frame.encode.ledger.endFirst = frame.endpoints.endFirst := rfl

@[simp] theorem binaryEncode_ledger_endSecond (frame : BinaryBondAxisFrame) :
    frame.encode.ledger.endSecond = frame.endpoints.endSecond := rfl

/-- Under actual incidence the ledger's axis occurrence really is the interaction at the recorded
source-list position.  This is the recovery half of the ledger contract. -/
theorem axisInteraction_lookup_of_actual
    (frame : BinaryBondAxisFrame) (actual : frame.Actual) :
    frame.encode.ledger.source.molecule.interactions[
        frame.encode.ledger.axisInteraction.interactionIndex]? =
      some frame.encode.ledger.axisInteraction.interaction := by
  simpa only [BinaryBondAxisFrame.encode, BinaryBondAxisFrame.ledger] using actual.2.1

/-! ## Optional parser bridge and its scope

The practical frame predicate consumes the written-neighbour rows of the normalization result's
explicit-hydrogen molecule.  The bridge below says that this parsed molecule is the supplied source
constitution and that its written-neighbour view is exact.  It asserts no chemical eligibility and
no descriptor.

**Scope limitation.**  The raw parser's bond image contains only `.unspecifiedCovalent`,
`.covalent 1/2/3` and `.aromatic` interactions.  The semantic layer accepts broader
`.coordinate`/`.delocalized` interactions, so the bridge is *not* available for arbitrary sources:
its applicability requires, among other conditions, that every source interaction lie in the
raw-bond image (and additionally the exact semantic conversion, diagram agreement, parser
well-formedness and written-neighbour exactness recorded by `SourceFaithfulNormalizationFrame`).
Raw-kind membership is therefore necessary but not sufficient.  The direct semantic-neighbour
theorems above do not depend on this bridge at all. -/

/-- Separately evidenced exactness of the parsed molecule against the supplied source. -/
structure SourceFaithfulNormalizationFrame
    (result : ChemistryNormalizationResult)
    (source : AuthoritativeChemicalInput) : Prop where
  semanticConversion : result.parsed.toSemanticMolecule? = some source.molecule
  diagramAgreement : source.diagram? = some result.parsed.toDiagramConfiguration
  wellFormed : result.parsed.WellFormed
  writtenNeighborExact : result.parsed.WrittenNeighborExact

/-- The bridge is exactly the existing `AuthoritativeStructureAgreement` plus structural exactness
of the written rows. -/
theorem SourceFaithfulNormalizationFrame.authoritativeStructureAgreement
    (result : ChemistryNormalizationResult) (source : AuthoritativeChemicalInput)
    (bridge : SourceFaithfulNormalizationFrame result source) :
    result.parsed.AuthoritativeStructureAgreement source :=
  ⟨bridge.semanticConversion, bridge.diagramAgreement⟩

/-- The interaction kinds producible by `RawBond.toSemanticInteraction`. -/
def RawInteractionKindImage : SemanticInteractionKind → Prop
  | .unspecifiedCovalent => True
  | .covalent 1 | .covalent 2 | .covalent 3 => True
  | .aromatic => True
  | _ => False

/-- Every raw bond maps to an interaction kind in the parser image. -/
theorem rawBond_kind_image (bond : RawBond) :
    RawInteractionKindImage bond.toSemanticInteraction.kind := by
  rcases bond with ⟨source, target, kind⟩
  cases kind <;> simp [RawBond.toSemanticInteraction, RawInteractionKindImage]

theorem not_rawInteractionKindImage_coordinate :
    ¬ RawInteractionKindImage (.coordinate : SemanticInteractionKind) := by
  simp [RawInteractionKindImage]

theorem not_rawInteractionKindImage_delocalized (electrons : Nat) :
    ¬ RawInteractionKindImage (.delocalized electrons) := by
  simp [RawInteractionKindImage]

/-- In a source-faithful normalization frame every source interaction kind lies in the raw-parser
image.  This is a necessary condition on the parser bridge, not a sufficient one: the bridge also
requires exact semantic conversion, diagram agreement, parser well-formedness and written-row
exactness. -/
theorem SourceFaithfulNormalizationFrame.interaction_kinds_in_parser_image
    (result : ChemistryNormalizationResult) (source : AuthoritativeChemicalInput)
    (bridge : SourceFaithfulNormalizationFrame result source) :
    ∀ interaction ∈ source.molecule.interactions,
      RawInteractionKindImage interaction.kind := by
  intro interaction member
  have interactionsEq :
      source.molecule.interactions =
        result.parsed.bonds.map RawBond.toSemanticInteraction :=
    RawMolecule.toSemanticMolecule?_interactions result.parsed source.molecule
      bridge.semanticConversion
  have mappedMember :
      interaction ∈ result.parsed.bonds.map RawBond.toSemanticInteraction := by
    rw [← interactionsEq]
    exact member
  obtain ⟨bond, _, bondEq⟩ := List.mem_map.mp mappedMember
  rw [← bondEq]
  exact rawBond_kind_image bond

/-- A source containing a `.coordinate` interaction cannot enter the parser bridge, although the
direct semantic layer accepts it. -/
theorem no_sourceFaithful_of_coordinate_interaction
    (result : ChemistryNormalizationResult) (source : AuthoritativeChemicalInput)
    (interaction : SemanticInteraction)
    (member : interaction ∈ source.molecule.interactions)
    (kind : interaction.kind = .coordinate) :
    ¬ SourceFaithfulNormalizationFrame result source := by
  intro bridge
  have image :=
    SourceFaithfulNormalizationFrame.interaction_kinds_in_parser_image
      result source bridge interaction member
  rw [kind] at image
  exact not_rawInteractionKindImage_coordinate image

/-- A source containing a `.delocalized` interaction likewise cannot enter the parser bridge. -/
theorem no_sourceFaithful_of_delocalized_interaction
    (result : ChemistryNormalizationResult) (source : AuthoritativeChemicalInput)
    (interaction : SemanticInteraction) (electrons : Nat)
    (member : interaction ∈ source.molecule.interactions)
    (kind : interaction.kind = .delocalized electrons) :
    ¬ SourceFaithfulNormalizationFrame result source := by
  intro bridge
  have image :=
    SourceFaithfulNormalizationFrame.interaction_kinds_in_parser_image
      result source bridge interaction member
  rw [kind] at image
  exact not_rawInteractionKindImage_delocalized electrons image

/-- Every original written neighbour survives hydrogen materialization. -/
theorem mem_withExplicitHydrogens_writtenNeighbors_of_mem
    (molecule : RawMolecule) (well : molecule.WellFormed)
    (exact : molecule.WrittenNeighborExact)
    {center ligand : Nat} (centerBound : center < molecule.atomCount)
    (member : ligand ∈ molecule.writtenNeighbors center) :
    ligand ∈ molecule.withExplicitHydrogens.writtenNeighbors center := by
  rw [withExplicitHydrogens_writtenNeighbors molecule well exact center centerBound]
  unfold materializedWrittenRow
  refine (RawMolecule.insertHydrogenInOrder_perm (molecule.writtenNeighbors center)
    (materializationHasPreceding molecule center)
    (materializedHydrogenIds molecule center)).mem_iff.mpr ?_
  exact List.mem_append.mpr (Or.inr member)

/-- A source binary bond is visible in the exact written-neighbour row of the parsed molecule. -/
theorem sourceBond_mem_writtenNeighbors_of_source
    (result : ChemistryNormalizationResult) (source : AuthoritativeChemicalInput)
    (bridge : SourceFaithfulNormalizationFrame result source)
    {endpoint ref : Nat}
    (endpointBound : endpoint < source.molecule.atomCount)
    (refBound : ref < source.molecule.atomCount)
    (distinct : endpoint ≠ ref)
    (bond : P93AuthorityBinaryBond source endpoint ref) :
    ref ∈ result.parsed.writtenNeighbors endpoint := by
  rcases bond with ⟨_, interaction, interactionMem, _, participants⟩
  have interactionsEq :
      source.molecule.interactions =
        result.parsed.bonds.map RawBond.toSemanticInteraction :=
    RawMolecule.toSemanticMolecule?_interactions result.parsed source.molecule
      bridge.semanticConversion
  have mappedMember :
      interaction ∈ result.parsed.bonds.map RawBond.toSemanticInteraction := by
    rw [← interactionsEq]
    exact interactionMem
  obtain ⟨rawBond, rawBondMem, rawBondEq⟩ := List.mem_map.mp mappedMember
  have participantEq :
      [rawBond.source, rawBond.target] = interaction.participants := by
    have applied := congrArg SemanticInteraction.participants rawBondEq
    simpa [RawBond.toSemanticInteraction] using applied
  have connects : rawBond.connects endpoint ref = true := by
    rcases participants with oriented | oriented
    · have listEq : [rawBond.source, rawBond.target] = [endpoint, ref] := by
        rw [participantEq, oriented]
      simp at listEq
      rcases listEq with ⟨rfl, rfl⟩
      simp [RawBond.connects]
    · have listEq : [rawBond.source, rawBond.target] = [ref, endpoint] := by
        rw [participantEq, oriented]
      simp at listEq
      rcases listEq with ⟨rfl, rfl⟩
      simp [RawBond.connects]
  have positive : 0 < result.parsed.bondOrder endpoint ref :=
    (RawMolecule.bondOrder_pos_iff_exists_bond result.parsed distinct).mpr
      ⟨rawBond, rawBondMem, connects⟩
  have atomCountEq : source.molecule.atomCount = result.parsed.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount result.parsed source.molecule
      bridge.semanticConversion
  have endpointBound' : endpoint < result.parsed.atomCount := atomCountEq ▸ endpointBound
  have refBound' : ref < result.parsed.atomCount := atomCountEq ▸ refBound
  exact ((RawMolecule.WrittenNeighborExact.at result.parsed bridge.writtenNeighborExact
    ⟨endpoint, endpointBound'⟩).2.2 ⟨ref, refBound'⟩).mpr positive

/-- An exact source incidence is visible in the practical frame's neighbour row. -/
theorem frameNeighbor_of_attached
    (result : ChemistryNormalizationResult) (frame : SourceIndexedAxialFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.source)
    (incidence : SourceAxialIncidence) {endpoint : Nat}
    (endpointBound : endpoint < frame.source.molecule.atomCount)
    (referenceBound :
      incidence.referenceAtom < frame.source.molecule.atomCount)
    (attached : incidence.AttachedTo frame.source endpoint) :
    incidence.referenceAtom ∈
      result.geometryPriorityState.1.writtenNeighbors endpoint := by
  have bond :
      P93AuthorityBinaryBond frame.source endpoint incidence.referenceAtom :=
    p93AuthorityBinaryBond_of_attached frame.source endpoint incidence attached
  have member :
      incidence.referenceAtom ∈ result.parsed.writtenNeighbors endpoint :=
    sourceBond_mem_writtenNeighbors_of_source result frame.source bridge
      endpointBound referenceBound attached.2.1 bond
  have atomCountEq : frame.source.molecule.atomCount = result.parsed.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount result.parsed frame.source.molecule
      bridge.semanticConversion
  have endpointBound' : endpoint < result.parsed.atomCount := atomCountEq ▸ endpointBound
  have expandedMember :
      incidence.referenceAtom ∈
        result.parsed.withExplicitHydrogens.writtenNeighbors endpoint :=
    mem_withExplicitHydrogens_writtenNeighbors_of_mem result.parsed
      bridge.wellFormed bridge.writtenNeighborExact endpointBound' member
  simpa [ChemistryNormalizationResult.geometryPriorityState] using expandedMember

/-- Semantic binary adjacency upgrades to a written-neighbour row across the parser bridge.  The
endpoint-distinctness side condition of the authority binary bond is supplied explicitly; it is not
part of semantic adjacency. -/
theorem writtenNeighbors_of_semanticBinaryAdjacent
    (result : ChemistryNormalizationResult) (source : AuthoritativeChemicalInput)
    (bridge : SourceFaithfulNormalizationFrame result source)
    {endpoint ref : Nat}
    (endpointBound : endpoint < source.molecule.atomCount)
    (refBound : ref < source.molecule.atomCount)
    (distinct : endpoint ≠ ref)
    (adjacent : SemanticBinaryAdjacent source.molecule endpoint ref) :
    ref ∈ result.parsed.writtenNeighbors endpoint := by
  obtain ⟨interaction, member, kind, participants⟩ := adjacent
  exact sourceBond_mem_writtenNeighbors_of_source result source bridge
    endpointBound refBound distinct
    ⟨distinct, interaction, member, kind, participants⟩

/-- The same upgrade through explicit-hydrogen materialization, i.e. to the row actually consumed
by the practical frame. -/
theorem frameNeighbor_of_semanticBinaryAdjacent
    (result : ChemistryNormalizationResult) (frame : SourceIndexedAxialFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.source)
    {endpoint ref : Nat}
    (endpointBound : endpoint < frame.source.molecule.atomCount)
    (referenceBound : ref < frame.source.molecule.atomCount)
    (distinct : endpoint ≠ ref)
    (adjacent : SemanticBinaryAdjacent frame.source.molecule endpoint ref) :
    ref ∈ result.geometryPriorityState.1.writtenNeighbors endpoint := by
  have member :
      ref ∈ result.parsed.writtenNeighbors endpoint :=
    writtenNeighbors_of_semanticBinaryAdjacent result frame.source bridge
      endpointBound referenceBound distinct adjacent
  have atomCountEq : frame.source.molecule.atomCount = result.parsed.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount result.parsed frame.source.molecule
      bridge.semanticConversion
  have endpointBound' : endpoint < result.parsed.atomCount := atomCountEq ▸ endpointBound
  have expandedMember :
      ref ∈ result.parsed.withExplicitHydrogens.writtenNeighbors endpoint :=
    mem_withExplicitHydrogens_writtenNeighbors_of_mem result.parsed
      bridge.wellFormed bridge.writtenNeighborExact endpointBound' member
  simpa [ChemistryNormalizationResult.geometryPriorityState] using expandedMember

/-! ## Validity correspondence -/

/-- The boundedness component of the practical frame, stated on the frame's fields. -/
def PracticalAxialFrameBounds
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame) : Prop :=
  frame.axisStart < result.parsed.atomCount ∧
    frame.axisEnd < result.parsed.atomCount ∧
    frame.startFirst.referenceAtom < result.parsed.atomCount ∧
    frame.startSecond.referenceAtom < result.parsed.atomCount ∧
    frame.endFirst.referenceAtom < result.parsed.atomCount ∧
    frame.endSecond.referenceAtom < result.parsed.atomCount

/-- The distinctness component of the practical frame is the input's distinctness component. -/
abbrev PracticalAxialFrameDistinctness
    (frame : SourceIndexedAxialFrame) : Prop :=
  frame.DistinctEndpointReferences

/-- The adjacency component of the practical frame, stated on the frame's fields. -/
def PracticalAxialFrameNeighbors
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame) : Prop :=
  frame.startFirst.referenceAtom ∈
      result.geometryPriorityState.1.writtenNeighbors frame.axisStart ∧
    frame.startSecond.referenceAtom ∈
      result.geometryPriorityState.1.writtenNeighbors frame.axisStart ∧
    frame.endFirst.referenceAtom ∈
      result.geometryPriorityState.1.writtenNeighbors frame.axisEnd ∧
    frame.endSecond.referenceAtom ∈
      result.geometryPriorityState.1.writtenNeighbors frame.axisEnd

/-- The practical frame's validity, decomposed on the source-indexed fields. -/
def PracticalAxialFrameFieldValidity
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame) : Prop :=
  PracticalAxialFrameBounds result frame ∧
    PracticalAxialFrameDistinctness frame ∧
    PracticalAxialFrameNeighbors result frame

/-- Exact field-level correspondence: the existing practical frame judgment on the encoded
candidate is precisely the decomposed frame validity on the source-indexed fields. -/
theorem practicalAxialMolecularFrameJudgment_iff_fieldValidity
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame) :
    PracticalAxialMolecularFrameJudgment result frame.toPracticalCandidate ↔
      PracticalAxialFrameFieldValidity result frame := by
  unfold PracticalAxialMolecularFrameJudgment PracticalAxialFrameFieldValidity
    PracticalAxialFrameBounds PracticalAxialFrameDistinctness
    PracticalAxialFrameNeighbors SourceIndexedAxialFrame.toPracticalCandidate
    SourceIndexedAxialFrame.DistinctEndpointReferences
  tauto

/-- Semantic neighbours upgrade to the practical neighbour rows, provided the parser bridge is
available and the same-endpoint participant distinctness (which the destination record does not
state) is supplied explicitly.  This is the qualified parser route; it is not assumed for broad
interactions outside the raw-parser image. -/
theorem practicalAxialFrameNeighbors_of_semanticAxialFrameNeighbors
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.source)
    (bounds : PracticalAxialFrameBounds result frame)
    (sameEndpointDistinct :
      frame.axisStart ≠ frame.startFirst.referenceAtom ∧
        frame.axisStart ≠ frame.startSecond.referenceAtom ∧
          frame.axisEnd ≠ frame.endFirst.referenceAtom ∧
            frame.axisEnd ≠ frame.endSecond.referenceAtom)
    (neighbors : frame.SemanticAxialFrameNeighbors) :
    PracticalAxialFrameNeighbors result frame := by
  obtain ⟨axisStartBound, axisEndBound, startFirstBound, startSecondBound,
    endFirstBound, endSecondBound⟩ := bounds
  obtain ⟨neStartFirst, neStartSecond, neEndFirst, neEndSecond⟩ := sameEndpointDistinct
  obtain ⟨startFirstAdjacent, startSecondAdjacent, endFirstAdjacent,
    endSecondAdjacent⟩ := neighbors
  have atomCountEq : frame.source.molecule.atomCount = result.parsed.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount result.parsed frame.source.molecule
      bridge.semanticConversion
  exact ⟨
    frameNeighbor_of_semanticBinaryAdjacent result frame bridge
      (atomCountEq.symm ▸ axisStartBound) (atomCountEq.symm ▸ startFirstBound)
      neStartFirst startFirstAdjacent,
    frameNeighbor_of_semanticBinaryAdjacent result frame bridge
      (atomCountEq.symm ▸ axisStartBound) (atomCountEq.symm ▸ startSecondBound)
      neStartSecond startSecondAdjacent,
    frameNeighbor_of_semanticBinaryAdjacent result frame bridge
      (atomCountEq.symm ▸ axisEndBound) (atomCountEq.symm ▸ endFirstBound)
      neEndFirst endFirstAdjacent,
    frameNeighbor_of_semanticBinaryAdjacent result frame bridge
      (atomCountEq.symm ▸ axisEndBound) (atomCountEq.symm ▸ endSecondBound)
      neEndSecond endSecondAdjacent⟩

/-- Direct semantic validity upgrades to the practical frame validity across the qualified parser
bridge. -/
theorem practicalAxialFrameFieldValidity_of_semanticAxialFrameFieldValidity
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.source)
    (semantic : SemanticAxialFrameFieldValidity frame)
    (sameEndpointDistinct :
      frame.axisStart ≠ frame.startFirst.referenceAtom ∧
        frame.axisStart ≠ frame.startSecond.referenceAtom ∧
          frame.axisEnd ≠ frame.endFirst.referenceAtom ∧
            frame.axisEnd ≠ frame.endSecond.referenceAtom) :
    PracticalAxialFrameFieldValidity result frame := by
  obtain ⟨bounded, distinct, neighbors⟩ := semantic
  obtain ⟨bound1, bound2, bound3, bound4, bound5, bound6⟩ := bounded
  have atomCountEq : frame.source.molecule.atomCount = result.parsed.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount result.parsed frame.source.molecule
      bridge.semanticConversion
  have resultBounds : PracticalAxialFrameBounds result frame :=
    ⟨atomCountEq ▸ bound1, atomCountEq ▸ bound2, atomCountEq ▸ bound3,
      atomCountEq ▸ bound4, atomCountEq ▸ bound5, atomCountEq ▸ bound6⟩
  exact ⟨resultBounds, distinct,
    practicalAxialFrameNeighbors_of_semanticAxialFrameNeighbors result frame bridge
      resultBounds sameEndpointDistinct neighbors⟩

/-- Actual source incidences make the decomposed frame validity hold (parser-bridge route). -/
theorem practicalAxialFrameFieldValidity_of_actualAxialIncidence
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.source)
    (actual : ActualAxialIncidence frame) :
    PracticalAxialFrameFieldValidity result frame := by
  rcases actual with ⟨bounded, distinct, witnesses⟩
  rcases bounded with ⟨axisStartBound, axisEndBound, startFirstBound,
    startSecondBound, endFirstBound, endSecondBound⟩
  rcases witnesses with ⟨startFirstAttached, startSecondAttached,
    endFirstAttached, endSecondAttached⟩
  have atomCountEq : frame.source.molecule.atomCount = result.parsed.atomCount :=
    RawMolecule.toSemanticMolecule?_atomCount result.parsed frame.source.molecule
      bridge.semanticConversion
  refine ⟨?_, distinct, ?_⟩
  · exact ⟨atomCountEq ▸ axisStartBound, atomCountEq ▸ axisEndBound,
      atomCountEq ▸ startFirstBound, atomCountEq ▸ startSecondBound,
      atomCountEq ▸ endFirstBound, atomCountEq ▸ endSecondBound⟩
  · exact ⟨
      frameNeighbor_of_attached result frame bridge frame.startFirst
        axisStartBound startFirstBound startFirstAttached,
      frameNeighbor_of_attached result frame bridge frame.startSecond
        axisStartBound startSecondBound startSecondAttached,
      frameNeighbor_of_attached result frame bridge frame.endFirst
        axisEndBound endFirstBound endFirstAttached,
      frameNeighbor_of_attached result frame bridge frame.endSecond
        axisEndBound endSecondBound endSecondAttached⟩

/-- Actual source incidence implies the existing practical molecular frame judgment. -/
theorem practicalAxialMolecularFrameJudgment_of_actualAxialIncidence
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.source)
    (actual : ActualAxialIncidence frame) :
    PracticalAxialMolecularFrameJudgment result frame.toPracticalCandidate :=
  (practicalAxialMolecularFrameJudgment_iff_fieldValidity result frame).mpr
    (practicalAxialFrameFieldValidity_of_actualAxialIncidence
      result frame bridge actual)

/-- Executable correspondence for the existing Boolean frame check. -/
theorem practicalAxialMolecularFrameOK?_toPracticalCandidate_eq_true_iff
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame) :
    practicalAxialMolecularFrameOK? result frame.toPracticalCandidate = true ↔
      PracticalAxialFrameFieldValidity result frame := by
  rw [practicalAxialMolecularFrameOK?_eq_true_iff,
    practicalAxialMolecularFrameJudgment_iff_fieldValidity]

/-- The existing Boolean frame check accepts every actual source-indexed axis. -/
theorem practicalAxialMolecularFrameOK?_toPracticalCandidate_of_actualAxialIncidence
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.source)
    (actual : ActualAxialIncidence frame) :
    practicalAxialMolecularFrameOK? result frame.toPracticalCandidate = true :=
  (practicalAxialMolecularFrameOK?_toPracticalCandidate_eq_true_iff result frame).mpr
    (practicalAxialFrameFieldValidity_of_actualAxialIncidence
      result frame bridge actual)

/-- The binary-bond layer satisfies the existing practical molecular frame judgment whenever the
four reference incidences do.  The axis occurrence itself is not a destination field. -/
theorem practicalAxialMolecularFrameJudgment_of_actualBinaryAxis
    (result : ChemistryNormalizationResult)
    (frame : BinaryBondAxisFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.endpoints.source)
    (actual : frame.Actual) :
    PracticalAxialMolecularFrameJudgment result frame.toPracticalCandidate := by
  have judgment :=
    practicalAxialMolecularFrameJudgment_of_actualAxialIncidence
      result frame.endpoints bridge actual.1
  simpa [BinaryBondAxisFrame.toPracticalCandidate] using judgment

/-- The executable Boolean frame check accepts an actual binary-bond axis. -/
theorem practicalAxialMolecularFrameOK?_of_actualBinaryAxis
    (result : ChemistryNormalizationResult)
    (frame : BinaryBondAxisFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.endpoints.source)
    (actual : frame.Actual) :
    practicalAxialMolecularFrameOK? result frame.toPracticalCandidate = true := by
  have accepted :=
    practicalAxialMolecularFrameOK?_toPracticalCandidate_of_actualAxialIncidence
      result frame.endpoints bridge actual.1
  simpa [BinaryBondAxisFrame.toPracticalCandidate] using accepted

/-- Exact ledger-level correspondence.

The existing frame judgment consists exactly of the endpoint/reference field conditions (bounds,
distinctness, adjacency).  The source-attached ledger supplies the interaction identities that the
frame cannot see.  Together they are equivalent to actual source incidence.  Neither component
alone is claimed to imply actual incidence. -/
theorem actualAxialIncidence_iff_frameValidity_and_sourceWitnesses
    (result : ChemistryNormalizationResult)
    (frame : SourceIndexedAxialFrame)
    (bridge : SourceFaithfulNormalizationFrame result frame.source) :
    ActualAxialIncidence frame ↔
      PracticalAxialMolecularFrameJudgment result frame.toPracticalCandidate ∧
        frame.SourceInteractionWitnesses := by
  constructor
  · intro actual
    exact ⟨practicalAxialMolecularFrameJudgment_of_actualAxialIncidence
        result frame bridge actual,
      actual.2.2⟩
  · rintro ⟨frameJudgment, witnesses⟩
    have fields :=
      (practicalAxialMolecularFrameJudgment_iff_fieldValidity result frame).mp
        frameJudgment
    have atomCountEq : frame.source.molecule.atomCount = result.parsed.atomCount :=
      RawMolecule.toSemanticMolecule?_atomCount result.parsed frame.source.molecule
        bridge.semanticConversion
    have bounds : frame.Bounded := by
      have decomposed : PracticalAxialFrameBounds result frame := fields.1
      unfold PracticalAxialFrameBounds at decomposed
      rcases decomposed with ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨atomCountEq.symm ▸ h1, atomCountEq.symm ▸ h2, atomCountEq.symm ▸ h3,
        atomCountEq.symm ▸ h4, atomCountEq.symm ▸ h5, atomCountEq.symm ▸ h6⟩
    exact ⟨bounds, fields.2.1, witnesses⟩

/-! ## Concrete regression witnesses

The fixtures below are intentionally minimal.  They use carbon only as a neutral test atom; the
encoding itself imposes no element policy.  The first fixture demonstrates that references on the
two different endpoints may coincide, and that the generic frame does not force a direct axis bond
(it can therefore describe a longer-path / cumulene-type unit).  The binary-axis fixtures add the
separate axis occurrence.  The duplicate fixtures demonstrate that the practical frame forgets the
interaction occurrence and that the ledger retains it.
-/

/-- A neutral test atom (carbon); no chemical restriction is attached to it. -/
def carbonAtom : SemanticAtom :=
  { element := ⟨6, by decide, by decide⟩ }

/-- Five atoms and four binary interactions.  The reference atom `2` is attached to both axis
endpoints, which the destination predicate permits.  There is deliberately no `[0, 1]` interaction:
the generic frame accepts this source, so it can describe a longer-path axis. -/
def sharedReferenceSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom]
        interactions :=
          [ ⟨[0, 2], .covalent 1⟩,
            ⟨[0, 3], .covalent 1⟩,
            ⟨[1, 2], .covalent 1⟩,
            ⟨[1, 4], .covalent 1⟩ ] } }

def sharedReferenceFrame : SourceIndexedAxialFrame :=
  { source := sharedReferenceSource
    axisStart := 0
    axisEnd := 1
    startFirst :=
      { referenceAtom := 2
        interactionIndex := 0
        interaction := ⟨[0, 2], .covalent 1⟩ }
    startSecond :=
      { referenceAtom := 3
        interactionIndex := 1
        interaction := ⟨[0, 3], .covalent 1⟩ }
    endFirst :=
      { referenceAtom := 2
        interactionIndex := 2
        interaction := ⟨[1, 2], .covalent 1⟩ }
    endSecond :=
      { referenceAtom := 4
        interactionIndex := 3
        interaction := ⟨[1, 4], .covalent 1⟩ } }

theorem sharedReferenceFrame_actual :
    ActualAxialIncidence sharedReferenceFrame := by
  unfold ActualAxialIncidence SourceIndexedAxialFrame.Bounded
    SourceIndexedAxialFrame.DistinctEndpointReferences
    SourceIndexedAxialFrame.SourceInteractionWitnesses
    SourceAxialIncidence.AttachedTo
  decide

/-- Shared reference atoms are permitted: no gratuitous six-way distinctness is imposed. -/
theorem sharedReference_permitted :
    sharedReferenceFrame.startFirst.referenceAtom =
      sharedReferenceFrame.endFirst.referenceAtom := rfl

/-- The input predicate does not require references on opposite endpoints to differ. -/
theorem not_all_endpoint_references_distinct :
    ¬ (∀ frame : SourceIndexedAxialFrame, ActualAxialIncidence frame →
        frame.startFirst.referenceAtom ≠ frame.endFirst.referenceAtom) := by
  intro allDistinct
  exact allDistinct sharedReferenceFrame sharedReferenceFrame_actual rfl

/-- The generic fixture has no `[0, 1]` interaction at all. -/
theorem sharedReferenceSource_no_axis_bond :
    ¬ P93AuthorityBinaryBond sharedReferenceSource 0 1 := by
  rintro ⟨_, interaction, member, _, participants⟩
  simp [sharedReferenceSource] at member
  rcases member with h | h | h | h
  · subst h; simp at participants
  · subst h; simp at participants
  · subst h; simp at participants
  · subst h; simp at participants

/-- The generic endpoint frame is not silently tightened to a binary-bond axis.  Actual endpoint
incidence does not in general force a direct bond between the two axis atoms. -/
theorem genericFrame_not_forces_axisBond :
    ¬ (∀ frame : SourceIndexedAxialFrame, ActualAxialIncidence frame →
        P93AuthorityBinaryBond frame.source frame.axisStart frame.axisEnd) := by
  intro forces
  exact sharedReferenceSource_no_axis_bond
    (forces sharedReferenceFrame sharedReferenceFrame_actual)

/-- Direct semantic validity of the generic fixture, without any parser bridge. -/
theorem sharedReferenceFrame_semanticValid :
    SemanticAxialFrameFieldValidity sharedReferenceFrame :=
  semanticAxialFrameFieldValidity_of_actualAxialIncidence
    sharedReferenceFrame sharedReferenceFrame_actual

/-! ### Actual binary-bond axis fixture -/

/-- Five atoms: one explicit `[0, 1]` axis bond plus four endpoint/reference interactions. -/
def binaryAxisSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom]
        interactions :=
          [ ⟨[0, 1], .covalent 1⟩,
            ⟨[0, 2], .covalent 1⟩,
            ⟨[0, 3], .covalent 1⟩,
            ⟨[1, 2], .covalent 1⟩,
            ⟨[1, 4], .covalent 1⟩ ] } }

def binaryAxisEndpoints : SourceIndexedAxialFrame :=
  { source := binaryAxisSource
    axisStart := 0
    axisEnd := 1
    startFirst :=
      { referenceAtom := 2
        interactionIndex := 1
        interaction := ⟨[0, 2], .covalent 1⟩ }
    startSecond :=
      { referenceAtom := 3
        interactionIndex := 2
        interaction := ⟨[0, 3], .covalent 1⟩ }
    endFirst :=
      { referenceAtom := 2
        interactionIndex := 3
        interaction := ⟨[1, 2], .covalent 1⟩ }
    endSecond :=
      { referenceAtom := 4
        interactionIndex := 4
        interaction := ⟨[1, 4], .covalent 1⟩ } }

def binaryAxisOccurrence : SourceAxisInteraction :=
  { interactionIndex := 0
    interaction := ⟨[0, 1], .covalent 1⟩ }

def binaryAxisFrame : BinaryBondAxisFrame :=
  { endpoints := binaryAxisEndpoints
    axisInteraction := binaryAxisOccurrence }

theorem binaryAxisEndpoints_actual :
    ActualAxialIncidence binaryAxisEndpoints := by
  unfold ActualAxialIncidence SourceIndexedAxialFrame.Bounded
    SourceIndexedAxialFrame.DistinctEndpointReferences
    SourceIndexedAxialFrame.SourceInteractionWitnesses
    SourceAxialIncidence.AttachedTo
  decide

theorem binaryAxisFrame_actual : binaryAxisFrame.Actual := by
  unfold BinaryBondAxisFrame.Actual SourceAxisInteraction.IsBinaryBond
  exact ⟨binaryAxisEndpoints_actual, by decide⟩

/-- The binary-bond layer really yields the existing authority bond between the endpoints. -/
theorem binaryAxisFrame_axisBond :
    P93AuthorityBinaryBond binaryAxisSource 0 1 :=
  p93AuthorityBinaryBond_axisStart_axisEnd_of_actual binaryAxisFrame binaryAxisFrame_actual

/-- The axis occurrence index is retained in the binary ledger. -/
theorem binaryAxisFrame_ledger_index :
    binaryAxisFrame.encode.ledger.axisInteraction.interactionIndex = 0 := rfl

/-- The axis interaction record is retained in the binary ledger. -/
theorem binaryAxisFrame_ledger_record :
    binaryAxisFrame.encode.ledger.axisInteraction.interaction =
      ⟨[0, 1], .covalent 1⟩ := rfl

/-- The binary axis occurrence is exact in the source. -/
theorem binaryAxisFrame_ledger_lookup :
    binaryAxisFrame.encode.ledger.source.molecule.interactions[
        binaryAxisFrame.encode.ledger.axisInteraction.interactionIndex]? =
      some binaryAxisFrame.encode.ledger.axisInteraction.interaction :=
  axisInteraction_lookup_of_actual binaryAxisFrame binaryAxisFrame_actual

/-- The binary candidate projects the same six atom indices as the endpoint frame. -/
theorem binaryAxisFrame_candidate :
    binaryAxisFrame.toPracticalCandidate = binaryAxisEndpoints.toPracticalCandidate := rfl

/-! ### Broad (parser-irrelevant) interaction fixture

A `.delocalized` axis and reference interactions are accepted by the direct semantic layer, while
the parser bridge is provably unavailable for that source.  This exercises the qualified scope. -/

def delocalizedSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom]
        interactions :=
          [ ⟨[0, 1], .delocalized 4⟩,
            ⟨[0, 2], .covalent 1⟩,
            ⟨[0, 3], .covalent 1⟩,
            ⟨[1, 2], .covalent 1⟩,
            ⟨[1, 4], .covalent 1⟩ ] } }

def delocalizedEndpoints : SourceIndexedAxialFrame :=
  { source := delocalizedSource
    axisStart := 0
    axisEnd := 1
    startFirst :=
      { referenceAtom := 2
        interactionIndex := 1
        interaction := ⟨[0, 2], .covalent 1⟩ }
    startSecond :=
      { referenceAtom := 3
        interactionIndex := 2
        interaction := ⟨[0, 3], .covalent 1⟩ }
    endFirst :=
      { referenceAtom := 2
        interactionIndex := 3
        interaction := ⟨[1, 2], .covalent 1⟩ }
    endSecond :=
      { referenceAtom := 4
        interactionIndex := 4
        interaction := ⟨[1, 4], .covalent 1⟩ } }

theorem delocalizedEndpoints_actual :
    ActualAxialIncidence delocalizedEndpoints := by
  unfold ActualAxialIncidence SourceIndexedAxialFrame.Bounded
    SourceIndexedAxialFrame.DistinctEndpointReferences
    SourceIndexedAxialFrame.SourceInteractionWitnesses
    SourceAxialIncidence.AttachedTo
  decide

/-- Broad sources still receive direct semantic validity. -/
theorem delocalizedEndpoints_semanticValid :
    SemanticAxialFrameFieldValidity delocalizedEndpoints :=
  semanticAxialFrameFieldValidity_of_actualAxialIncidence
    delocalizedEndpoints delocalizedEndpoints_actual

/-- But the parser bridge is impossible for such a source. -/
theorem delocalizedSource_no_parserBridge
    (result : ChemistryNormalizationResult) :
    ¬ SourceFaithfulNormalizationFrame result delocalizedSource :=
  no_sourceFaithful_of_delocalized_interaction result delocalizedSource
    ⟨[0, 1], .delocalized 4⟩ 4 (by decide) rfl

/-! ### Duplicate interaction occurrences -/

/-- A source with two identical interaction records for the same endpoint pair.  The two
occurrences are different interaction identities even though their records agree. -/
def duplicateInteractionSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom]
        interactions :=
          [ ⟨[0, 2], .covalent 1⟩,
            ⟨[0, 2], .covalent 1⟩,
            ⟨[0, 3], .covalent 1⟩,
            ⟨[1, 2], .covalent 1⟩,
            ⟨[1, 4], .covalent 1⟩ ] } }

def duplicateInteractionFrameFirst : SourceIndexedAxialFrame :=
  { source := duplicateInteractionSource
    axisStart := 0
    axisEnd := 1
    startFirst :=
      { referenceAtom := 2
        interactionIndex := 0
        interaction := ⟨[0, 2], .covalent 1⟩ }
    startSecond :=
      { referenceAtom := 3
        interactionIndex := 2
        interaction := ⟨[0, 3], .covalent 1⟩ }
    endFirst :=
      { referenceAtom := 2
        interactionIndex := 3
        interaction := ⟨[1, 2], .covalent 1⟩ }
    endSecond :=
      { referenceAtom := 4
        interactionIndex := 4
        interaction := ⟨[1, 4], .covalent 1⟩ } }

def duplicateInteractionFrameSecond : SourceIndexedAxialFrame :=
  { source := duplicateInteractionSource
    axisStart := 0
    axisEnd := 1
    startFirst :=
      { referenceAtom := 2
        interactionIndex := 1
        interaction := ⟨[0, 2], .covalent 1⟩ }
    startSecond :=
      { referenceAtom := 3
        interactionIndex := 2
        interaction := ⟨[0, 3], .covalent 1⟩ }
    endFirst :=
      { referenceAtom := 2
        interactionIndex := 3
        interaction := ⟨[1, 2], .covalent 1⟩ }
    endSecond :=
      { referenceAtom := 4
        interactionIndex := 4
        interaction := ⟨[1, 4], .covalent 1⟩ } }

theorem duplicateInteractionFrameFirst_actual :
    ActualAxialIncidence duplicateInteractionFrameFirst := by
  unfold ActualAxialIncidence SourceIndexedAxialFrame.Bounded
    SourceIndexedAxialFrame.DistinctEndpointReferences
    SourceIndexedAxialFrame.SourceInteractionWitnesses
    SourceAxialIncidence.AttachedTo
  decide

theorem duplicateInteractionFrameSecond_actual :
    ActualAxialIncidence duplicateInteractionFrameSecond := by
  unfold ActualAxialIncidence SourceIndexedAxialFrame.Bounded
    SourceIndexedAxialFrame.DistinctEndpointReferences
    SourceIndexedAxialFrame.SourceInteractionWitnesses
    SourceAxialIncidence.AttachedTo
  decide

/-- The two inputs have different interaction occurrences but the same practical candidate. -/
theorem duplicateInteraction_candidates_equal :
    duplicateInteractionFrameFirst.toPracticalCandidate =
      duplicateInteractionFrameSecond.toPracticalCandidate := rfl

/-- The ledger distinguishes the two exact source occurrences. -/
theorem duplicateInteraction_ledgers_differ :
    duplicateInteractionFrameFirst.startFirst.interactionIndex ≠
      duplicateInteractionFrameSecond.startFirst.interactionIndex := by
  decide

/-- The practical-record encoding is not injective: erasure of interaction identity is real. -/
theorem toPracticalCandidate_not_injective :
    ¬ Function.Injective SourceIndexedAxialFrame.toPracticalCandidate := by
  intro injective
  have framesEqual :
      duplicateInteractionFrameFirst = duplicateInteractionFrameSecond :=
    injective duplicateInteraction_candidates_equal
  have indicesEqual :
      duplicateInteractionFrameFirst.startFirst.interactionIndex =
        duplicateInteractionFrameSecond.startFirst.interactionIndex := by
    rw [framesEqual]
  exact duplicateInteraction_ledgers_differ indicesEqual

/-! ### Duplicate axis occurrences

Two actual binary-bond axes that differ only in which duplicated axis occurrence they record have
the same practical candidate; the binary ledger retains the distinction. -/

def duplicateAxisSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom]
        interactions :=
          [ ⟨[0, 1], .covalent 1⟩,
            ⟨[0, 1], .covalent 1⟩,
            ⟨[0, 2], .covalent 1⟩,
            ⟨[0, 3], .covalent 1⟩,
            ⟨[1, 2], .covalent 1⟩,
            ⟨[1, 4], .covalent 1⟩ ] } }

def duplicateAxisFrameFirst : BinaryBondAxisFrame :=
  { endpoints :=
      { source := duplicateAxisSource
        axisStart := 0
        axisEnd := 1
        startFirst :=
          { referenceAtom := 2
            interactionIndex := 2
            interaction := ⟨[0, 2], .covalent 1⟩ }
        startSecond :=
          { referenceAtom := 3
            interactionIndex := 3
            interaction := ⟨[0, 3], .covalent 1⟩ }
        endFirst :=
          { referenceAtom := 2
            interactionIndex := 4
            interaction := ⟨[1, 2], .covalent 1⟩ }
        endSecond :=
          { referenceAtom := 4
            interactionIndex := 5
            interaction := ⟨[1, 4], .covalent 1⟩ } }
    axisInteraction :=
      { interactionIndex := 0
        interaction := ⟨[0, 1], .covalent 1⟩ } }

def duplicateAxisFrameSecond : BinaryBondAxisFrame :=
  { endpoints :=
      { source := duplicateAxisSource
        axisStart := 0
        axisEnd := 1
        startFirst :=
          { referenceAtom := 2
            interactionIndex := 2
            interaction := ⟨[0, 2], .covalent 1⟩ }
        startSecond :=
          { referenceAtom := 3
            interactionIndex := 3
            interaction := ⟨[0, 3], .covalent 1⟩ }
        endFirst :=
          { referenceAtom := 2
            interactionIndex := 4
            interaction := ⟨[1, 2], .covalent 1⟩ }
        endSecond :=
          { referenceAtom := 4
            interactionIndex := 5
            interaction := ⟨[1, 4], .covalent 1⟩ } }
    axisInteraction :=
      { interactionIndex := 1
        interaction := ⟨[0, 1], .covalent 1⟩ } }

theorem duplicateAxisFrameFirst_actual : duplicateAxisFrameFirst.Actual := by
  unfold BinaryBondAxisFrame.Actual ActualAxialIncidence SourceIndexedAxialFrame.Bounded
    SourceIndexedAxialFrame.DistinctEndpointReferences
    SourceIndexedAxialFrame.SourceInteractionWitnesses
    SourceAxialIncidence.AttachedTo SourceAxisInteraction.IsBinaryBond
  decide

theorem duplicateAxisFrameSecond_actual : duplicateAxisFrameSecond.Actual := by
  unfold BinaryBondAxisFrame.Actual ActualAxialIncidence SourceIndexedAxialFrame.Bounded
    SourceIndexedAxialFrame.DistinctEndpointReferences
    SourceIndexedAxialFrame.SourceInteractionWitnesses
    SourceAxialIncidence.AttachedTo SourceAxisInteraction.IsBinaryBond
  decide

theorem duplicateAxis_candidates_equal :
    duplicateAxisFrameFirst.toPracticalCandidate =
      duplicateAxisFrameSecond.toPracticalCandidate := rfl

theorem duplicateAxis_ledgers_differ :
    duplicateAxisFrameFirst.axisInteraction.interactionIndex ≠
      duplicateAxisFrameSecond.axisInteraction.interactionIndex := by
  decide

/-- The binary-bond encoding also forgets which duplicated axis occurrence was used; the ledger
retains it.  No injectivity is claimed. -/
theorem binaryToPracticalCandidate_not_injective :
    ¬ Function.Injective BinaryBondAxisFrame.toPracticalCandidate := by
  intro injective
  have framesEqual : duplicateAxisFrameFirst = duplicateAxisFrameSecond :=
    injective duplicateAxis_candidates_equal
  have indicesEqual :
      duplicateAxisFrameFirst.axisInteraction.interactionIndex =
        duplicateAxisFrameSecond.axisInteraction.interactionIndex := by
    rw [framesEqual]
  exact duplicateAxis_ledgers_differ indicesEqual

/-! ## Optional ring-assembly carrier

A source-indexed binary-bond axis is not by itself a P-93.5.7 ring-assembly axis.  The ring and
junction graph conditions are supplied separately, and only then is the existing
`P93RingAssemblyAxisFrameValid` frame constructed.
-/

/-- Separately evidenced ring-assembly graph conditions for one source-indexed frame.  The two
rings, the junction index lookups and the placement of the four references inside those rings are
all explicit.  No assembly policy, citation, descriptor, or stereochemical stability is asserted. -/
def RingAssemblyAxisGraphEvidence
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (junction : P93RingAssemblyJunction)
    (frame : SourceIndexedAxialFrame) : Prop :=
  frame.source = source ∧
    frame.axisStart = junction.leftAtom ∧
    frame.axisEnd = junction.rightAtom ∧
    ∃ leftRing rightRing,
      assembly.rings[junction.leftRingIndex]? = some leftRing ∧
        assembly.rings[junction.rightRingIndex]? = some rightRing ∧
        frame.startFirst.referenceAtom ∈ leftRing ∧
        frame.startSecond.referenceAtom ∈ leftRing ∧
        frame.endFirst.referenceAtom ∈ rightRing ∧
        frame.endSecond.referenceAtom ∈ rightRing

/-- The existing ring-assembly axial frame, constructed only from separate graph evidence plus
actual source incidences.  No generic axis is silently promoted to a ring assembly. -/
theorem ringAssemblyAxisFrameValid_of_actualAxialIncidence
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (junction : P93RingAssemblyJunction)
    (frame : SourceIndexedAxialFrame)
    (sense : StereoSense)
    (evidence : RingAssemblyAxisGraphEvidence source assembly junction frame)
    (actual : ActualAxialIncidence frame) :
    P93RingAssemblyAxisFrameValid source assembly junction
      (frame.toObservation sense) := by
  rcases evidence with ⟨sourceEq, axisStartEq, axisEndEq, leftRing, rightRing,
    leftLookup, rightLookup, startFirstMem, startSecondMem, endFirstMem, endSecondMem⟩
  rcases actual with ⟨_, distinct, witnesses⟩
  rcases distinct with ⟨_, startFirstNeStartSecond, endFirstNeEndSecond, _, _, _, _⟩
  rcases witnesses with ⟨startFirstAttached, startSecondAttached,
    endFirstAttached, endSecondAttached⟩
  have bondStartFirst :
      P93AuthorityBinaryBond source frame.axisStart frame.startFirst.referenceAtom := by
    have derived := p93AuthorityBinaryBond_of_attached frame.source frame.axisStart
      frame.startFirst startFirstAttached
    rwa [sourceEq] at derived
  have bondStartSecond :
      P93AuthorityBinaryBond source frame.axisStart frame.startSecond.referenceAtom := by
    have derived := p93AuthorityBinaryBond_of_attached frame.source frame.axisStart
      frame.startSecond startSecondAttached
    rwa [sourceEq] at derived
  have bondEndFirst :
      P93AuthorityBinaryBond source frame.axisEnd frame.endFirst.referenceAtom := by
    have derived := p93AuthorityBinaryBond_of_attached frame.source frame.axisEnd
      frame.endFirst endFirstAttached
    rwa [sourceEq] at derived
  have bondEndSecond :
      P93AuthorityBinaryBond source frame.axisEnd frame.endSecond.referenceAtom := by
    have derived := p93AuthorityBinaryBond_of_attached frame.source frame.axisEnd
      frame.endSecond endSecondAttached
    rwa [sourceEq] at derived
  exact ⟨axisStartEq, axisEndEq, leftRing, rightRing, leftLookup, rightLookup,
    startFirstMem, startSecondMem, endFirstMem, endSecondMem,
    startFirstNeStartSecond, endFirstNeEndSecond,
    bondStartFirst, bondStartSecond, bondEndFirst, bondEndSecond⟩

/-- The binary-bond layer reaches the ring-assembly carrier only through separate graph evidence,
exactly as the generic layer does. -/
theorem ringAssemblyAxisFrameValid_of_actualBinaryAxis
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (junction : P93RingAssemblyJunction)
    (frame : BinaryBondAxisFrame)
    (sense : StereoSense)
    (evidence : RingAssemblyAxisGraphEvidence source assembly junction frame.endpoints)
    (actual : frame.Actual) :
    P93RingAssemblyAxisFrameValid source assembly junction
      (frame.toObservation sense) :=
  ringAssemblyAxisFrameValid_of_actualAxialIncidence source assembly junction
    frame.endpoints sense evidence actual.1

end OrganicStereoAxialFrameEncoding

end TetraStereo.OneCenter
