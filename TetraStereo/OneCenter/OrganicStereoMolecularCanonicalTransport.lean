import TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

namespace OrganicStereoMolecularCanonicalTransport

open OrganicStereoMolecularEvidenceAssembly

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# Canonical finite transport of the assembled molecular representation

`OrganicStereoMolecularEvidenceAssembly.assemble` produces an
`OrganicMolecularRepresentation V` whose assembled whole state still lives on the supplied atom
labels `V` and on the supplied (arbitrary finite) path and band index types.  This module builds
the *canonical finite representation* of that representation and composes its decoder with the
independently supplied `OrganicMolecularEvidence V` request.

The canonical record stores:

* the two presence tags `pathPresent` / `bandPresent`, copied literally from the representation;
* one explicit atom enumeration `V ≃ Fin (Fintype.card V)`;
* the source edge and band index types as explicit finite shapes, each with its `Fintype`
  instance and one explicit equivalence to `Fin (Fintype.card _)`;
* the assembled whole state **at** `WholeState (Fin (Fintype.card V))
  (Fin (Fintype.card edgeShape)) (Fin (Fintype.card bandShape))`, obtained by the actual
  `OrganicStereoFiniteClassicalDescription.encodeDescription` applied to the representation's
  state (so every channel, including graph atom data, conformation, rational positions, roles,
  path endpoints, band attachment atoms, diagrams, fragments, conventions, cages, residue ledgers
  and frame annotations, is relabelled by the same atom codec and the edge/band families are
  reindexed by the same equivalences);
* a proof-only `PathGeometryValid` field stated about the **decoded actual output state**, i.e.
  about `decodeDescription atomEquiv edgeEquiv bandEquiv state`, never about a retained native
  state.

No `V`-labelled state and no `OrganicMolecularEvidence` request is retained in the canonical
record: the only source context kept is the explicit type/index shape plus the two equivalences
needed to reconstruct the source index types.  Arbitrary finite types are not literally
`Fin (Fintype.card _)`, so the shape is kept honestly as data rather than silently identified
with its cardinality.

The main results are:

* `canonicalDecode_state_canonicalize` — the canonical state really decodes back to the source
  state (a genuine two-sided `encodeDescription` / `decodeDescription` inverse at the
  representation's state);
* `canonicalDecode_canonicalize` and `canonicalDecode_canonicalizeFin` — the representation-level
  inverse `canonicalDecode (canonicalize representation e) = representation`;
* `decode_canonicalAssemble` — decoding the canonical assembly of an independently supplied
  request through the upstream `decode` returns the original request;
* `canonicalAssemble_injective` and
  `decode_image_canonicalDecode_image_canonicalAssemble_image` — injectivity on requests and the
  exact inverse on arbitrary correlated sets of requests.
-/

/-! ## The canonical finite representation -/

/-- The canonical finite representation of an assembled `OrganicMolecularRepresentation V`.

`edgeShape` / `bandShape` are the source index types retained as explicit finite shapes; the
equivalences `edgeEquiv` / `bandEquiv` identify them with the canonical `Fin` index types used by
`state`.  The `state` field is an actual `WholeState` at `Fin` coordinates, and
`pathGeometryValid` is a proof-only witness about the state obtained by decoding that actual
output, not about any hidden native state. -/
structure CanonicalOrganicMolecularRepresentation (V : Type) [DecidableEq V] [Fintype V] where
  /-- Presence tag for the bond-path channel.  Copied literally from the representation. -/
  pathPresent : Bool
  /-- Presence tag for the band channel.  Copied literally from the representation. -/
  bandPresent : Bool
  /-- The explicit atom enumeration used to relabel every atom reference of every channel. -/
  atomEquiv : V ≃ Fin (Fintype.card V)
  /-- The source bond-path index type, retained as an explicit finite shape. -/
  edgeShape : Type
  /-- Finiteness of the retained source edge index type. -/
  fintypeEdgeShape : Fintype edgeShape
  /-- The explicit equivalence from the retained source edge type to canonical `Fin` indices. -/
  edgeEquiv : edgeShape ≃ Fin (@Fintype.card edgeShape fintypeEdgeShape)
  /-- The source band index type, retained as an explicit finite shape. -/
  bandShape : Type
  /-- Finiteness of the retained source band index type. -/
  fintypeBandShape : Fintype bandShape
  /-- The explicit equivalence from the retained source band type to canonical `Fin` indices. -/
  bandEquiv : bandShape ≃ Fin (@Fintype.card bandShape fintypeBandShape)
  /-- The assembled correlated whole state in canonical `Fin` coordinates and index types. -/
  state : @WholeState (Fin (Fintype.card V))
    (Fin (@Fintype.card edgeShape fintypeEdgeShape))
    (Fin (@Fintype.card bandShape fintypeBandShape)) _ _ _ _
  /-- Proof-only geometric validity of the decoded actual output state.  It contains no data. -/
  pathGeometryValid : pathPresent = true →
    (letI : Fintype edgeShape := fintypeEdgeShape
     letI : Fintype bandShape := fintypeBandShape
     PathGeometryValid (decodeDescription atomEquiv edgeEquiv bandEquiv state))

/-! ## Encoding a representation into the canonical finite record -/

/-- Encode an assembled representation into its canonical finite record.  The whole state is
relabelled by the actual `encodeDescription` at the supplied atom enumeration and the supplied
edge/band equivalences; the presence tags are copied exactly; the path-validity field is derived
from the representation's own validity after the (proved) encode/decode state inverse. -/
noncomputable def canonicalize (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    CanonicalOrganicMolecularRepresentation V :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  { pathPresent := representation.pathPresent
    bandPresent := representation.bandPresent
    atomEquiv := atomEquiv
    edgeShape := representation.edgeIndex
    fintypeEdgeShape := representation.fintypeEdgeIndex
    edgeEquiv := edgeEquiv
    bandShape := representation.bandIndex
    fintypeBandShape := representation.fintypeBandIndex
    bandEquiv := bandEquiv
    state := encodeDescription atomEquiv edgeEquiv bandEquiv representation.state
    pathGeometryValid := by
      intro present
      rw [decodeDescription_encodeDescription]
      exact representation.pathGeometryValid present }

/-- The canonical encoding with the canonical `Fin` equivalences chosen noncomputably for the
edge and band index types. -/
noncomputable def canonicalizeFin (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V)) :
    CanonicalOrganicMolecularRepresentation V :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  canonicalize representation atomEquiv (Fintype.equivFin representation.edgeIndex)
    (Fintype.equivFin representation.bandIndex)

/-! ## Decoding the canonical finite record back to a representation -/

/-- Decode a canonical finite record into an assembled representation.  Only the canonical
`Fin`-indexed state, the two presence tags, the explicit finite shapes/equivalences and the
proof-only path validity are read; no native state or request is available. -/
noncomputable def canonicalDecode
    (canonical : CanonicalOrganicMolecularRepresentation V) :
    OrganicMolecularRepresentation V :=
  letI : Fintype canonical.edgeShape := canonical.fintypeEdgeShape
  letI : Fintype canonical.bandShape := canonical.fintypeBandShape
  { pathPresent := canonical.pathPresent
    edgeIndex := canonical.edgeShape
    fintypeEdgeIndex := canonical.fintypeEdgeShape
    bandPresent := canonical.bandPresent
    bandIndex := canonical.bandShape
    fintypeBandIndex := canonical.fintypeBandShape
    state := decodeDescription canonical.atomEquiv canonical.edgeEquiv canonical.bandEquiv
      canonical.state
    pathGeometryValid := canonical.pathGeometryValid }

/-! ## Projections -/

/-- The canonical encoding preserves the path presence tag literally. -/
@[simp] theorem canonicalize_pathPresent (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (canonicalize representation atomEquiv edgeEquiv bandEquiv).pathPresent =
      representation.pathPresent := rfl

/-- The canonical encoding preserves the band presence tag literally. -/
@[simp] theorem canonicalize_bandPresent (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (canonicalize representation atomEquiv edgeEquiv bandEquiv).bandPresent =
      representation.bandPresent := rfl

/-- The canonical edge shape is the source edge index type, not a replacement. -/
@[simp] theorem canonicalize_edgeShape (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (canonicalize representation atomEquiv edgeEquiv bandEquiv).edgeShape =
      representation.edgeIndex := rfl

/-- The canonical band shape is the source band index type, not a replacement. -/
@[simp] theorem canonicalize_bandShape (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (canonicalize representation atomEquiv edgeEquiv bandEquiv).bandShape =
      representation.bandIndex := rfl

/-- The decoded representation preserves the path presence tag literally. -/
@[simp] theorem canonicalDecode_pathPresent
    (canonical : CanonicalOrganicMolecularRepresentation V) :
    (canonicalDecode canonical).pathPresent = canonical.pathPresent := rfl

/-- The decoded representation preserves the band presence tag literally. -/
@[simp] theorem canonicalDecode_bandPresent
    (canonical : CanonicalOrganicMolecularRepresentation V) :
    (canonicalDecode canonical).bandPresent = canonical.bandPresent := rfl

/-- The decoded representation's edge index type is the retained source shape. -/
@[simp] theorem canonicalDecode_edgeIndex
    (canonical : CanonicalOrganicMolecularRepresentation V) :
    (canonicalDecode canonical).edgeIndex = canonical.edgeShape := rfl

/-- The decoded representation's band index type is the retained source shape. -/
@[simp] theorem canonicalDecode_bandIndex
    (canonical : CanonicalOrganicMolecularRepresentation V) :
    (canonicalDecode canonical).bandIndex = canonical.bandShape := rfl

/-! ## The real state-level inverse -/

/-- Decoding the canonical state returns the source representation state exactly.  This is the
actual `decodeDescription` / `encodeDescription` inverse applied at the assembled state. -/
theorem canonicalDecode_state_canonicalize
    (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (canonicalDecode
        (canonicalize representation atomEquiv edgeEquiv bandEquiv)).state =
      representation.state := by
  simp only [canonicalDecode, canonicalize, decodeDescription_encodeDescription]

/-- The same inverse expressed on the canonical record's own state field: the canonical state is
exactly the actual `encodeDescription` of the assembled source state. -/
theorem canonicalize_state_eq_encodeDescription
    (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (canonicalize representation atomEquiv edgeEquiv bandEquiv).state =
      (letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
       letI : Fintype representation.bandIndex := representation.fintypeBandIndex
       encodeDescription atomEquiv edgeEquiv bandEquiv representation.state) := rfl

/-! ### Concrete channel projections of the actual codec

The canonical state is definitionally the actual `encodeDescription` of the source state, so each
channel is literally the relabelled source channel.  These projections make the graph atom data,
the path family at `Fin` edge indices and the band family at `Fin` band indices explicit. -/

/-- The canonical graph is the source graph relabelled by the atom enumeration. -/
theorem canonicalize_state_graph (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
     letI : Fintype representation.bandIndex := representation.fintypeBandIndex
     (canonicalize representation atomEquiv edgeEquiv bandEquiv).state.graph =
       relabelGraph atomEquiv representation.state.graph) := by
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  rfl

/-- Every canonical `Fin` edge index is exactly the source edge index read through the explicit
edge equivalence, with the whole path annotation relabelled by the atom codec. -/
theorem canonicalize_state_paths (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex))
    (index : Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex)) :
    (letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
     letI : Fintype representation.bandIndex := representation.fintypeBandIndex
     (canonicalize representation atomEquiv edgeEquiv bandEquiv).state.paths index =
       relabelPathAnnotation atomEquiv
         (representation.state.paths (edgeEquiv.symm index))) := by
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  rfl

/-- Every canonical `Fin` band index is exactly the source band index read through the explicit
band equivalence, with the whole band attachment relabelled by the atom codec. -/
theorem canonicalize_state_bandFamily (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex))
    (index : Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
     letI : Fintype representation.bandIndex := representation.fintypeBandIndex
     (canonicalize representation atomEquiv edgeEquiv bandEquiv).state.bandFamily index =
       relabelBandAttachment atomEquiv
         (representation.state.bandFamily (bandEquiv.symm index))) := by
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  rfl

/-- The ordered frame channel of the canonical state is the source frame list relabelled
elementwise by the same atom codec, through the existing `encodeDescription_frames` theorem. -/
theorem canonicalize_state_frames (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    (letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
     letI : Fintype representation.bandIndex := representation.fintypeBandIndex
     (canonicalize representation atomEquiv edgeEquiv bandEquiv).state.frames =
       representation.state.frames.map (relabelFrameAnnotation atomEquiv)) := by
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  rw [canonicalize_state_eq_encodeDescription]
  exact encodeDescription_frames atomEquiv edgeEquiv bandEquiv representation.state

/-! ## Extensionality of the assembled representation

The upstream representation is a structure with dependent type/index fields.  This lemma records
that two representations with the same presence tags, the same effective index types and
heterogeneously equal states are equal; the path-validity fields are proposition-valued functions
and are identified by proof irrelevance.  It is used for the canonical representation inverse. -/

/-- Extensionality for `OrganicMolecularRepresentation` across its dependent index-type fields. -/
theorem organicMolecularRepresentation_extEq
    {first second : OrganicMolecularRepresentation V}
    (pathPresent : first.pathPresent = second.pathPresent)
    (edgeIndex : first.edgeIndex = second.edgeIndex)
    (bandPresent : first.bandPresent = second.bandPresent)
    (bandIndex : first.bandIndex = second.bandIndex)
    (state : HEq first.state second.state) : first = second := by
  obtain ⟨firstPath, firstEdge, firstFintypeEdge, firstBand, firstBandIndex,
    firstFintypeBand, firstState, firstValid⟩ := first
  obtain ⟨secondPath, secondEdge, secondFintypeEdge, secondBand, secondBandIndex,
    secondFintypeBand, secondState, secondValid⟩ := second
  dsimp only at pathPresent edgeIndex bandPresent bandIndex state
  cases pathPresent
  cases edgeIndex
  cases bandPresent
  cases bandIndex
  have fintypeEdge : firstFintypeEdge = secondFintypeEdge := Subsingleton.elim _ _
  have fintypeBand : firstFintypeBand = secondFintypeBand := Subsingleton.elim _ _
  cases fintypeEdge
  cases fintypeBand
  have stateEq : firstState = secondState := eq_of_heq state
  cases stateEq
  have validEq : firstValid = secondValid := by
    funext present
    exact Subsingleton.elim _ _
  cases validEq
  rfl

/-! ## The representation-level inverse -/

/-- **Representation inverse.**  Canonically encoding a representation and then decoding the
canonical record returns the original representation exactly, for every atom enumeration and every
edge/band equivalence. -/
theorem canonicalDecode_canonicalize (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : representation.edgeIndex ≃
      Fin (@Fintype.card representation.edgeIndex representation.fintypeEdgeIndex))
    (bandEquiv : representation.bandIndex ≃
      Fin (@Fintype.card representation.bandIndex representation.fintypeBandIndex)) :
    canonicalDecode (canonicalize representation atomEquiv edgeEquiv bandEquiv) = representation := by
  apply organicMolecularRepresentation_extEq
  · rfl
  · rfl
  · rfl
  · rfl
  · exact heq_of_eq
      (canonicalDecode_state_canonicalize representation atomEquiv edgeEquiv bandEquiv)

/-- The canonical `Fin` encoding has the same representation-level inverse. -/
theorem canonicalDecode_canonicalizeFin (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V)) :
    canonicalDecode (canonicalizeFin representation atomEquiv) = representation := by
  unfold canonicalizeFin
  exact canonicalDecode_canonicalize representation atomEquiv _ _

/-- Canonical encoding is injective on representations (with the canonical `Fin` edge/band
equivalences and a fixed atom enumeration). -/
theorem canonicalizeFin_injective (atomEquiv : V ≃ Fin (Fintype.card V)) :
    Function.Injective (fun representation => canonicalizeFin representation atomEquiv) := by
  intro first second equal
  have applied : canonicalDecode (canonicalizeFin first atomEquiv) =
      canonicalDecode (canonicalizeFin second atomEquiv) := congrArg canonicalDecode equal
  rwa [canonicalDecode_canonicalizeFin, canonicalDecode_canonicalizeFin] at applied

/-! ## Canonical assembly of an independently supplied request -/

/-- The canonical finite assembly of an independently supplied molecular-evidence request.  It is
the canonical encoding of the actual upstream `assemble` output. -/
noncomputable def canonicalAssemble (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) : CanonicalOrganicMolecularRepresentation V :=
  canonicalizeFin (assemble request) enumeration

/-- The canonical assembly decodes to the actual assembled representation. -/
theorem canonicalDecode_canonicalAssemble (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    canonicalDecode (canonicalAssemble enumeration request) = assemble request :=
  canonicalDecode_canonicalizeFin (assemble request) enumeration

/-- The canonical assembly preserves the path presence tag of the actual assembly. -/
theorem canonicalAssemble_pathPresent (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).pathPresent = (assemble request).pathPresent := rfl

/-- The canonical assembly preserves the band presence tag of the actual assembly. -/
theorem canonicalAssemble_bandPresent (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).bandPresent = (assemble request).bandPresent := rfl

/-- The canonical assembly carries the actual `encodeDescription` of the assembled state. -/
theorem canonicalAssemble_state (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).state =
      (letI : Fintype (assemble request).edgeIndex := (assemble request).fintypeEdgeIndex
       letI : Fintype (assemble request).bandIndex := (assemble request).fintypeBandIndex
       encodeDescription enumeration (Fintype.equivFin (assemble request).edgeIndex)
         (Fintype.equivFin (assemble request).bandIndex) (assemble request).state) := by
  simp only [canonicalAssemble, canonicalizeFin, canonicalize]

/-! ## Exact recovery of the independently supplied request -/

/-- **Source decode of the canonical assembly.**  Applying the actual upstream `decode` to the
decoded canonical assembly returns the original independently supplied request, including both
optional channels and every correlation between them. -/
theorem decode_canonicalAssemble (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    decode (canonicalDecode (canonicalAssemble enumeration request)) = request := by
  rw [canonicalDecode_canonicalAssemble, decode_assemble]

/-- The decoded canonical assembly recovers the exact optional path channel: `none` and
`some` (including a supplied empty family) remain distinct. -/
theorem decodedPaths?_canonicalAssemble (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    decodedPaths? (canonicalDecode (canonicalAssemble enumeration request)) = request.paths? := by
  have recovered := congrArg OrganicMolecularEvidence.paths?
    (decode_canonicalAssemble enumeration request)
  simpa [decode] using recovered

/-- The decoded canonical assembly recovers the exact optional band channel: `none` and
`some` (including a supplied empty band family) remain distinct. -/
theorem decodedBands?_canonicalAssemble (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    decodedBands? (canonicalDecode (canonicalAssemble enumeration request)) = request.bands? := by
  have recovered := congrArg OrganicMolecularEvidence.bands?
    (decode_canonicalAssemble enumeration request)
  simpa [decode] using recovered

/-- The path presence tag of any representation is exactly whether its decoded path option is
`some`.  In particular `none` and a supplied empty family remain distinct. -/
theorem representation_pathPresent_iff (representation : OrganicMolecularRepresentation V) :
    representation.pathPresent = true ↔ (decodedPaths? representation).isSome := by
  cases present : representation.pathPresent with
  | false =>
      rw [decodedPaths?_eq_none representation present]
      simp [present]
  | true =>
      rw [decodedPaths?_eq_some representation present]
      simp [present]

/-- The band presence tag of any representation is exactly whether its decoded band option is
`some`.  In particular `none` and a supplied empty band family remain distinct. -/
theorem representation_bandPresent_iff (representation : OrganicMolecularRepresentation V) :
    representation.bandPresent = true ↔ (decodedBands? representation).isSome := by
  cases present : representation.bandPresent with
  | false =>
      rw [decodedBands?_eq_none representation present]
      simp [present]
  | true =>
      rw [decodedBands?_eq_some representation present]
      simp [present]

/-- The canonical assembly's path presence tag is exactly the presence of the supplied path
option: `none` is tagged absent and `some family` (even an empty family) is tagged present. -/
theorem canonicalAssemble_pathPresent_iff_isSome
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).pathPresent = true ↔ request.paths?.isSome := by
  rw [canonicalAssemble_pathPresent]
  exact (representation_pathPresent_iff (assemble request)).trans (by rw [assemble_paths?])

/-- The canonical assembly's band presence tag is exactly the presence of the supplied band
option: `none` is tagged absent and `some bands` (even an empty band family) is tagged
present. -/
theorem canonicalAssemble_bandPresent_iff_isSome
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).bandPresent = true ↔ request.bands?.isSome := by
  rw [canonicalAssemble_bandPresent]
  exact (representation_bandPresent_iff (assemble request)).trans (by rw [assemble_bands?])

/-- The canonical assembly of a request is injective: equal canonical records at the same atom
enumeration arise only from equal independently supplied requests. -/
theorem canonicalAssemble_injective (enumeration : V ≃ Fin (Fintype.card V)) :
    Function.Injective (canonicalAssemble enumeration) := by
  intro first second equal
  have applied : decode (canonicalDecode (canonicalAssemble enumeration first)) =
      decode (canonicalDecode (canonicalAssemble enumeration second)) :=
    congrArg (fun canonical => decode (canonicalDecode canonical)) equal
  rwa [decode_canonicalAssemble, decode_canonicalAssemble] at applied

/-! ## Arbitrary correlated sets of requests -/

/-- **Set-image recovery.**  For every set of independently supplied requests, decoding the
decoded canonical assembly of that set recovers exactly the original set.  Because the whole
correlated request is recovered pointwise, no correlation between the graph, conformation,
electronic, path, band, drawing and annotation channels is lost. -/
theorem decode_canonicalDecode_image_canonicalAssemble_image
    (enumeration : V ≃ Fin (Fintype.card V))
    (requests : Set (OrganicMolecularEvidence V)) :
    (fun request => decode (canonicalDecode (canonicalAssemble enumeration request))) '' requests =
      requests := by
  have pointwise : (fun request => decode (canonicalDecode (canonicalAssemble enumeration request))) =
      id := funext (decode_canonicalAssemble enumeration)
  rw [pointwise, Set.image_id]

/-- The same set-image recovery written with the three explicit image stages: the canonical
assembly, its representation decoder, and the upstream request decoder. -/
theorem decode_image_canonicalDecode_image_canonicalAssemble_image
    (enumeration : V ≃ Fin (Fintype.card V))
    (requests : Set (OrganicMolecularEvidence V)) :
    decode '' (canonicalDecode '' (canonicalAssemble enumeration '' requests)) = requests := by
  rw [Set.image_image, Set.image_image]
  exact decode_canonicalDecode_image_canonicalAssemble_image enumeration requests

end

end OrganicStereoMolecularCanonicalTransport

end TetraStereo.OneCenter
