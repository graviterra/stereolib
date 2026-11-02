import TetraStereo.OneCenter.OrganicStereoSourceGlyphIngress

set_option autoImplicit false

namespace TetraStereo.OneCenter

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport
open OrganicStereoSpatialSupportMolecularAssembly

variable {V W : Type}

/-!
# Source-supplied bond-crossing ingress

This leaf carries the remaining actual ST-3 drawing payload
`IUPACDrawing2006.ST3.BondCrossing` through the existing drawing-convention channel.

The supplied record is an *ordered pair of supplied glyph occurrences*.  `SuppliedBondCrossing`
stores the two positions as `Fin glyphs.length` and the complete source crossing record.  The
record is compiled to `BondCrossingGlyph` by copying the source `Bool` discontinuity flag, the
exact rational `discontinuityWidthRatio` and the ordering-conflict flag literally.  The two `Nat`
cue indices are computed from the actual last-source cue prefix length and the supplied glyph
positions; they are positions in the ordered convention cue list and are never atom labels or
interaction indices.  No `UnambiguousCrossing` condition, recommendation, derived depth or
chemical-applicability judgment is required or invented.

Attachment first uses the existing `attachSourceGlyphs`, preserving every non-convention field,
the convention-record prefix and the old cue-list prefix in the last record. It then appends the
compiled crossing cues with `appendCues`/`attachCuesToLast`. A nonempty append merges the prior
last-record states `cues? = none` and `cues? = some []`; this module recovers the augmented source,
not that pre-attachment distinction. The separate lossless batch adapter preserves independently
supplied prior records unchanged. The main source-level results identify
the exact resulting cue list, prove every stored cue index is bounded and looks up the
corresponding supplied glyph (including repeated equal glyphs at distinct positions), and retain
both actual interaction occurrences and endpoints.

The canonical readback uses the *actual* `canonicalAssemble`, `canonicalDecode` and `decodedCore`.
The common atom enumeration maps both supplied glyphs and both cue indices are unchanged; the
literal source crossing record is recovered, and the decoded core recovers the augmented source
request (and hence the literal source-labelled crossing cue) without any original source supplied
to the decoder.  Atom references at the canonical output are mapped by exactly the same
enumeration used by the graph encoding.

This is supplied drawing provenance only: it is not a depth recognizer, not a recommendation
oracle, and not a chemical-applicability oracle.
-/

/-! ## The ordered cue sequence of the last convention source -/

/-- The cue sequence carried by the last record of a convention channel.  An empty channel has an
empty sequence.  This is the actual ordered list in which crossing cue indices live. -/
def channelLastCues (channel : ConventionChannel V) : List (ConventionCue V) :=
  match channel.getLast? with
  | none => []
  | some source => source.cues?.getD []

@[simp] theorem channelLastCues_nil :
    channelLastCues ([] : ConventionChannel V) = [] := rfl

namespace OrganicConventionSource

/-- Exact cue list after any append, uniformly including the identity append.  This is the
ordered-list equation used for multiplicity and duplicate retention. -/
@[simp] theorem appendCues_getD (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) :
    (source.appendCues extra).cues?.getD [] = source.cues?.getD [] ++ extra := by
  cases extra with
  | nil => simp
  | cons head tail => rfl

/-- The appended record is present after a nonempty append, and its cue list is exactly the old
list followed by the appended list. -/
theorem appendCues_cues?_eq (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) (nonempty : extra ≠ []) :
    (source.appendCues extra).cues? =
      some (source.cues?.getD [] ++ extra) := by
  cases extra with
  | nil => exact absurd rfl nonempty
  | cons head tail => rfl

end OrganicConventionSource

namespace ConventionChannel

/-- Attaching an extra cue list never changes the convention records before the last one, for
every extra list (the empty append is the identity). -/
theorem attachCuesToLast_dropLast (extra : List (ConventionCue V))
    (channel : ConventionChannel V) :
    (attachCuesToLast extra channel).dropLast = channel.dropLast := by
  cases extra with
  | nil => simp
  | cons head tail =>
      have nonempty : head :: tail ≠ [] := by simp
      cases observed : channel.getLast? with
      | none =>
          rw [attachCuesToLast_of_getLast?_none (head :: tail) channel nonempty observed]
          have emptyChannel : channel = [] := List.getLast?_eq_none_iff.mp observed
          rw [emptyChannel]
          rfl
      | some last =>
          exact attachCuesToLast_dropLast_of_some (head :: tail) channel
            (last := last) nonempty observed

end ConventionChannel

/-- The exact cue sequence after appending to the last source record. -/
theorem channelLastCues_attachCuesToLast (extra : List (ConventionCue V))
    (channel : ConventionChannel V) :
    channelLastCues (ConventionChannel.attachCuesToLast extra channel) =
      channelLastCues channel ++ extra := by
  cases extra with
  | nil => simp
  | cons head tail =>
      have nonempty : head :: tail ≠ [] := by simp
      cases observed : channel.getLast? with
      | none =>
          rw [ConventionChannel.attachCuesToLast_of_getLast?_none (head :: tail) channel
            nonempty observed]
          simp [channelLastCues, observed]
      | some last =>
          rw [ConventionChannel.attachCuesToLast_of_getLast? (head :: tail) channel
            (last := last) nonempty observed]
          simp [channelLastCues, observed]

/-- Encoding a channel applies the one common atom equivalence to every cue of every record and
therefore to the last ordered cue sequence, without changing order or multiplicity. -/
theorem channelLastCues_encode (e : V ≃ W)
    (channel : ConventionChannel V) :
    channelLastCues (ConventionChannel.encode e channel) =
      (channelLastCues channel).map (ConventionCue.mapAtom e) := by
  unfold channelLastCues
  rw [ConventionChannel.encode_getLast?]
  cases observed : channel.getLast? with
  | none => simp
  | some last =>
      simp only [Option.map_some]
      rw [OrganicConventionSource.encode_cues?]
      cases cuesObserved : last.cues? with
      | none => simp
      | some cues => simp

/-! ## Supplied crossing records -/

section Crossing

variable [DecidableEq V] [Fintype V]

/-- A source-supplied crossing between two ordered supplied glyph occurrences.  The two positions
are bounded by the supplied glyph list; the complete ST-3 crossing record is retained literally.
No stereochemical or drawing recommendation is required. -/
structure SuppliedBondCrossing {graph : FiniteAtomInteractionHypergraph V}
    (glyphs : List (SuppliedBondGlyph graph)) where
  /-- Position of the first supplied glyph occurrence in the ordered glyph list. -/
  first : Fin glyphs.length
  /-- Position of the second supplied glyph occurrence in the ordered glyph list. -/
  second : Fin glyphs.length
  /-- The complete source ST-3 crossing record. -/
  crossing : IUPACDrawing2006.ST3.BondCrossing

section Compile

variable {graph : FiniteAtomInteractionHypergraph V}

/-- Compile one supplied crossing to the retention-layer crossing glyph.  The cue indices are
positions in the containing ordered convention cue list, computed as the actual last-source cue
prefix length plus the supplied glyph positions.  Both glyph payloads and the literal source
crossing record are copied. -/
def compileSuppliedCrossing (glyphs : List (SuppliedBondGlyph graph))
    (prefixLength : Nat) (crossing : SuppliedBondCrossing glyphs) :
    BondCrossingGlyph V where
  firstCueIndex := prefixLength + crossing.first.val
  secondCueIndex := prefixLength + crossing.second.val
  first := (glyphs.get crossing.first).toBondGlyph
  second := (glyphs.get crossing.second).toBondGlyph
  crossing := crossing.crossing

@[simp] theorem compileSuppliedCrossing_firstCueIndex
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).firstCueIndex =
      prefixLength + crossing.first.val := rfl

@[simp] theorem compileSuppliedCrossing_secondCueIndex
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).secondCueIndex =
      prefixLength + crossing.second.val := rfl

@[simp] theorem compileSuppliedCrossing_first
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).first =
      (glyphs.get crossing.first).toBondGlyph := rfl

@[simp] theorem compileSuppliedCrossing_second
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).second =
      (glyphs.get crossing.second).toBondGlyph := rfl

@[simp] theorem compileSuppliedCrossing_crossing
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).crossing =
      crossing.crossing := rfl

/-- Both cue indices are exactly the computed positions, and they are not atom labels. -/
theorem compileSuppliedCrossing_cue_indices
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).firstCueIndex =
        prefixLength + crossing.first.val ∧
    (compileSuppliedCrossing glyphs prefixLength crossing).secondCueIndex =
        prefixLength + crossing.second.val :=
  ⟨rfl, rfl⟩

/-- The written first/second position order is retained as cue-index order. -/
theorem compileSuppliedCrossing_index_order
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs)
    (ordered : crossing.first.val < crossing.second.val) :
    (compileSuppliedCrossing glyphs prefixLength crossing).firstCueIndex <
      (compileSuppliedCrossing glyphs prefixLength crossing).secondCueIndex := by
  simp only [compileSuppliedCrossing_firstCueIndex, compileSuppliedCrossing_secondCueIndex]
  omega

/-- The compiled crossing cue takes no single-atom focus; its references are carried by both
glyphs.  (The two indices remain cue positions.) -/
theorem compileSuppliedCrossingCue_atom?_none
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (ConventionCue.bondCrossing
      (compileSuppliedCrossing glyphs prefixLength crossing)).atom? = none :=
  ConventionCue.atom?_bondCrossing _

/-- The compiled crossing cue references both glyph endpoint lists in the written order: first
glyph, then second glyph. -/
theorem compileSuppliedCrossingCue_atomReferences
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (ConventionCue.bondCrossing
      (compileSuppliedCrossing glyphs prefixLength crossing)).atomReferences =
      (glyphs.get crossing.first).toBondGlyph.atomReferences ++
        (glyphs.get crossing.second).toBondGlyph.atomReferences := by
  rw [ConventionCue.atomReferences_bondCrossing]
  simp only [compileSuppliedCrossing_first, compileSuppliedCrossing_second]

/-- The compiled first glyph has exactly the supplied first occurrence index and written
endpoints, and both endpoints are participants of that actual occurrence. -/
theorem compileSuppliedCrossing_first_occurrence
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).first.interactionIndex =
        (glyphs.get crossing.first).interactionIndex.val ∧
    (compileSuppliedCrossing glyphs prefixLength crossing).first.source =
        (glyphs.get crossing.first).source ∧
    (compileSuppliedCrossing glyphs prefixLength crossing).first.target =
        (glyphs.get crossing.first).target ∧
    (glyphs.get crossing.first).source ∈
        (graph.interactions.get (glyphs.get crossing.first).interactionIndex).1 ∧
    (glyphs.get crossing.first).target ∈
        (graph.interactions.get (glyphs.get crossing.first).interactionIndex).1 :=
  ⟨rfl, rfl, rfl,
    (glyphs.get crossing.first).source_mem_occurrence,
    (glyphs.get crossing.first).target_mem_occurrence⟩

/-- The compiled second glyph has exactly the supplied second occurrence index and written
endpoints, and both endpoints are participants of that actual occurrence. -/
theorem compileSuppliedCrossing_second_occurrence
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).second.interactionIndex =
        (glyphs.get crossing.second).interactionIndex.val ∧
    (compileSuppliedCrossing glyphs prefixLength crossing).second.source =
        (glyphs.get crossing.second).source ∧
    (compileSuppliedCrossing glyphs prefixLength crossing).second.target =
        (glyphs.get crossing.second).target ∧
    (glyphs.get crossing.second).source ∈
        (graph.interactions.get (glyphs.get crossing.second).interactionIndex).1 ∧
    (glyphs.get crossing.second).target ∈
        (graph.interactions.get (glyphs.get crossing.second).interactionIndex).1 :=
  ⟨rfl, rfl, rfl,
    (glyphs.get crossing.second).source_mem_occurrence,
    (glyphs.get crossing.second).target_mem_occurrence⟩

/-- All three source crossing fields are retained literally, with no recommendation or
`UnambiguousCrossing` hypothesis. -/
theorem compileSuppliedCrossing_crossing_fields
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : SuppliedBondCrossing glyphs) :
    (compileSuppliedCrossing glyphs prefixLength crossing).crossing.backBondDiscontinuous =
        crossing.crossing.backBondDiscontinuous ∧
    (compileSuppliedCrossing glyphs prefixLength crossing).crossing.discontinuityWidthRatio =
        crossing.crossing.discontinuityWidthRatio ∧
    (compileSuppliedCrossing glyphs prefixLength crossing).crossing.orderingConflictsWithVerticalDepthCue =
        crossing.crossing.orderingConflictsWithVerticalDepthCue :=
  ⟨rfl, rfl, rfl⟩

/-- Two compiled crossings coincide only when both supplied positions and the literal crossing
record coincide.  This is the multiplicity statement for crossing records. -/
theorem compileSuppliedCrossing_eq_imp
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    {first second : SuppliedBondCrossing glyphs}
    (equal : compileSuppliedCrossing glyphs prefixLength first =
      compileSuppliedCrossing glyphs prefixLength second) :
    first.first = second.first ∧
    first.second = second.second ∧
    first.crossing = second.crossing := by
  have firstCue := congrArg BondCrossingGlyph.firstCueIndex equal
  have secondCue := congrArg BondCrossingGlyph.secondCueIndex equal
  have crossingEqual := congrArg BondCrossingGlyph.crossing equal
  simp only [compileSuppliedCrossing_firstCueIndex, compileSuppliedCrossing_secondCueIndex,
    compileSuppliedCrossing_crossing] at firstCue secondCue crossingEqual
  exact ⟨Fin.ext (Nat.add_left_cancel firstCue),
    Fin.ext (Nat.add_left_cancel secondCue), crossingEqual⟩

/-- Compilation of crossing records is injective: distinct supplied crossing records remain
distinct retained cues. -/
theorem compileSuppliedCrossing_injective
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat) :
    Function.Injective (compileSuppliedCrossing glyphs prefixLength) := by
  intro first second equal
  obtain ⟨hfirst, hsecond, hcrossing⟩ :=
    compileSuppliedCrossing_eq_imp glyphs prefixLength equal
  cases first with
  | mk firstPosition secondPosition crossing =>
      cases second with
      | mk firstPosition' secondPosition' crossing' =>
          simp only at hfirst hsecond hcrossing
          cases hfirst
          cases hsecond
          cases hcrossing
          rfl

/-- Compile an ordered list of supplied crossing records to retained crossing glyphs. -/
def compileSuppliedCrossings (glyphs : List (SuppliedBondGlyph graph))
    (prefixLength : Nat) (crossings : List (SuppliedBondCrossing glyphs)) :
    List (BondCrossingGlyph V) :=
  crossings.map (compileSuppliedCrossing glyphs prefixLength)

/-- Compile an ordered list of supplied crossing records directly to convention cues. -/
def compileSuppliedCrossingCues (glyphs : List (SuppliedBondGlyph graph))
    (prefixLength : Nat) (crossings : List (SuppliedBondCrossing glyphs)) :
    List (ConventionCue V) :=
  crossings.map fun crossing =>
    ConventionCue.bondCrossing (compileSuppliedCrossing glyphs prefixLength crossing)

@[simp] theorem compileSuppliedCrossings_length
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (compileSuppliedCrossings glyphs prefixLength crossings).length = crossings.length := by
  simp [compileSuppliedCrossings]

@[simp] theorem compileSuppliedCrossingCues_length
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (compileSuppliedCrossingCues glyphs prefixLength crossings).length = crossings.length := by
  simp [compileSuppliedCrossingCues]

/-- Exact ordered lookup of a compiled crossing, position by position. -/
theorem compileSuppliedCrossings_get?_bounded
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (SuppliedBondCrossing glyphs)) (index : Nat)
    (bound : index < crossings.length) :
    (compileSuppliedCrossings glyphs prefixLength crossings)[index]? =
      some (compileSuppliedCrossing glyphs prefixLength (crossings[index]'bound)) := by
  unfold compileSuppliedCrossings
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  rfl

/-- Exact ordered lookup of a compiled crossing cue, position by position. -/
theorem compileSuppliedCrossingCues_get?_bounded
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (SuppliedBondCrossing glyphs)) (index : Nat)
    (bound : index < crossings.length) :
    (compileSuppliedCrossingCues glyphs prefixLength crossings)[index]? =
      some (ConventionCue.bondCrossing
        (compileSuppliedCrossing glyphs prefixLength (crossings[index]'bound))) := by
  unfold compileSuppliedCrossingCues
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  rfl

/-- Membership in the compiled crossing-cue list, with the exact supplied witness. -/
theorem compileSuppliedCrossingCues_mem_iff
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (SuppliedBondCrossing glyphs)) (cue : ConventionCue V) :
    cue ∈ compileSuppliedCrossingCues glyphs prefixLength crossings ↔
      ∃ supplied ∈ crossings,
        ConventionCue.bondCrossing
          (compileSuppliedCrossing glyphs prefixLength supplied) = cue := by
  unfold compileSuppliedCrossingCues
  simp [List.mem_map]

end Compile

/-! ## Attachment to actual molecular evidence -/

/-- Append typed cues to the last existing convention record, or create a fresh record when the
channel is empty.  The empty append is the identity.  This is the generic cue-level operation
underlying the crossing attachment. -/
def attachConventionCues (request : OrganicMolecularEvidence V)
    (extra : List (ConventionCue V)) : OrganicMolecularEvidence V :=
  match extra with
  | [] => request
  | _ =>
      { request with
        conventions :=
          ConventionChannel.attachCuesToLast extra request.conventions }

@[simp] theorem attachConventionCues_nil (request : OrganicMolecularEvidence V) :
    attachConventionCues request [] = request := rfl

@[simp] theorem attachConventionCues_conventions (request : OrganicMolecularEvidence V)
    (extra : List (ConventionCue V)) :
    (attachConventionCues request extra).conventions =
      ConventionChannel.attachCuesToLast extra request.conventions := by
  cases extra <;> rfl

/-- Bundled statement: appending cues changes no non-convention evidence field. -/
theorem attachConventionCues_preserves_nonconvention
    (request : OrganicMolecularEvidence V) (extra : List (ConventionCue V)) :
    (attachConventionCues request extra).graph = request.graph ∧
    (attachConventionCues request extra).conformation = request.conformation ∧
    (attachConventionCues request extra).rationalPositions? = request.rationalPositions? ∧
    (attachConventionCues request extra).electronic? = request.electronic? ∧
    (attachConventionCues request extra).paths? = request.paths? ∧
    (attachConventionCues request extra).bands? = request.bands? ∧
    (attachConventionCues request extra).roles = request.roles ∧
    (attachConventionCues request extra).diagram? = request.diagram? ∧
    (attachConventionCues request extra).diagramPartial? = request.diagramPartial? ∧
    (attachConventionCues request extra).diagramIncidence = request.diagramIncidence ∧
    (attachConventionCues request extra).fragments = request.fragments ∧
    (attachConventionCues request extra).cages = request.cages ∧
    (attachConventionCues request extra).residueLedger? = request.residueLedger? ∧
    (attachConventionCues request extra).frames = request.frames := by
  cases extra with
  | nil => simp
  | cons head tail => simp [attachConventionCues]

/-- The actual cue prefix length of the original last source record.  Crossing cue indices are
computed from this number, never from atom labels. -/
def lastSourceCuePrefixLength (request : OrganicMolecularEvidence V) : Nat :=
  (channelLastCues request.conventions).length

/-- Attach a supplied glyph batch and then the supplied crossing cues to a real evidence request.
The glyph batch goes through the existing `attachSourceGlyphs`; the crossing cues are appended to
the resulting last source record using the actual existing cue machinery. -/
def attachSourceCrossings (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) : OrganicMolecularEvidence V :=
  { attachSourceGlyphs request glyphs with
    conventions :=
      ConventionChannel.attachCuesToLast
        (compileSuppliedCrossingCues glyphs (lastSourceCuePrefixLength request) crossings)
        (attachSourceGlyphs request glyphs).conventions }

/-- The exact augmented convention channel. -/
@[simp] theorem attachSourceCrossings_conventions (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (attachSourceCrossings request glyphs crossings).conventions =
      ConventionChannel.attachCuesToLast
        (compileSuppliedCrossingCues glyphs (lastSourceCuePrefixLength request) crossings)
        (attachSourceGlyphs request glyphs).conventions := rfl

/-- No crossing records means that the crossing step is exactly the glyph step. -/
@[simp] theorem attachSourceCrossings_nil_crossings (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    attachSourceCrossings request glyphs [] = attachSourceGlyphs request glyphs := by
  simp only [attachSourceCrossings, compileSuppliedCrossingCues, List.map_nil,
    ConventionChannel.attachCuesToLast_nil]

/-- No supplied glyphs and no crossing records means no change at all. -/
@[simp] theorem attachSourceCrossings_nil_nil (request : OrganicMolecularEvidence V) :
    attachSourceCrossings request [] [] = request := by
  simp [attachSourceCrossings, attachSourceGlyphs_nil, compileSuppliedCrossingCues]

/-- The actual original cue prefix length, definitionally. -/
@[simp] theorem lastSourceCuePrefixLength_eq (request : OrganicMolecularEvidence V) :
    lastSourceCuePrefixLength request =
      (channelLastCues request.conventions).length := rfl

/-- The exact final ordered cue sequence: the original last-source cues, then the compiled
supplied glyph cues, then the compiled crossing cues. -/
theorem channelLastCues_attachSourceCrossings (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    channelLastCues (attachSourceCrossings request glyphs crossings).conventions =
      (channelLastCues request.conventions ++
        compileSuppliedCues request.graph glyphs) ++
        compileSuppliedCrossingCues glyphs (lastSourceCuePrefixLength request) crossings := by
  rw [attachSourceCrossings_conventions, attachSourceGlyphs_conventions,
    channelLastCues_attachCuesToLast, channelLastCues_attachCuesToLast]

/-- Exact ordered lookup of every supplied glyph after crossing attachment.  This includes
repeated equal glyphs at distinct supplied positions, which appear at distinct cue positions. -/
theorem attachSourceCrossings_slot_lookup (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (slot : Fin glyphs.length) :
    (channelLastCues (attachSourceCrossings request glyphs crossings).conventions)[lastSourceCuePrefixLength request + slot.val]? =
      some (ConventionCue.bondGlyph (glyphs.get slot).toBondGlyph) := by
  have slotBound : slot.val < glyphs.length := slot.isLt
  rw [channelLastCues_attachSourceCrossings]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, compileSuppliedCues_length, lastSourceCuePrefixLength]
    exact Nat.add_lt_add_left slot.isLt _)]
  rw [List.getElem?_append_right (by
    simp only [lastSourceCuePrefixLength]
    exact Nat.le_add_right _ _)]
  have hsub : lastSourceCuePrefixLength request + slot.val -
      (channelLastCues request.conventions).length = slot.val := by
    simp only [lastSourceCuePrefixLength]
    exact Nat.add_sub_cancel_left _ _
  rw [hsub]
  simpa [SuppliedBondGlyph.toCue] using
    compileSuppliedCues_get?_bounded request.graph glyphs slot.val slot.isLt

/-- A successful bounded lookup gives a length bound. -/
theorem nat_lt_length_of_getElem?_some {α : Type*} {l : List α} (index : Nat) {value : α}
    (observed : l[index]? = some value) : index < l.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp observed
  exact bound

/-- Every supplied glyph cue position is bounded in the final cue list. -/
theorem attachSourceCrossings_slot_bounded (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (slot : Fin glyphs.length) :
    lastSourceCuePrefixLength request + slot.val <
      (channelLastCues (attachSourceCrossings request glyphs crossings).conventions).length :=
  nat_lt_length_of_getElem?_some _
    (attachSourceCrossings_slot_lookup request glyphs crossings slot)

/-- Exact lookup of one compiled crossing cue at its computed final cue position. -/
theorem attachSourceCrossings_crossingCue_lookup (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (channelLastCues (attachSourceCrossings request glyphs crossings).conventions)[lastSourceCuePrefixLength request + glyphs.length + position.val]? =
      some (ConventionCue.bondCrossing
        (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position))) := by
  rw [channelLastCues_attachSourceCrossings]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, compileSuppliedCues_length, lastSourceCuePrefixLength]
    exact Nat.le_add_right _ _)]
  have hsub : lastSourceCuePrefixLength request + glyphs.length + position.val -
      (channelLastCues request.conventions ++ compileSuppliedCues request.graph glyphs).length =
      position.val := by
    simp only [List.length_append, compileSuppliedCues_length, lastSourceCuePrefixLength]
    exact Nat.add_sub_cancel_left _ _
  rw [hsub]
  simpa using compileSuppliedCrossingCues_get?_bounded glyphs
    (lastSourceCuePrefixLength request) crossings position.val position.isLt

/-- The stored first cue index looks up exactly the first supplied glyph. -/
theorem attachSourceCrossings_firstCueIndex_lookup (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (channelLastCues (attachSourceCrossings request glyphs crossings).conventions)[(compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position)).firstCueIndex]? =
      some (ConventionCue.bondGlyph
        (glyphs.get (crossings.get position).first).toBondGlyph) := by
  rw [compileSuppliedCrossing_firstCueIndex]
  exact attachSourceCrossings_slot_lookup request glyphs crossings
    (crossings.get position).first

/-- The stored first cue index of a crossing is bounded in the final cue list. -/
theorem attachSourceCrossings_firstCueIndex_bounded (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
      (crossings.get position)).firstCueIndex <
      (channelLastCues (attachSourceCrossings request glyphs crossings).conventions).length :=
  nat_lt_length_of_getElem?_some _
    (attachSourceCrossings_firstCueIndex_lookup request glyphs crossings position)

/-- The stored second cue index looks up exactly the second supplied glyph. -/
theorem attachSourceCrossings_secondCueIndex_lookup (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (channelLastCues (attachSourceCrossings request glyphs crossings).conventions)[(compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position)).secondCueIndex]? =
      some (ConventionCue.bondGlyph
        (glyphs.get (crossings.get position).second).toBondGlyph) := by
  rw [compileSuppliedCrossing_secondCueIndex]
  exact attachSourceCrossings_slot_lookup request glyphs crossings
    (crossings.get position).second

/-- The stored second cue index of a crossing is bounded in the final cue list. -/
theorem attachSourceCrossings_secondCueIndex_bounded (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
      (crossings.get position)).secondCueIndex <
      (channelLastCues (attachSourceCrossings request glyphs crossings).conventions).length :=
  nat_lt_length_of_getElem?_some _
    (attachSourceCrossings_secondCueIndex_lookup request glyphs crossings position)

/-- Repeated equal glyph payloads at two distinct supplied positions remain two cues at two
distinct positions in the final ordered cue list. -/
theorem attachSourceCrossings_repeated_equal_glyphs (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs))
    (first second : Fin glyphs.length)
    (equal : (glyphs.get first).toBondGlyph = (glyphs.get second).toBondGlyph)
    (different : first ≠ second) :
    (channelLastCues (attachSourceCrossings request glyphs crossings).conventions)[lastSourceCuePrefixLength request + first.val]? =
      some (ConventionCue.bondGlyph (glyphs.get first).toBondGlyph) ∧
    (channelLastCues (attachSourceCrossings request glyphs crossings).conventions)[lastSourceCuePrefixLength request + second.val]? =
      some (ConventionCue.bondGlyph (glyphs.get first).toBondGlyph) ∧
    lastSourceCuePrefixLength request + first.val ≠
      lastSourceCuePrefixLength request + second.val := by
  have secondLookup :=
    attachSourceCrossings_slot_lookup request glyphs crossings second
  refine ⟨attachSourceCrossings_slot_lookup request glyphs crossings first, ?_, ?_⟩
  · rw [secondLookup, ← equal]
  · intro indexEqual
    exact different (Fin.ext (Nat.add_left_cancel indexEqual))

/-- Distinct crossing list positions receive distinct final cue positions, so multiplicity of
crossing records is retained even when their payloads coincide. -/
theorem attachSourceCrossings_distinct_crossing_indices
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs))
    {first second : Fin crossings.length} (different : first ≠ second) :
    lastSourceCuePrefixLength request + glyphs.length + first.val ≠
      lastSourceCuePrefixLength request + glyphs.length + second.val := by
  intro indexEqual
  exact different (Fin.ext (Nat.add_left_cancel indexEqual))

/-- The complete original last-source cue sequence is a prefix of the final cue sequence. -/
theorem attachSourceCrossings_oldCues_prefix (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    channelLastCues request.conventions <+:
      channelLastCues (attachSourceCrossings request glyphs crossings).conventions := by
  rw [channelLastCues_attachSourceCrossings, List.append_assoc]
  exact List.prefix_append _ _

/-- Every convention record before the last one is literally unchanged by crossing attachment. -/
theorem attachConventionCues_dropLast (request : OrganicMolecularEvidence V)
    (extra : List (ConventionCue V)) :
    (attachConventionCues request extra).conventions.dropLast =
      request.conventions.dropLast := by
  cases extra with
  | nil => rfl
  | cons head tail =>
      change (ConventionChannel.attachCuesToLast (head :: tail)
        request.conventions).dropLast = request.conventions.dropLast
      exact ConventionChannel.attachCuesToLast_dropLast _ _

/-- Supplied glyph attachment never changes the records before the last convention record. -/
theorem attachSourceGlyphs_dropLast (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).conventions.dropLast =
      request.conventions.dropLast := by
  rw [attachSourceGlyphs_conventions]
  exact ConventionChannel.attachCuesToLast_dropLast _ _

/-- Crossing attachment never changes the records before the last convention record. -/
theorem attachSourceCrossings_dropLast (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (attachSourceCrossings request glyphs crossings).conventions.dropLast =
      request.conventions.dropLast := by
  rw [attachSourceCrossings_conventions, attachSourceGlyphs_conventions,
    ConventionChannel.attachCuesToLast_dropLast,
    ConventionChannel.attachCuesToLast_dropLast]

/-- Bundled statement: crossing attachment changes no non-convention evidence field. -/
theorem attachSourceCrossings_preserves_nonconvention (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (attachSourceCrossings request glyphs crossings).graph = request.graph ∧
    (attachSourceCrossings request glyphs crossings).conformation = request.conformation ∧
    (attachSourceCrossings request glyphs crossings).rationalPositions? =
      request.rationalPositions? ∧
    (attachSourceCrossings request glyphs crossings).electronic? = request.electronic? ∧
    (attachSourceCrossings request glyphs crossings).paths? = request.paths? ∧
    (attachSourceCrossings request glyphs crossings).bands? = request.bands? ∧
    (attachSourceCrossings request glyphs crossings).roles = request.roles ∧
    (attachSourceCrossings request glyphs crossings).diagram? = request.diagram? ∧
    (attachSourceCrossings request glyphs crossings).diagramPartial? = request.diagramPartial? ∧
    (attachSourceCrossings request glyphs crossings).diagramIncidence =
      request.diagramIncidence ∧
    (attachSourceCrossings request glyphs crossings).fragments = request.fragments ∧
    (attachSourceCrossings request glyphs crossings).cages = request.cages ∧
    (attachSourceCrossings request glyphs crossings).residueLedger? = request.residueLedger? ∧
    (attachSourceCrossings request glyphs crossings).frames = request.frames := by
  simp [attachSourceCrossings]

/-- Final last record when the supplied glyph list is nonempty: the old last record with the
glyph cues and then the crossing cues appended. -/
theorem attachSourceCrossings_last_cues_of_glyphs_nonempty
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) (glyphsNonempty : glyphs ≠ [])
    (crossings : List (SuppliedBondCrossing glyphs)) (crossingsNonempty : crossings ≠ [])
    {last : OrganicConventionSource V}
    (observed : request.conventions.getLast? = some last) :
    (attachSourceCrossings request glyphs crossings).conventions.getLast? =
      some ((last.appendCues (compileSuppliedCues request.graph glyphs)).appendCues
        (compileSuppliedCrossingCues glyphs
          (lastSourceCuePrefixLength request) crossings)) := by
  have cuesNonempty : compileSuppliedCues request.graph glyphs ≠ [] := by
    intro empty
    exact glyphsNonempty (by simpa [compileSuppliedCues] using empty)
  have crossingCuesNonempty :
      compileSuppliedCrossingCues glyphs (lastSourceCuePrefixLength request) crossings ≠ [] := by
    intro empty
    exact crossingsNonempty (by simpa [compileSuppliedCrossingCues] using empty)
  have glyphLast : (attachSourceGlyphs request glyphs).conventions.getLast? =
      some (last.appendCues (compileSuppliedCues request.graph glyphs)) := by
    rw [attachSourceGlyphs_conventions]
    exact ConventionChannel.attachCuesToLast_getLast?_of_some _ _ (last := last)
      cuesNonempty observed
  rw [attachSourceCrossings_conventions]
  exact ConventionChannel.attachCuesToLast_getLast?_of_some _ _
    (last := last.appendCues (compileSuppliedCues request.graph glyphs))
    crossingCuesNonempty glyphLast

/-- Exact final cue list of the last record in the nonempty-glyph case. -/
theorem attachSourceCrossings_last_cues?_of_glyphs_nonempty
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) (glyphsNonempty : glyphs ≠ [])
    (crossings : List (SuppliedBondCrossing glyphs)) (crossingsNonempty : crossings ≠ [])
    {last : OrganicConventionSource V}
    (observed : request.conventions.getLast? = some last) :
    ∃ finalLast : OrganicConventionSource V,
      (attachSourceCrossings request glyphs crossings).conventions.getLast? = some finalLast ∧
      finalLast.cues? = some
        ((last.cues?.getD [] ++ compileSuppliedCues request.graph glyphs) ++
          compileSuppliedCrossingCues glyphs
            (lastSourceCuePrefixLength request) crossings) := by
  have crossingCuesNonempty :
      compileSuppliedCrossingCues glyphs (lastSourceCuePrefixLength request) crossings ≠ [] := by
    intro empty
    exact crossingsNonempty (by simpa [compileSuppliedCrossingCues] using empty)
  refine ⟨_, attachSourceCrossings_last_cues_of_glyphs_nonempty request glyphs
    glyphsNonempty crossings crossingsNonempty observed, ?_⟩
  rw [OrganicConventionSource.appendCues_cues?_eq _ _ crossingCuesNonempty,
    OrganicConventionSource.appendCues_getD]

/-- The final last record keeps the old last record's non-cue fields in the nonempty-glyph
case. -/
theorem attachSourceCrossings_last_nonCue_of_glyphs_nonempty
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) (glyphsNonempty : glyphs ≠ [])
    (crossings : List (SuppliedBondCrossing glyphs)) (crossingsNonempty : crossings ≠ [])
    {last : OrganicConventionSource V}
    (observed : request.conventions.getLast? = some last) :
    ∃ finalLast : OrganicConventionSource V,
      (attachSourceCrossings request glyphs crossings).conventions.getLast? = some finalLast ∧
      finalLast.convention? = last.convention? ∧
      finalLast.scope? = last.scope? ∧
      finalLast.referenceFrame? = last.referenceFrame? := by
  refine ⟨_, attachSourceCrossings_last_cues_of_glyphs_nonempty request glyphs
    glyphsNonempty crossings crossingsNonempty observed, ?_, ?_, ?_⟩ <;> simp

/-- Final last record when the supplied glyph list is empty: the crossing cues are appended
directly to the old last record. -/
theorem attachSourceCrossings_last_cues_of_glyphs_nil
    (request : OrganicMolecularEvidence V)
    (crossings : List
      (SuppliedBondCrossing ([] : List (SuppliedBondGlyph request.graph))))
    (crossingsNonempty : crossings ≠ [])
    {last : OrganicConventionSource V}
    (observed : request.conventions.getLast? = some last) :
    (attachSourceCrossings request [] crossings).conventions.getLast? =
      some (last.appendCues
        (compileSuppliedCrossingCues
          ([] : List (SuppliedBondGlyph request.graph))
          (lastSourceCuePrefixLength request) crossings)) := by
  have cueNonempty :
      compileSuppliedCrossingCues ([] : List (SuppliedBondGlyph request.graph))
        (lastSourceCuePrefixLength request) crossings ≠ [] := by
    intro empty
    exact crossingsNonempty (by simpa [compileSuppliedCrossingCues] using empty)
  rw [attachSourceCrossings_conventions, attachSourceGlyphs_conventions]
  simp only [compileSuppliedCues_nil, ConventionChannel.attachCuesToLast_nil]
  exact ConventionChannel.attachCuesToLast_getLast?_of_some _ _ (last := last)
    cueNonempty observed

/-- Exact final cue list of the last record in the empty-glyph case. -/
theorem attachSourceCrossings_last_cues?_of_glyphs_nil
    (request : OrganicMolecularEvidence V)
    (crossings : List
      (SuppliedBondCrossing ([] : List (SuppliedBondGlyph request.graph))))
    (crossingsNonempty : crossings ≠ [])
    {last : OrganicConventionSource V}
    (observed : request.conventions.getLast? = some last) :
    ∃ finalLast : OrganicConventionSource V,
      (attachSourceCrossings request [] crossings).conventions.getLast? = some finalLast ∧
      finalLast.cues? = some
        (last.cues?.getD [] ++
          compileSuppliedCrossingCues
            ([] : List (SuppliedBondGlyph request.graph))
            (lastSourceCuePrefixLength request) crossings) := by
  have cueNonempty :
      compileSuppliedCrossingCues ([] : List (SuppliedBondGlyph request.graph))
        (lastSourceCuePrefixLength request) crossings ≠ [] := by
    intro empty
    exact crossingsNonempty (by simpa [compileSuppliedCrossingCues] using empty)
  refine ⟨_, attachSourceCrossings_last_cues_of_glyphs_nil request crossings
    crossingsNonempty observed, ?_⟩
  exact OrganicConventionSource.appendCues_cues?_eq last _ cueNonempty

/-- The final last record keeps the old last record's non-cue fields in the empty-glyph case. -/
theorem attachSourceCrossings_last_nonCue_of_glyphs_nil
    (request : OrganicMolecularEvidence V)
    (crossings : List
      (SuppliedBondCrossing ([] : List (SuppliedBondGlyph request.graph))))
    (crossingsNonempty : crossings ≠ [])
    {last : OrganicConventionSource V}
    (observed : request.conventions.getLast? = some last) :
    ∃ finalLast : OrganicConventionSource V,
      (attachSourceCrossings request [] crossings).conventions.getLast? = some finalLast ∧
      finalLast.convention? = last.convention? ∧
      finalLast.scope? = last.scope? ∧
      finalLast.referenceFrame? = last.referenceFrame? := by
  refine ⟨_, attachSourceCrossings_last_cues_of_glyphs_nil request crossings
    crossingsNonempty observed, ?_, ?_, ?_⟩ <;> simp

/-! ## Canonical common-core readback -/

/-- The common-enumeration image of a supplied crossing record.  Both cue indices and the literal
source crossing record are unchanged; both glyph payloads are mapped by the same enumeration. -/
def encodedSuppliedCrossing (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs))
    (position : Fin crossings.length) : BondCrossingGlyph (Fin (Fintype.card V)) :=
  BondCrossingGlyph.mapAtom enumeration
    (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
      (crossings.get position))

@[simp] theorem encodedSuppliedCrossing_firstCueIndex
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs))
    (position : Fin crossings.length) :
    (encodedSuppliedCrossing enumeration request glyphs crossings position).firstCueIndex =
      lastSourceCuePrefixLength request + (crossings.get position).first.val := rfl

@[simp] theorem encodedSuppliedCrossing_secondCueIndex
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs))
    (position : Fin crossings.length) :
    (encodedSuppliedCrossing enumeration request glyphs crossings position).secondCueIndex =
      lastSourceCuePrefixLength request + (crossings.get position).second.val := rfl

@[simp] theorem encodedSuppliedCrossing_first
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs))
    (position : Fin crossings.length) :
    (encodedSuppliedCrossing enumeration request glyphs crossings position).first =
      (glyphs.get (crossings.get position).first).toBondGlyph.mapAtom enumeration := rfl

@[simp] theorem encodedSuppliedCrossing_second
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs))
    (position : Fin crossings.length) :
    (encodedSuppliedCrossing enumeration request glyphs crossings position).second =
      (glyphs.get (crossings.get position).second).toBondGlyph.mapAtom enumeration := rfl

@[simp] theorem encodedSuppliedCrossing_crossing
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs))
    (position : Fin crossings.length) :
    (encodedSuppliedCrossing enumeration request glyphs crossings position).crossing =
      (crossings.get position).crossing := rfl

/-- The actual canonical assembly contains exactly the encoded crossing cue at the computed final
cue position. -/
theorem canonical_crossingCue_lookup (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (channelLastCues
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings)).state.conventions)[lastSourceCuePrefixLength request + glyphs.length + position.val]? =
      some (ConventionCue.bondCrossing
        (encodedSuppliedCrossing enumeration request glyphs crossings position)) := by
  rw [canonicalAssemble_conventions, channelLastCues_encode, List.getElem?_map,
    attachSourceCrossings_crossingCue_lookup]
  simp [encodedSuppliedCrossing]

/-- Every computed canonical crossing cue position is bounded in the actual canonical cue list. -/
theorem canonical_crossingCueIndex_bounded (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    lastSourceCuePrefixLength request + glyphs.length + position.val <
      (channelLastCues
        (canonicalAssemble enumeration
          (attachSourceCrossings request glyphs crossings)).state.conventions).length :=
  nat_lt_length_of_getElem?_some _
    (canonical_crossingCue_lookup enumeration request glyphs crossings position)

/-- The stored first cue index is unchanged by the common encoding and looks up exactly the
common-enumeration image of the first supplied glyph in the actual canonical cue list. -/
theorem canonical_firstCueIndex_lookup (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (channelLastCues
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings)).state.conventions)[(compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position)).firstCueIndex]? =
      some (ConventionCue.bondGlyph
        ((glyphs.get (crossings.get position).first).toBondGlyph.mapAtom enumeration)) := by
  rw [canonicalAssemble_conventions, channelLastCues_encode, List.getElem?_map,
    attachSourceCrossings_firstCueIndex_lookup]
  simp

/-- The stored first cue index is bounded in the actual canonical cue list. -/
theorem canonical_firstCueIndex_bounded (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
      (crossings.get position)).firstCueIndex <
      (channelLastCues
        (canonicalAssemble enumeration
          (attachSourceCrossings request glyphs crossings)).state.conventions).length :=
  nat_lt_length_of_getElem?_some _
    (canonical_firstCueIndex_lookup enumeration request glyphs crossings position)

/-- The stored second cue index is unchanged by the common encoding and looks up exactly the
common-enumeration image of the second supplied glyph in the actual canonical cue list. -/
theorem canonical_secondCueIndex_lookup (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (channelLastCues
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings)).state.conventions)[(compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position)).secondCueIndex]? =
      some (ConventionCue.bondGlyph
        ((glyphs.get (crossings.get position).second).toBondGlyph.mapAtom enumeration)) := by
  rw [canonicalAssemble_conventions, channelLastCues_encode, List.getElem?_map,
    attachSourceCrossings_secondCueIndex_lookup]
  simp

/-- The stored second cue index is bounded in the actual canonical cue list. -/
theorem canonical_secondCueIndex_bounded (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
      (crossings.get position)).secondCueIndex <
      (channelLastCues
        (canonicalAssemble enumeration
          (attachSourceCrossings request glyphs crossings)).state.conventions).length :=
  nat_lt_length_of_getElem?_some _
    (canonical_secondCueIndex_lookup enumeration request glyphs crossings position)

/-- Exact canonical retention bundle: the cue is present at the computed position, both stored
indices are the computed cue positions, both glyph payloads are the common-enumeration images of
the supplied glyphs, and the source crossing record is literal. -/
theorem canonical_crossingCue_fields (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    ∃ cueGlyph : BondCrossingGlyph (Fin (Fintype.card V)),
      (channelLastCues
        (canonicalAssemble enumeration
          (attachSourceCrossings request glyphs crossings)).state.conventions)[lastSourceCuePrefixLength request + glyphs.length + position.val]? =
        some (ConventionCue.bondCrossing cueGlyph) ∧
      cueGlyph.firstCueIndex =
        lastSourceCuePrefixLength request + (crossings.get position).first.val ∧
      cueGlyph.secondCueIndex =
        lastSourceCuePrefixLength request + (crossings.get position).second.val ∧
      cueGlyph.first =
        (glyphs.get (crossings.get position).first).toBondGlyph.mapAtom enumeration ∧
      cueGlyph.second =
        (glyphs.get (crossings.get position).second).toBondGlyph.mapAtom enumeration ∧
      cueGlyph.crossing = (crossings.get position).crossing := by
  refine ⟨encodedSuppliedCrossing enumeration request glyphs crossings position,
    canonical_crossingCue_lookup enumeration request glyphs crossings position,
    ?_, ?_, ?_, ?_, ?_⟩ <;> simp [encodedSuppliedCrossing]

/-- The canonical first glyph retains its actual interaction occurrence index, both mapped
endpoints, the complete orientation record and the optional supplied tokens. -/
theorem canonical_crossing_first_payload (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (encodedSuppliedCrossing enumeration request glyphs crossings position).first.interactionIndex =
        (glyphs.get (crossings.get position).first).interactionIndex.val ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).first.source =
        enumeration (glyphs.get (crossings.get position).first).source ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).first.target =
        enumeration (glyphs.get (crossings.get position).first).target ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).first.oriented =
        (glyphs.get (crossings.get position).first).oriented ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).first.hashConvention? =
        (glyphs.get (crossings.get position).first).hashConvention? ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).first.wavyGeometry? =
        (glyphs.get (crossings.get position).first).wavyGeometry? ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).first.purpose? =
        (glyphs.get (crossings.get position).first).purpose? := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [encodedSuppliedCrossing]

/-- The canonical second glyph retains its actual interaction occurrence index, both mapped
endpoints, the complete orientation record and the optional supplied tokens. -/
theorem canonical_crossing_second_payload (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (encodedSuppliedCrossing enumeration request glyphs crossings position).second.interactionIndex =
        (glyphs.get (crossings.get position).second).interactionIndex.val ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).second.source =
        enumeration (glyphs.get (crossings.get position).second).source ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).second.target =
        enumeration (glyphs.get (crossings.get position).second).target ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).second.oriented =
        (glyphs.get (crossings.get position).second).oriented ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).second.hashConvention? =
        (glyphs.get (crossings.get position).second).hashConvention? ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).second.wavyGeometry? =
        (glyphs.get (crossings.get position).second).wavyGeometry? ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).second.purpose? =
        (glyphs.get (crossings.get position).second).purpose? := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [encodedSuppliedCrossing]

/-- The two source flags and the exact rational ratio are retained literally at the canonical
output.  No recommendation, `UnambiguousCrossing` or derived-depth hypothesis is used. -/
theorem canonical_crossing_literal_fields (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (encodedSuppliedCrossing enumeration request glyphs crossings position).crossing.backBondDiscontinuous =
        (crossings.get position).crossing.backBondDiscontinuous ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).crossing.discontinuityWidthRatio =
        (crossings.get position).crossing.discontinuityWidthRatio ∧
    (encodedSuppliedCrossing enumeration request glyphs crossings position).crossing.orderingConflictsWithVerticalDepthCue =
        (crossings.get position).crossing.orderingConflictsWithVerticalDepthCue :=
  ⟨rfl, rfl, rfl⟩

/-- Canonical cue atom references are exactly the source cue references mapped by the one common
enumeration, preserving both written endpoints of both glyphs in order and multiplicity. -/
theorem canonical_crossingCue_atomReferences (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (ConventionCue.bondCrossing
      (encodedSuppliedCrossing enumeration request glyphs crossings position)).atomReferences =
      ((ConventionCue.bondCrossing
        (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position))).atomReferences).map enumeration := by
  simp only [encodedSuppliedCrossing, ConventionCue.atomReferences_bondCrossing,
    BondCrossingGlyph.mapAtom_first, BondCrossingGlyph.mapAtom_second,
    BondGlyph.atomReferences_mapAtom, List.map_append]

/-- Membership in the canonical crossing cue's atom references is exactly membership of the
source atom in the source cue references after applying the common enumeration. -/
theorem canonical_crossingCue_atomReferences_mem_iff
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length)
    (atom : Fin (Fintype.card V)) :
    atom ∈ (ConventionCue.bondCrossing
      (encodedSuppliedCrossing enumeration request glyphs crossings position)).atomReferences ↔
      ∃ sourceAtom ∈ (ConventionCue.bondCrossing
        (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position))).atomReferences,
        enumeration sourceAtom = atom := by
  rw [canonical_crossingCue_atomReferences, List.mem_map]

/-- Every atom reference of the source crossing cue is looked up in the encoded graph at exactly
the enumeration index that the graph encoding itself uses for that atom's semantic data.  Thus
cue references use the same equivalence as the graph. -/
theorem crossing_atomReferences_agree_with_graph
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (crossing : BondCrossingGlyph V) {atom : V}
    (member : atom ∈ (ConventionCue.bondCrossing crossing).atomReferences) :
    listGet? (graph.encode enumeration).atoms (enumeration atom).val =
      some (graph.atomData atom) :=
  atomReferences_agrees_with_graph graph enumeration
    (ConventionCue.bondCrossing crossing) member

/-- The source crossing cue's references satisfy the same graph-agreement property. -/
theorem compileSuppliedCrossingCue_atomReferences_agree_with_graph
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length)
    (enumeration : V ≃ Fin (Fintype.card V)) {atom : V}
    (member : atom ∈ (ConventionCue.bondCrossing
      (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
        (crossings.get position))).atomReferences) :
    listGet? (request.graph.encode enumeration).atoms (enumeration atom).val =
      some (request.graph.atomData atom) :=
  atomReferences_agrees_with_graph request.graph enumeration
    (ConventionCue.bondCrossing
      (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
        (crossings.get position))) member

/-- A canonical crossing-cue atom reference comes from a source crossing-cue reference through the
one common enumeration, and that source reference is looked up in the encoded request graph at
exactly the enumeration index. -/
theorem canonical_crossingCue_atomReferences_agree_with_graph
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length)
    {atom : Fin (Fintype.card V)}
    (member : atom ∈ (ConventionCue.bondCrossing
      (encodedSuppliedCrossing enumeration request glyphs crossings position)).atomReferences) :
    ∃ sourceAtom : V,
      enumeration sourceAtom = atom ∧
      sourceAtom ∈ (ConventionCue.bondCrossing
        (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position))).atomReferences ∧
      listGet? (request.graph.encode enumeration).atoms atom.val =
        some (request.graph.atomData sourceAtom) := by
  obtain ⟨sourceAtom, sourceMember, mapped⟩ :=
    (canonical_crossingCue_atomReferences_mem_iff enumeration request glyphs crossings
      position atom).mp member
  refine ⟨sourceAtom, mapped, sourceMember, ?_⟩
  rw [← mapped]
  exact compileSuppliedCrossingCue_atomReferences_agree_with_graph request glyphs
    crossings position enumeration sourceMember

/-- The actual canonical state graph is exactly the common-enumeration relabelling of the request
graph. -/
theorem canonical_attachSourceCrossings_graph (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (canonicalAssemble enumeration
      (attachSourceCrossings request glyphs crossings)).state.graph =
      relabelGraph enumeration request.graph := by
  rw [canonicalAssemble_state_graph]
  rfl

/-- Canonical graph atom data is looked up at the image of the same common enumeration, so cue
atom references and graph atom data use one equivalence. -/
theorem canonical_attachSourceCrossings_graph_atomData
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (atom : V) :
    (canonicalAssemble enumeration
      (attachSourceCrossings request glyphs crossings)).state.graph.atomData
        (enumeration atom) = request.graph.atomData atom := by
  rw [canonical_attachSourceCrossings_graph, relabelGraph_atomData_apply]
  simp

/-- A supplied glyph at any position still names its actual interaction occurrence after the
common relabelling, and both mapped endpoints are participants of that exact occurrence. -/
theorem relabel_graph_suppliedGlyph_mem (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (slot : Fin glyphs.length) :
    ∃ index : Fin (relabelGraph enumeration graph).interactions.length,
      index.val = (glyphs.get slot).interactionIndex.val ∧
      enumeration (glyphs.get slot).source ∈
        ((relabelGraph enumeration graph).interactions.get index).1 ∧
      enumeration (glyphs.get slot).target ∈
        ((relabelGraph enumeration graph).interactions.get index).1 := by
  refine ⟨relabelInteractionIndex enumeration (glyphs.get slot).interactionIndex, rfl, ?_, ?_⟩
  · rw [relabelGraph_interactions_get]
    show enumeration (glyphs.get slot).source ∈
      (graph.interactions.get (glyphs.get slot).interactionIndex).1.map enumeration
    exact List.mem_map_of_mem (f := enumeration) (glyphs.get slot).source_mem_occurrence
  · rw [relabelGraph_interactions_get]
    show enumeration (glyphs.get slot).target ∈
      (graph.interactions.get (glyphs.get slot).interactionIndex).1.map enumeration
    exact List.mem_map_of_mem (f := enumeration) (glyphs.get slot).target_mem_occurrence

/-- Both supplied crossing occurrences survive the canonical relabelling: the canonical state
graph is the relabelled request graph, and each glyph still names an actual interaction
occurrence containing both of its mapped endpoints. -/
theorem canonical_crossing_occurrences (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (canonicalAssemble enumeration
      (attachSourceCrossings request glyphs crossings)).state.graph =
        relabelGraph enumeration request.graph ∧
    ∃ firstIndex secondIndex :
        Fin (relabelGraph enumeration request.graph).interactions.length,
      firstIndex.val =
          (glyphs.get (crossings.get position).first).interactionIndex.val ∧
      secondIndex.val =
          (glyphs.get (crossings.get position).second).interactionIndex.val ∧
      enumeration (glyphs.get (crossings.get position).first).source ∈
        ((relabelGraph enumeration request.graph).interactions.get firstIndex).1 ∧
      enumeration (glyphs.get (crossings.get position).first).target ∈
        ((relabelGraph enumeration request.graph).interactions.get firstIndex).1 ∧
      enumeration (glyphs.get (crossings.get position).second).source ∈
        ((relabelGraph enumeration request.graph).interactions.get secondIndex).1 ∧
      enumeration (glyphs.get (crossings.get position).second).target ∈
        ((relabelGraph enumeration request.graph).interactions.get secondIndex).1 := by
  refine ⟨canonical_attachSourceCrossings_graph enumeration request glyphs crossings, ?_⟩
  obtain ⟨firstIndex, hfirstValue, hfirstSource, hfirstTarget⟩ :=
    relabel_graph_suppliedGlyph_mem enumeration request.graph glyphs
      (crossings.get position).first
  obtain ⟨secondIndex, hsecondValue, hsecondSource, hsecondTarget⟩ :=
    relabel_graph_suppliedGlyph_mem enumeration request.graph glyphs
      (crossings.get position).second
  exact ⟨firstIndex, secondIndex, hfirstValue, hsecondValue,
    hfirstSource, hfirstTarget, hsecondSource, hsecondTarget⟩

/-- The canonically mapped original last-source cue prefix is retained. -/
theorem canonical_attachSourceCrossings_oldCues_prefix
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (channelLastCues request.conventions).map (ConventionCue.mapAtom enumeration) <+:
      channelLastCues
        (canonicalAssemble enumeration
          (attachSourceCrossings request glyphs crossings)).state.conventions := by
  rw [canonicalAssemble_conventions, channelLastCues_encode]
  exact List.IsPrefix.map (ConventionCue.mapAtom enumeration)
    (attachSourceCrossings_oldCues_prefix request glyphs crossings)

/-! ## Decoder recovery: literal supply from the canonical common core -/

/-- The actual `decodedCore` of the canonical assembly is exactly the source-augmented request.
No original source is supplied to the decoder. -/
theorem decodedCore_attachSourceCrossings (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings)) =
      attachSourceCrossings request glyphs crossings := by
  simpa [decodedCore] using
    decode_canonicalAssemble enumeration
      (attachSourceCrossings request glyphs crossings)

/-- The decoded canonical core carries exactly the augmented convention channel. -/
theorem decodedCore_attachSourceCrossings_conventions
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).conventions =
      (attachSourceCrossings request glyphs crossings).conventions := by
  rw [decodedCore_attachSourceCrossings]

/-- The decoded canonical core recovers the complete literal source-labelled last cue sequence. -/
theorem decodedCore_attachSourceCrossings_lastCues
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    channelLastCues
      (decodedCore
        (canonicalAssemble enumeration
          (attachSourceCrossings request glyphs crossings))).conventions =
      (channelLastCues request.conventions ++
        compileSuppliedCues request.graph glyphs) ++
        compileSuppliedCrossingCues glyphs
          (lastSourceCuePrefixLength request) crossings := by
  rw [decodedCore_attachSourceCrossings]
  exact channelLastCues_attachSourceCrossings request glyphs crossings

/-- The decoded canonical core contains exactly the literal source crossing cue at the computed
cue position, with no source parameter passed to the decoder. -/
theorem decodedCore_crossingCue_lookup (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) (position : Fin crossings.length) :
    (channelLastCues
      (decodedCore
        (canonicalAssemble enumeration
          (attachSourceCrossings request glyphs crossings))).conventions)[lastSourceCuePrefixLength request + glyphs.length + position.val]? =
      some (ConventionCue.bondCrossing
        (compileSuppliedCrossing glyphs (lastSourceCuePrefixLength request)
          (crossings.get position))) := by
  rw [decodedCore_attachSourceCrossings]
  exact attachSourceCrossings_crossingCue_lookup request glyphs crossings position

/-- The decoded canonical core retains the whole original last-source cue sequence as a prefix,
in addition to the appended glyph and crossing cues. -/
theorem decodedCore_attachSourceCrossings_oldCues_prefix
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    channelLastCues request.conventions <+:
      channelLastCues
        (decodedCore
          (canonicalAssemble enumeration
            (attachSourceCrossings request glyphs crossings))).conventions := by
  rw [decodedCore_attachSourceCrossings]
  exact attachSourceCrossings_oldCues_prefix request glyphs crossings

/-- The decoded canonical core keeps every non-convention field of the request. -/
theorem decodedCore_attachSourceCrossings_preserves_nonconvention
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).graph = request.graph ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).conformation =
        request.conformation ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).rationalPositions? =
        request.rationalPositions? ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).electronic? =
        request.electronic? ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).paths? =
        request.paths? ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).bands? =
        request.bands? ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).roles =
        request.roles ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).diagram? =
        request.diagram? ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).diagramPartial? =
        request.diagramPartial? ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).diagramIncidence =
        request.diagramIncidence ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).fragments =
        request.fragments ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).cages =
        request.cages ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).residueLedger? =
        request.residueLedger? ∧
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).frames =
        request.frames := by
  rw [decodedCore_attachSourceCrossings]
  exact attachSourceCrossings_preserves_nonconvention request glyphs crossings

@[simp] theorem decodedCore_attachSourceCrossings_graph
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).graph =
      request.graph := by
  rw [decodedCore_attachSourceCrossings]
  rfl

@[simp] theorem decodedCore_attachSourceCrossings_conformation
    (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph))
    (crossings : List (SuppliedBondCrossing glyphs)) :
    (decodedCore
      (canonicalAssemble enumeration
        (attachSourceCrossings request glyphs crossings))).conformation =
      request.conformation := by
  rw [decodedCore_attachSourceCrossings]
  rfl

end Crossing

end TetraStereo.OneCenter
