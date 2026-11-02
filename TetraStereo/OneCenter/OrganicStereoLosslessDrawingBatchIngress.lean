import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoSourceCrossingIngress

set_option autoImplicit false

namespace TetraStereo.OneCenter

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport
open OrganicStereoSpatialSupportMolecularAssembly

variable {V W : Type}

/-!
# Lossless drawing-batch ingress

The approved `attachSourceGlyphs` (and the active crossing ingress) append generated cues to the
*last existing* `OrganicConventionSource`.  With a nonempty append, `appendCues` merges a prior
`cues? = none` and a prior `cues? = some []` into the same `some (old ++ extra)` shape, so the
prior request's absence/present-empty distinction cannot be recovered from the output.

This leaf supplies a separate, lossless attachment path.  It never merges: it always appends one
*fresh* `OrganicConventionSource` record to the existing `ConventionChannel`, whose cue channel is

* `none` when no batch is supplied,
* `some []` when a supplied batch is empty,
* `some (glyphCues ++ crossingCues)` otherwise.

The prior channel is therefore a literal prefix and the exact `dropLast` of the result.  Crossing
cue indices in the fresh record start at `0 + glyph position` (there is no prior prefix), and all
retention payloads are the existing `BondGlyph` / `BondCrossingGlyph` records compiled from
`SuppliedBondGlyph` by the green glyph ingress.

The decoder reads only a common atom equivalence and either a `ConventionChannel` or an actual
`CanonicalOrganicMolecularRepresentation`.  It never receives the original request: the prior
channel is obtained by `dropLast`, and batch presence plus the ordered glyph/crossing payloads are
obtained from the last record.  Proof-carrying records are reconstructed from the decoded common
graph with bounds and memberships proved there, not from saved original bindings.

No interpretation of a wedge, hash, wavy geometry, purpose, or crossing is introduced.
-/

section Batch

variable [DecidableEq V] [Fintype V]

/-! ## Supplied batch crossings -/





abbrev DrawingBatchCrossing (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) : Type :=
  SuppliedBondCrossing (graph := graph) glyphs

/-- Compile one batch crossing at a cue-list prefix.  The two indices are positions in the
containing ordered cue list, not atom labels or interaction indices.  This is verbatim the active
upstream `compileSuppliedCrossing`; only the fresh-batch argument order is fixed. -/
abbrev compileBatchCrossing (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossing : DrawingBatchCrossing graph glyphs) : BondCrossingGlyph V :=
  compileSuppliedCrossing (graph := graph) glyphs prefixLength crossing

/-- Compile an ordered crossing list to retention-layer crossing records (upstream
`compileSuppliedCrossings`). -/
abbrev compileBatchCrossings (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) : List (BondCrossingGlyph V) :=
  compileSuppliedCrossings (graph := graph) glyphs prefixLength crossings

/-- Compile an ordered crossing list directly to ordered convention cues (upstream
`compileSuppliedCrossingCues`). -/
abbrev compileBatchCrossingCues (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) : List (ConventionCue V) :=
  compileSuppliedCrossingCues (graph := graph) glyphs prefixLength crossings

namespace DrawingBatchCrossing

variable {graph : FiniteAtomInteractionHypergraph V} {glyphs : List (SuppliedBondGlyph graph)}

/-- The compiled first cue index is the batch prefix plus the supplied position. -/
@[simp] theorem compileBatchCrossing_firstCueIndex (prefixLength : Nat)
    (crossing : DrawingBatchCrossing graph glyphs) :
    (compileBatchCrossing graph glyphs prefixLength crossing).firstCueIndex =
      prefixLength + crossing.first.val := rfl

/-- The compiled second cue index is the batch prefix plus the supplied position. -/
@[simp] theorem compileBatchCrossing_secondCueIndex (prefixLength : Nat)
    (crossing : DrawingBatchCrossing graph glyphs) :
    (compileBatchCrossing graph glyphs prefixLength crossing).secondCueIndex =
      prefixLength + crossing.second.val := rfl

/-- The first retained glyph is exactly the supplied first position's compiled glyph. -/
@[simp] theorem compileBatchCrossing_first (prefixLength : Nat)
    (crossing : DrawingBatchCrossing graph glyphs) :
    (compileBatchCrossing graph glyphs prefixLength crossing).first =
      (glyphs.get crossing.first).toBondGlyph := rfl

/-- The second retained glyph is exactly the supplied second position's compiled glyph. -/
@[simp] theorem compileBatchCrossing_second (prefixLength : Nat)
    (crossing : DrawingBatchCrossing graph glyphs) :
    (compileBatchCrossing graph glyphs prefixLength crossing).second =
      (glyphs.get crossing.second).toBondGlyph := rfl

/-- The literal source crossing record is copied verbatim. -/
@[simp] theorem compileBatchCrossing_crossing (prefixLength : Nat)
    (crossing : DrawingBatchCrossing graph glyphs) :
    (compileBatchCrossing graph glyphs prefixLength crossing).crossing =
      crossing.crossing := rfl

end DrawingBatchCrossing

/-- The two compilations agree. -/
theorem compileBatchCrossings_map_bondCrossing (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) :
    (compileBatchCrossings graph glyphs prefixLength crossings).map ConventionCue.bondCrossing =
      compileBatchCrossingCues graph glyphs prefixLength crossings := by
  unfold compileBatchCrossings compileBatchCrossingCues
  unfold compileSuppliedCrossings compileSuppliedCrossingCues
  rw [List.map_map]
  rfl

/-- Ordered length retention for crossings. -/
@[simp] theorem compileBatchCrossings_length (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) :
    (compileBatchCrossings graph glyphs prefixLength crossings).length = crossings.length :=
  compileSuppliedCrossings_length glyphs prefixLength crossings

/-- Ordered length retention for crossing cues. -/
@[simp] theorem compileBatchCrossingCues_length (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) :
    (compileBatchCrossingCues graph glyphs prefixLength crossings).length = crossings.length :=
  compileSuppliedCrossingCues_length glyphs prefixLength crossings

/-- Exact ordered crossing lookup, position by position. -/
theorem compileBatchCrossings_get?_bounded (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) (index : Nat)
    (bound : index < crossings.length) :
    (compileBatchCrossings graph glyphs prefixLength crossings)[index]? =
      some (compileBatchCrossing graph glyphs prefixLength (crossings[index]'bound)) :=
  compileSuppliedCrossings_get?_bounded glyphs prefixLength crossings index bound

/-- Exact ordered crossing-cue lookup, position by position. -/
theorem compileBatchCrossingCues_get?_bounded (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) (index : Nat)
    (bound : index < crossings.length) :
    (compileBatchCrossingCues graph glyphs prefixLength crossings)[index]? =
      some (ConventionCue.bondCrossing
        (compileBatchCrossing graph glyphs prefixLength (crossings[index]'bound))) :=
  compileSuppliedCrossingCues_get?_bounded glyphs prefixLength crossings index bound

/-! ## The supplied batch -/

/-- An independently supplied drawing batch: an ordered glyph list and an ordered crossing list
whose positions are bounded by that same glyph list. -/
structure SuppliedDrawingBatch (graph : FiniteAtomInteractionHypergraph V) where
  /-- The ordered supplied bond glyphs. -/
  glyphs : List (SuppliedBondGlyph graph)
  /-- The ordered supplied crossings, referencing positions in `glyphs`. -/
  crossings : List (DrawingBatchCrossing graph glyphs)

namespace SuppliedDrawingBatch

variable {graph : FiniteAtomInteractionHypergraph V}

/-- The ordered compiled cue list of a batch.  Glyph cues come first, so a crossing index
`first.val` is exactly the position of the first glyph's cue.  The prefix is `0`: this list is
always placed in a fresh record. -/
def cues (batch : SuppliedDrawingBatch graph) : List (ConventionCue V) :=
  compileSuppliedCues graph batch.glyphs ++
    compileBatchCrossingCues graph batch.glyphs 0 batch.crossings

/-- The empty batch compiles to the empty cue list. -/
@[simp] theorem cues_empty :
    (⟨[], []⟩ : SuppliedDrawingBatch graph).cues = [] := rfl

/-- Exact structural count: one cue per glyph plus one cue per crossing. -/
@[simp] theorem cues_length (batch : SuppliedDrawingBatch graph) :
    batch.cues.length = batch.glyphs.length + batch.crossings.length := by
  unfold cues
  rw [List.length_append, compileSuppliedCues_length, compileBatchCrossingCues_length]

/-- Exact ordered glyph-cue lookup.  Order, position and multiplicity are retained. -/
theorem cues_get?_glyph (batch : SuppliedDrawingBatch graph) (index : Nat)
    (bound : index < batch.glyphs.length) :
    batch.cues[index]? = some (batch.glyphs[index]'bound).toCue := by
  unfold cues
  rw [List.getElem?_append_left (by simpa using bound)]
  exact compileSuppliedCues_get?_bounded graph batch.glyphs index bound

/-- Exact ordered crossing-cue lookup at the post-glyph positions. -/
theorem cues_get?_crossing (batch : SuppliedDrawingBatch graph) (index : Nat)
    (bound : index < batch.crossings.length) :
    batch.cues[batch.glyphs.length + index]? =
      some (ConventionCue.bondCrossing
        (compileBatchCrossing graph batch.glyphs 0 (batch.crossings[index]'bound))) := by
  unfold cues
  rw [List.getElem?_append_right (by simp)]
  have hlen : (compileSuppliedCues graph batch.glyphs).length = batch.glyphs.length := by simp
  rw [hlen, Nat.add_sub_cancel_left]
  exact compileBatchCrossingCues_get?_bounded graph batch.glyphs 0 batch.crossings index bound

/-- The first stored cue index of a crossing is in the fresh cue list and looks up exactly the
first supplied glyph's cue. -/
theorem cues_firstCueIndex_lookup (batch : SuppliedDrawingBatch graph)
    (crossing : DrawingBatchCrossing graph batch.glyphs) :
    batch.cues[(compileBatchCrossing graph batch.glyphs 0 crossing).firstCueIndex]? =
      some (ConventionCue.bondGlyph
        (batch.glyphs.get crossing.first).toBondGlyph) := by
  rw [DrawingBatchCrossing.compileBatchCrossing_firstCueIndex, Nat.zero_add]
  rw [cues_get?_glyph batch crossing.first.val crossing.first.isLt]
  rfl

/-- The second stored cue index of a crossing is in the fresh cue list and looks up exactly the
second supplied glyph's cue. -/
theorem cues_secondCueIndex_lookup (batch : SuppliedDrawingBatch graph)
    (crossing : DrawingBatchCrossing graph batch.glyphs) :
    batch.cues[(compileBatchCrossing graph batch.glyphs 0 crossing).secondCueIndex]? =
      some (ConventionCue.bondGlyph
        (batch.glyphs.get crossing.second).toBondGlyph) := by
  rw [DrawingBatchCrossing.compileBatchCrossing_secondCueIndex, Nat.zero_add]
  rw [cues_get?_glyph batch crossing.second.val crossing.second.isLt]
  rfl

/-- Both stored crossing indices are bounded by the fresh cue-list length. -/
theorem cues_firstCueIndex_lt (batch : SuppliedDrawingBatch graph)
    (crossing : DrawingBatchCrossing graph batch.glyphs) :
    (compileBatchCrossing graph batch.glyphs 0 crossing).firstCueIndex < batch.cues.length := by
  rw [DrawingBatchCrossing.compileBatchCrossing_firstCueIndex, Nat.zero_add, cues_length]
  exact Nat.lt_of_lt_of_le crossing.first.isLt (Nat.le_add_right _ _)

/-- Both stored crossing indices are bounded by the fresh cue-list length. -/
theorem cues_secondCueIndex_lt (batch : SuppliedDrawingBatch graph)
    (crossing : DrawingBatchCrossing graph batch.glyphs) :
    (compileBatchCrossing graph batch.glyphs 0 crossing).secondCueIndex < batch.cues.length := by
  rw [DrawingBatchCrossing.compileBatchCrossing_secondCueIndex, Nat.zero_add, cues_length]
  exact Nat.lt_of_lt_of_le crossing.second.isLt (Nat.le_add_right _ _)

/-- Two distinct glyph positions are two distinct cue positions with their exact payloads: order
and duplicate multiplicity are retained, not collapsed. -/
theorem cues_distinct_glyph_positions (batch : SuppliedDrawingBatch graph)
    (first second : Fin batch.glyphs.length) (different : first ≠ second) :
    ∃ firstIndex secondIndex : Nat, firstIndex ≠ secondIndex ∧
      batch.cues[firstIndex]? = some (batch.glyphs.get first).toCue ∧
      batch.cues[secondIndex]? = some (batch.glyphs.get second).toCue := by
  refine ⟨first.val, second.val, ?_, ?_, ?_⟩
  · intro equal
    exact different (Fin.ext equal)
  · exact batch.cues_get?_glyph first.val first.isLt
  · exact batch.cues_get?_glyph second.val second.isLt

/-- Two distinct crossing positions occupy two distinct post-glyph cue positions. -/
theorem cues_distinct_crossing_positions (batch : SuppliedDrawingBatch graph)
    (first second : Fin batch.crossings.length) (different : first ≠ second) :
    ∃ firstIndex secondIndex : Nat, firstIndex ≠ secondIndex ∧
      batch.cues[firstIndex]? =
        some (ConventionCue.bondCrossing
          (compileBatchCrossing graph batch.glyphs 0 (batch.crossings.get first))) ∧
      batch.cues[secondIndex]? =
        some (ConventionCue.bondCrossing
          (compileBatchCrossing graph batch.glyphs 0 (batch.crossings.get second))) := by
  refine ⟨batch.glyphs.length + first.val, batch.glyphs.length + second.val, ?_, ?_, ?_⟩
  · intro equal
    have : first.val = second.val := Nat.add_left_cancel equal
    exact different (Fin.ext this)
  · exact batch.cues_get?_crossing first.val first.isLt
  · exact batch.cues_get?_crossing second.val second.isLt

end SuppliedDrawingBatch

/-! ## The fresh record and the lossless attachment -/

/-- The single fresh record appended by the lossless path.  `cues? = none` for an absent batch,
`some []` for a present empty batch, and `some batch.cues` otherwise.  The other three fields are
absent exactly as they would be for a record that carries no convention/scope/frame. -/
def freshDrawingSource {graph : FiniteAtomInteractionHypergraph V}
    (batch? : Option (SuppliedDrawingBatch graph)) : OrganicConventionSource V :=
  match batch? with
  | none =>
      { convention? := none, scope? := none, referenceFrame? := none, cues? := none }
  | some batch =>
      { convention? := none, scope? := none, referenceFrame? := none,
        cues? := some batch.cues }

/-- Absent batch: the fresh cue channel is genuinely absent. -/
@[simp] theorem freshDrawingSource_cues?_none {graph : FiniteAtomInteractionHypergraph V} :
    (freshDrawingSource (none : Option (SuppliedDrawingBatch graph))).cues? = none := rfl

/-- Present batch: the fresh cue channel is present and carries exactly the batch cues. -/
@[simp] theorem freshDrawingSource_cues?_some {graph : FiniteAtomInteractionHypergraph V}
    (batch : SuppliedDrawingBatch graph) :
    (freshDrawingSource (some batch)).cues? = some batch.cues := rfl

/-- The fresh record never invents a projection convention. -/
@[simp] theorem freshDrawingSource_convention? {graph : FiniteAtomInteractionHypergraph V}
    (batch? : Option (SuppliedDrawingBatch graph)) :
    (freshDrawingSource batch?).convention? = none := by
  cases batch? <;> rfl

/-- The fresh record never invents a configuration scope. -/
@[simp] theorem freshDrawingSource_scope? {graph : FiniteAtomInteractionHypergraph V}
    (batch? : Option (SuppliedDrawingBatch graph)) :
    (freshDrawingSource batch?).scope? = none := by
  cases batch? <;> rfl

/-- The fresh record never invents a reference frame. -/
@[simp] theorem freshDrawingSource_referenceFrame? {graph : FiniteAtomInteractionHypergraph V}
    (batch? : Option (SuppliedDrawingBatch graph)) :
    (freshDrawingSource batch?).referenceFrame? = none := by
  cases batch? <;> rfl

/-- An absent batch and a present empty batch produce *different* fresh records: `cues? = none`
versus `cues? = some []`. -/
theorem freshDrawingSource_none_ne_some_empty {graph : FiniteAtomInteractionHypergraph V} :
    (freshDrawingSource (none : Option (SuppliedDrawingBatch graph)) : OrganicConventionSource V) ≠
      freshDrawingSource (some (⟨[], []⟩ : SuppliedDrawingBatch graph)) := by
  intro equal
  have observed := congrArg OrganicConventionSource.cues? equal
  simp [freshDrawingSource] at observed

/-- Attach a supplied drawing batch losslessly: append exactly one fresh convention-source record.
The prior channel is copied literally, so its absence/present-empty distinctions survive. -/
def attachSourceDrawingBatch (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) : OrganicMolecularEvidence V :=
  { request with conventions := request.conventions ++ [freshDrawingSource batch?] }

/-- The exact augmented convention channel. -/
@[simp] theorem attachSourceDrawingBatch_conventions (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (attachSourceDrawingBatch request batch?).conventions =
      request.conventions ++ [freshDrawingSource batch?] := rfl

/-- The graph is untouched. -/
@[simp] theorem attachSourceDrawingBatch_graph (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (attachSourceDrawingBatch request batch?).graph = request.graph := rfl

/-- The conformation is untouched. -/
@[simp] theorem attachSourceDrawingBatch_conformation (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (attachSourceDrawingBatch request batch?).conformation = request.conformation := rfl

/-- Every non-convention evidence channel is literally unchanged. -/
theorem attachSourceDrawingBatch_preserves_nonconvention (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (attachSourceDrawingBatch request batch?).graph = request.graph ∧
    (attachSourceDrawingBatch request batch?).conformation = request.conformation ∧
    (attachSourceDrawingBatch request batch?).rationalPositions? = request.rationalPositions? ∧
    (attachSourceDrawingBatch request batch?).electronic? = request.electronic? ∧
    (attachSourceDrawingBatch request batch?).paths? = request.paths? ∧
    (attachSourceDrawingBatch request batch?).bands? = request.bands? ∧
    (attachSourceDrawingBatch request batch?).roles = request.roles ∧
    (attachSourceDrawingBatch request batch?).diagram? = request.diagram? ∧
    (attachSourceDrawingBatch request batch?).diagramPartial? = request.diagramPartial? ∧
    (attachSourceDrawingBatch request batch?).diagramIncidence = request.diagramIncidence ∧
    (attachSourceDrawingBatch request batch?).fragments = request.fragments ∧
    (attachSourceDrawingBatch request batch?).cages = request.cages ∧
    (attachSourceDrawingBatch request batch?).residueLedger? = request.residueLedger? ∧
    (attachSourceDrawingBatch request batch?).frames = request.frames := by
  simp [attachSourceDrawingBatch]

/-- The prior channel is a literal prefix. -/
theorem attachSourceDrawingBatch_prefix (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    request.conventions <+: (attachSourceDrawingBatch request batch?).conventions :=
  ⟨[freshDrawingSource batch?], by simp [attachSourceDrawingBatch]⟩

/-- The prior channel is exactly the `dropLast` of the result. -/
@[simp] theorem attachSourceDrawingBatch_dropLast (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (attachSourceDrawingBatch request batch?).conventions.dropLast = request.conventions := by
  simp [attachSourceDrawingBatch]

/-- The last record is exactly the fresh record. -/
@[simp] theorem attachSourceDrawingBatch_getLast? (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (attachSourceDrawingBatch request batch?).conventions.getLast? =
      some (freshDrawingSource batch?) := by
  simp [attachSourceDrawingBatch]

/-- The channel gains exactly one record. -/
@[simp] theorem attachSourceDrawingBatch_length (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (attachSourceDrawingBatch request batch?).conventions.length =
      request.conventions.length + 1 := by
  simp [attachSourceDrawingBatch]

/-- Old lookups are unchanged at every prior position. -/
theorem attachSourceDrawingBatch_get?_old (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) (index : Nat)
    (bound : index < request.conventions.length) :
    (attachSourceDrawingBatch request batch?).conventions[index]? =
      request.conventions[index]? := by
  rw [attachSourceDrawingBatch_conventions, List.getElem?_append_left bound]

/-- Every prior record is still a member of the augmented channel. -/
theorem attachSourceDrawingBatch_prior_mem (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) {source : OrganicConventionSource V}
    (member : source ∈ request.conventions) :
    source ∈ (attachSourceDrawingBatch request batch?).conventions := by
  rw [attachSourceDrawingBatch_conventions]
  exact List.mem_append_left _ member

/-- A prior record whose cue channel is absent stays absent. -/
theorem attachSourceDrawingBatch_prior_cues?_none (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) {source : OrganicConventionSource V}
    (member : source ∈ request.conventions) (observed : source.cues? = none) :
    source ∈ (attachSourceDrawingBatch request batch?).conventions ∧ source.cues? = none :=
  ⟨attachSourceDrawingBatch_prior_mem request batch? member, observed⟩

/-- A prior record whose cue channel is present-empty stays present-empty. -/
theorem attachSourceDrawingBatch_prior_cues?_some_nil (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) {source : OrganicConventionSource V}
    (member : source ∈ request.conventions) (observed : source.cues? = some []) :
    source ∈ (attachSourceDrawingBatch request batch?).conventions ∧
      source.cues? = some [] :=
  ⟨attachSourceDrawingBatch_prior_mem request batch? member, observed⟩

/-- The last record's cue channel is exactly the batch's presence/cue payload: absent for `none`,
`some []` for a present empty batch, and `some batch.cues` otherwise. -/
theorem attachSourceDrawingBatch_last_cues? (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    ((attachSourceDrawingBatch request batch?).conventions.getLast?).bind
        (fun last => last.cues?) =
      batch?.map (fun batch => batch.cues) := by
  rw [attachSourceDrawingBatch_getLast?]
  cases batch? with
  | none => rfl
  | some batch => rfl

/-! ## Canonical output -/

/-- The canonical convention channel is the common-enumeration image of the augmented channel. -/
theorem canonicalAssemble_attachSourceDrawingBatch_conventions
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (canonicalAssemble enumeration (attachSourceDrawingBatch request batch?)).state.conventions =
      ConventionChannel.encode enumeration
        (request.conventions ++ [freshDrawingSource batch?]) := by
  rw [canonicalAssemble_conventions, attachSourceDrawingBatch_conventions]

/-- The canonical last record is the encoded fresh record. -/
theorem canonicalAssemble_attachSourceDrawingBatch_getLast?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (canonicalAssemble enumeration
        (attachSourceDrawingBatch request batch?)).state.conventions.getLast? =
      some (OrganicConventionSource.encode enumeration (freshDrawingSource batch?)) := by
  rw [canonicalAssemble_attachSourceDrawingBatch_conventions, ConventionChannel.encode_getLast?]
  simp

/-- The canonical channel's first `length - 1` records are exactly the encoded prior channel. -/
theorem canonicalAssemble_attachSourceDrawingBatch_dropLast
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (canonicalAssemble enumeration
        (attachSourceDrawingBatch request batch?)).state.conventions.dropLast =
      ConventionChannel.encode enumeration request.conventions := by
  rw [canonicalAssemble_attachSourceDrawingBatch_conventions]
  simp [ConventionChannel.encode]

/-- The canonical output graph is the common relabelling of the request graph. -/
@[simp] theorem canonicalAssemble_attachSourceDrawingBatch_graph
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (canonicalAssemble enumeration
        (attachSourceDrawingBatch request batch?)).state.graph =
      relabelGraph enumeration request.graph := by
  rw [canonicalAssemble_state_graph, attachSourceDrawingBatch_graph]

/-- The actual decoded core of the canonical assembly is exactly the augmented request. -/
theorem decodedCore_attachSourceDrawingBatch
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    decodedCore (canonicalAssemble enumeration (attachSourceDrawingBatch request batch?)) =
      attachSourceDrawingBatch request batch? := by
  simpa [decodedCore] using
    decode_canonicalAssemble enumeration (attachSourceDrawingBatch request batch?)

/-- The decoded common graph is exactly the request graph. -/
@[simp] theorem decodedCore_attachSourceDrawingBatch_graph
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (decodedCore
        (canonicalAssemble enumeration (attachSourceDrawingBatch request batch?))).graph =
      request.graph := by
  rw [decodedCore_attachSourceDrawingBatch, attachSourceDrawingBatch_graph]

/-- The complete prior request recovered from the actual canonical output only: decode the whole
closed core, then cut the one fresh convention record.  No original request and no saved binding
is an argument. -/
noncomputable def decodedPriorRequest (canonical : CanonicalOrganicMolecularRepresentation V) :
    OrganicMolecularEvidence V :=
  { decodedCore canonical with
    conventions := (decodedCore canonical).conventions.dropLast }

/-- The output-only prior request is the *whole* original request, not merely its convention
channel: all fourteen non-convention fields and every prior convention record are recovered via the
existing `decode_canonicalAssemble` core inverse, and `dropLast` removes exactly the appended fresh
record. -/
theorem decodedPriorRequest_canonicalAssemble
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    decodedPriorRequest
        (canonicalAssemble enumeration (attachSourceDrawingBatch request batch?)) =
      request := by
  unfold decodedPriorRequest
  rw [decodedCore_attachSourceDrawingBatch]
  unfold attachSourceDrawingBatch
  simp only [List.dropLast_concat]

end Batch

/-! ## Ordered cue extraction -/

section Extraction

/-- The ordered glyph payloads of a cue list.  Only `bondGlyph` cues contribute. -/
def drawingGlyphs (cues : List (ConventionCue V)) : List (BondGlyph V) :=
  cues.filterMap fun cue =>
    match cue with
    | .bondGlyph glyph => some glyph
    | _ => none

/-- The ordered crossing payloads of a cue list.  Only `bondCrossing` cues contribute. -/
def drawingCrossings (cues : List (ConventionCue V)) : List (BondCrossingGlyph V) :=
  cues.filterMap fun cue =>
    match cue with
    | .bondCrossing crossing => some crossing
    | _ => none

/-- A leading glyph cue is extracted exactly. -/
@[simp] theorem drawingGlyphs_bondGlyph_cons (glyph : BondGlyph V)
    (cues : List (ConventionCue V)) :
    drawingGlyphs (ConventionCue.bondGlyph glyph :: cues) =
      glyph :: drawingGlyphs cues := rfl

/-- A leading crossing cue contributes no glyph payload. -/
@[simp] theorem drawingGlyphs_bondCrossing_cons (crossing : BondCrossingGlyph V)
    (cues : List (ConventionCue V)) :
    drawingGlyphs (ConventionCue.bondCrossing crossing :: cues) =
      drawingGlyphs cues := rfl

/-- A leading glyph cue contributes no crossing payload. -/
@[simp] theorem drawingCrossings_bondGlyph_cons (glyph : BondGlyph V)
    (cues : List (ConventionCue V)) :
    drawingCrossings (ConventionCue.bondGlyph glyph :: cues) =
      drawingCrossings cues := rfl

/-- A leading crossing cue is extracted exactly. -/
@[simp] theorem drawingCrossings_bondCrossing_cons (crossing : BondCrossingGlyph V)
    (cues : List (ConventionCue V)) :
    drawingCrossings (ConventionCue.bondCrossing crossing :: cues) =
      crossing :: drawingCrossings cues := rfl

/-- Extracting the ordered glyph payloads commutes with concatenation. -/
@[simp] theorem drawingGlyphs_append (first second : List (ConventionCue V)) :
    drawingGlyphs (first ++ second) = drawingGlyphs first ++ drawingGlyphs second := by
  simp [drawingGlyphs]

/-- Extracting the ordered crossing payloads commutes with concatenation. -/
@[simp] theorem drawingCrossings_append (first second : List (ConventionCue V)) :
    drawingCrossings (first ++ second) = drawingCrossings first ++ drawingCrossings second := by
  simp [drawingCrossings]

/-- Extraction inverts a compiled glyph-cue list exactly, order and duplicates included. -/
@[simp] theorem drawingGlyphs_bondGlyphs (glyphs : List (BondGlyph V)) :
    drawingGlyphs (glyphs.map ConventionCue.bondGlyph) = glyphs := by
  induction glyphs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, drawingGlyphs_bondGlyph_cons, inductionHypothesis]

/-- Extraction inverts a compiled crossing-cue list exactly. -/
@[simp] theorem drawingCrossings_bondCrossings (crossings : List (BondCrossingGlyph V)) :
    drawingCrossings (crossings.map ConventionCue.bondCrossing) = crossings := by
  induction crossings with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, drawingCrossings_bondCrossing_cons, inductionHypothesis]

/-- Glyph extraction ignores crossing cues. -/
@[simp] theorem drawingGlyphs_bondCrossings (crossings : List (BondCrossingGlyph V)) :
    drawingGlyphs (crossings.map ConventionCue.bondCrossing) = [] := by
  induction crossings with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, drawingGlyphs_bondCrossing_cons, inductionHypothesis]

/-- Crossing extraction ignores glyph cues. -/
@[simp] theorem drawingCrossings_bondGlyphs (glyphs : List (BondGlyph V)) :
    drawingCrossings (glyphs.map ConventionCue.bondGlyph) = [] := by
  induction glyphs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, drawingCrossings_bondGlyph_cons, inductionHypothesis]

/-- The ordered payloads recovered from a canonical record. -/
structure DecodedDrawingBatch (V : Type*) where
  /-- The ordered decoded glyph payloads. -/
  glyphs : List (BondGlyph V)
  /-- The ordered decoded crossing payloads. -/
  crossings : List (BondCrossingGlyph V)

/-- Absent and present-empty batch payloads are distinguished by the decoder. -/
theorem decodedDrawingBatch_absent_ne_present_empty :
    (none : Option (DecodedDrawingBatch V)) ≠
      some ({ glyphs := [], crossings := [] } : DecodedDrawingBatch V) := by
  simp

end Extraction

/-! ## The request-free decoder -/

section Decoder

variable [DecidableEq V] [Fintype V]

/-- Glyph extraction of a compiled source-glyph list is exactly the compiled glyph list. -/
@[simp] theorem drawingGlyphs_compiled (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) :
    drawingGlyphs (compileSuppliedCues graph glyphs) = compileSuppliedGlyphs graph glyphs := by
  rw [← compileSuppliedGlyphs_map_bondGlyph, drawingGlyphs_bondGlyphs]

/-- Crossing extraction ignores compiled source-glyph cues. -/
@[simp] theorem drawingCrossings_compiledGlyphs (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) :
    drawingCrossings (compileSuppliedCues graph glyphs) = [] := by
  rw [← compileSuppliedGlyphs_map_bondGlyph, drawingCrossings_bondGlyphs]

/-- Glyph extraction ignores compiled crossing cues. -/
@[simp] theorem drawingGlyphs_compiledCrossings (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) :
    drawingGlyphs (compileBatchCrossingCues graph glyphs prefixLength crossings) = [] := by
  rw [← compileBatchCrossings_map_bondCrossing, drawingGlyphs_bondCrossings]

/-- Crossing extraction of a compiled crossing list is exactly the compiled crossing list. -/
@[simp] theorem drawingCrossings_compiledCrossings
    (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (prefixLength : Nat)
    (crossings : List (DrawingBatchCrossing graph glyphs)) :
    drawingCrossings (compileBatchCrossingCues graph glyphs prefixLength crossings) =
      compileBatchCrossings graph glyphs prefixLength crossings := by
  rw [← compileBatchCrossings_map_bondCrossing, drawingCrossings_bondCrossings]

/-- The decoded payload of a fresh batch is exactly the ordered compiled payloads. -/
theorem decodedBatch_of_batch {graph : FiniteAtomInteractionHypergraph V}
    (batch : SuppliedDrawingBatch graph) :
    ({ glyphs := drawingGlyphs batch.cues,
       crossings := drawingCrossings batch.cues } : DecodedDrawingBatch V) =
      { glyphs := compileSuppliedGlyphs graph batch.glyphs,
        crossings := compileBatchCrossings graph batch.glyphs 0 batch.crossings } := by
  unfold SuppliedDrawingBatch.cues
  rw [drawingGlyphs_append, drawingCrossings_append, drawingGlyphs_compiled,
    drawingCrossings_compiledGlyphs, drawingGlyphs_compiledCrossings,
    drawingCrossings_compiledCrossings]
  simp

/-- The prior channel of a representation: every record except the last, decoded by the common
inverse equivalence. -/
def decodedDrawingPrior (e : V ≃ W) (channel : ConventionChannel W) : ConventionChannel V :=
  (ConventionChannel.decode e channel).dropLast

/-- The optional batch payload of a representation.  Presence is read from the last record's cue
channel: `none` stays absent, `some []` stays present-empty, and `some cues` gives the ordered
glyph/crossing payloads. -/
def decodedDrawingBatch? (e : V ≃ W) (channel : ConventionChannel W) :
    Option (DecodedDrawingBatch V) :=
  match channel.getLast? with
  | none => none
  | some last =>
      match (OrganicConventionSource.decode e last).cues? with
      | none => none
      | some cues =>
          some { glyphs := drawingGlyphs cues, crossings := drawingCrossings cues }

/-- The request-free decoder of a convention channel: prior channel plus optional fresh batch. -/
def decodeDrawingBatch (e : V ≃ W) (channel : ConventionChannel W) :
    ConventionChannel V × Option (DecodedDrawingBatch V) :=
  (decodedDrawingPrior e channel, decodedDrawingBatch? e channel)

/-- The actual canonical-output decoder.  It reads only the canonical record's own atom
equivalence and encoded convention channel; no original request is available to it. -/
def decodeDrawingBatchFromCanonical (canonical : CanonicalOrganicMolecularRepresentation V) :
    ConventionChannel V × Option (DecodedDrawingBatch V) :=
  decodeDrawingBatch canonical.atomEquiv canonical.state.conventions

/-- The decoder recovers the prior channel exactly from the actual canonical output. -/
theorem decodedDrawingPrior_canonicalAssemble
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (decodeDrawingBatch enumeration
        (canonicalAssemble enumeration
          (attachSourceDrawingBatch request batch?)).state.conventions).1 =
      request.conventions := by
  unfold decodeDrawingBatch decodedDrawingPrior
  rw [canonicalAssemble_attachSourceDrawingBatch_conventions,
    ConventionChannel.decode_encode, List.dropLast_concat]

/-- The decoder recovers the optional batch presence and the ordered compiled payloads exactly. -/
theorem decodedDrawingBatch?_canonicalAssemble
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    (decodeDrawingBatch enumeration
        (canonicalAssemble enumeration
          (attachSourceDrawingBatch request batch?)).state.conventions).2 =
      batch?.map (fun batch =>
        ({ glyphs := compileSuppliedGlyphs request.graph batch.glyphs,
           crossings := compileBatchCrossings request.graph batch.glyphs 0 batch.crossings } :
          DecodedDrawingBatch V)) := by
  unfold decodeDrawingBatch decodedDrawingBatch?
  rw [canonicalAssemble_attachSourceDrawingBatch_conventions,
    ConventionChannel.encode_getLast?]
  cases batch? with
  | none =>
      simp [freshDrawingSource]
  | some batch =>
      rw [List.getLast?_concat, Option.map_some]
      simp [freshDrawingSource, decodedBatch_of_batch batch]

/-- Exact joint readback: prior channel and optional ordered batch payloads. -/
theorem decodeDrawingBatch_canonicalAssemble
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    decodeDrawingBatch enumeration
        (canonicalAssemble enumeration
          (attachSourceDrawingBatch request batch?)).state.conventions =
      (request.conventions,
        batch?.map (fun batch =>
          ({ glyphs := compileSuppliedGlyphs request.graph batch.glyphs,
             crossings := compileBatchCrossings request.graph batch.glyphs 0 batch.crossings } :
            DecodedDrawingBatch V))) :=
  Prod.ext (decodedDrawingPrior_canonicalAssemble enumeration request batch?)
    (decodedDrawingBatch?_canonicalAssemble enumeration request batch?)

/-- The actual canonical-output decoder recovers the same prior channel and batch exactly. -/
theorem decodeDrawingBatchFromCanonical_canonicalAssemble
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch? : Option (SuppliedDrawingBatch request.graph)) :
    decodeDrawingBatchFromCanonical
        (canonicalAssemble enumeration (attachSourceDrawingBatch request batch?)) =
      (request.conventions,
        batch?.map (fun batch =>
          ({ glyphs := compileSuppliedGlyphs request.graph batch.glyphs,
             crossings := compileBatchCrossings request.graph batch.glyphs 0 batch.crossings } :
            DecodedDrawingBatch V))) := by
  unfold decodeDrawingBatchFromCanonical
  exact decodeDrawingBatch_canonicalAssemble enumeration request batch?

/-- Absent batch: the decoded optional payload is genuinely absent. -/
theorem decodeDrawingBatch_canonicalAssemble_absent
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V) :
    (decodeDrawingBatch enumeration
        (canonicalAssemble enumeration
          (attachSourceDrawingBatch request none)).state.conventions).2 = none := by
  rw [decodedDrawingBatch?_canonicalAssemble]
  rfl

/-- Present empty batch: the decoded payload is present and empty, not absent. -/
theorem decodeDrawingBatch_canonicalAssemble_present_empty
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V) :
    (decodeDrawingBatch enumeration
        (canonicalAssemble enumeration
          (attachSourceDrawingBatch request
            (some (⟨[], []⟩ : SuppliedDrawingBatch request.graph)))).state.conventions).2 =
      some ({ glyphs := [], crossings := [] } : DecodedDrawingBatch V) := by
  rw [decodedDrawingBatch?_canonicalAssemble]
  simp [compileSuppliedGlyphs, compileBatchCrossings, compileSuppliedCrossings]

/-- Exact glyph-payload lookup from the canonical output, position by position. -/
theorem decodeDrawingBatch_canonicalAssemble_glyph_get?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch : SuppliedDrawingBatch request.graph) (position : Fin batch.glyphs.length) :
    ((decodeDrawingBatch enumeration
        (canonicalAssemble enumeration
          (attachSourceDrawingBatch request (some batch))).state.conventions).2.bind
      (fun decoded => decoded.glyphs[position.val]?)) =
      some (batch.glyphs.get position).toBondGlyph := by
  rw [decodedDrawingBatch?_canonicalAssemble]
  exact compileSuppliedGlyphs_get?_bounded request.graph batch.glyphs position.val position.isLt

/-- Exact crossing-payload lookup from the canonical output, position by position. -/
theorem decodeDrawingBatch_canonicalAssemble_crossing_get?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch : SuppliedDrawingBatch request.graph) (position : Fin batch.crossings.length) :
    ((decodeDrawingBatch enumeration
        (canonicalAssemble enumeration
          (attachSourceDrawingBatch request (some batch))).state.conventions).2.bind
      (fun decoded => decoded.crossings[position.val]?)) =
      some (compileBatchCrossing request.graph batch.glyphs 0
        (batch.crossings.get position)) := by
  rw [decodedDrawingBatch?_canonicalAssemble]
  exact compileBatchCrossings_get?_bounded request.graph batch.glyphs 0 batch.crossings
    position.val position.isLt

end Decoder

/-! ## Actual graph occurrences -/

section Occurrences

variable [DecidableEq V] [Fintype V]

/-- **Assembled occurrence retention.**  After the actual upstream `assemble`, every supplied
glyph still names the same bounded interaction occurrence of the actual assembled graph and both
endpoints are participants of that occurrence. -/
theorem assembled_drawingBatch_glyph_occurrence
    (request : OrganicMolecularEvidence V) (batch : SuppliedDrawingBatch request.graph)
    (position : Fin batch.glyphs.length) :
    ∃ bound : (batch.glyphs.get position).toBondGlyph.interactionIndex <
        (assemble (attachSourceDrawingBatch request (some batch))).stateGraph.interactions.length,
      (batch.glyphs.get position).toBondGlyph.source ∈
          ((assemble (attachSourceDrawingBatch request (some batch))).stateGraph.interactions.get
            ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1 ∧
        (batch.glyphs.get position).toBondGlyph.target ∈
          ((assemble (attachSourceDrawingBatch request (some batch))).stateGraph.interactions.get
            ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1 := by
  let request' := attachSourceDrawingBatch request (some batch)
  let glyph := batch.glyphs.get position
  let payload := glyph.toBondGlyph
  have hgraph : (assemble request').stateGraph = request.graph :=
    (assemble_stateGraph_eq_request_graph request').trans
      (attachSourceDrawingBatch_graph request (some batch))
  have hlist : request.graph.interactions =
      (assemble request').stateGraph.interactions :=
    congrArg (fun graph : FiniteAtomInteractionHypergraph V => graph.interactions) hgraph.symm
  have hbound : payload.interactionIndex <
      (assemble request').stateGraph.interactions.length := by
    rw [hgraph]
    exact glyph.interactionIndex.isLt
  refine ⟨hbound, ?_, ?_⟩
  · have hget : request.graph.interactions.get glyph.interactionIndex =
        (assemble request').stateGraph.interactions.get ⟨payload.interactionIndex, hbound⟩ :=
      list_get_eq_of_eq hlist glyph.interactionIndex ⟨payload.interactionIndex, hbound⟩ rfl
    rw [← hget]
    exact glyph.source_mem
  · have hget : request.graph.interactions.get glyph.interactionIndex =
        (assemble request').stateGraph.interactions.get ⟨payload.interactionIndex, hbound⟩ :=
      list_get_eq_of_eq hlist glyph.interactionIndex ⟨payload.interactionIndex, hbound⟩ rfl
    rw [← hget]
    exact glyph.target_mem

/-- The bounded assembled occurrence is literally the request graph's supplied occurrence. -/
theorem assembled_drawingBatch_glyph_occurrence_eq
    (request : OrganicMolecularEvidence V) (batch : SuppliedDrawingBatch request.graph)
    (position : Fin batch.glyphs.length) :
    ∃ bound : (batch.glyphs.get position).toBondGlyph.interactionIndex <
        (assemble (attachSourceDrawingBatch request (some batch))).stateGraph.interactions.length,
      (assemble (attachSourceDrawingBatch request (some batch))).stateGraph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩ =
        request.graph.interactions.get (batch.glyphs.get position).interactionIndex := by
  let request' := attachSourceDrawingBatch request (some batch)
  let glyph := batch.glyphs.get position
  let payload := glyph.toBondGlyph
  have hgraph : (assemble request').stateGraph = request.graph :=
    (assemble_stateGraph_eq_request_graph request').trans
      (attachSourceDrawingBatch_graph request (some batch))
  have hlist : request.graph.interactions =
      (assemble request').stateGraph.interactions :=
    congrArg (fun graph : FiniteAtomInteractionHypergraph V => graph.interactions) hgraph.symm
  have hbound : payload.interactionIndex <
      (assemble request').stateGraph.interactions.length := by
    rw [hgraph]
    exact glyph.interactionIndex.isLt
  refine ⟨hbound, ?_⟩
  exact (list_get_eq_of_eq hlist glyph.interactionIndex
    ⟨payload.interactionIndex, hbound⟩ rfl).symm

/-- **Canonical occurrence retention with the common enumeration.**  In the actual canonical
output, a supplied glyph's stored occurrence index is bounded, its occurrence is exactly the
common-enumeration relabelling of the supplied source occurrence, and both encoded endpoints are
participants of it. -/
theorem canonical_drawingBatch_glyph_occurrence
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch : SuppliedDrawingBatch request.graph) (position : Fin batch.glyphs.length) :
    let assembled :=
      canonicalAssemble enumeration (attachSourceDrawingBatch request (some batch))
    ∃ bound : (batch.glyphs.get position).toBondGlyph.interactionIndex <
        assembled.state.graph.interactions.length,
      assembled.state.graph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩ =
        relabelInteractionEdge enumeration
          (request.graph.interactions.get (batch.glyphs.get position).interactionIndex) ∧
      enumeration (batch.glyphs.get position).source ∈
        (assembled.state.graph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1 ∧
      enumeration (batch.glyphs.get position).target ∈
        (assembled.state.graph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1 := by
  let assembled := canonicalAssemble enumeration (attachSourceDrawingBatch request (some batch))
  let glyph := batch.glyphs.get position
  let payload := glyph.toBondGlyph
  have hgraph : assembled.state.graph = relabelGraph enumeration request.graph := by
    unfold assembled
    rw [canonicalAssemble_state_graph, attachSourceDrawingBatch_graph]
  have hboundRel : payload.interactionIndex <
      (relabelGraph enumeration request.graph).interactions.length := by
    rw [relabelGraph_interactions_length]
    exact glyph.interactionIndex.isLt
  have hbound : payload.interactionIndex < assembled.state.graph.interactions.length := by
    rw [hgraph]
    exact hboundRel
  have hgetRel : (relabelGraph enumeration request.graph).interactions.get
      ⟨payload.interactionIndex, hboundRel⟩ =
        relabelInteractionEdge enumeration
          (request.graph.interactions.get glyph.interactionIndex) := by
    have hidx : (⟨payload.interactionIndex, hboundRel⟩ :
        Fin (relabelGraph enumeration request.graph).interactions.length) =
        relabelInteractionIndex enumeration glyph.interactionIndex := by
      apply Fin.ext
      rfl
    rw [hidx, relabelGraph_interactions_get]
  have hlist : (relabelGraph enumeration request.graph).interactions =
      assembled.state.graph.interactions :=
    congrArg (fun graph : FiniteAtomInteractionHypergraph (Fin (Fintype.card V)) =>
      graph.interactions) hgraph.symm
  have hget : assembled.state.graph.interactions.get ⟨payload.interactionIndex, hbound⟩ =
      (relabelGraph enumeration request.graph).interactions.get
        ⟨payload.interactionIndex, hboundRel⟩ :=
    (list_get_eq_of_eq hlist ⟨payload.interactionIndex, hboundRel⟩
      ⟨payload.interactionIndex, hbound⟩ rfl).symm
  refine ⟨hbound, ?_, ?_, ?_⟩
  · rw [hget, hgetRel]
  · rw [hget, hgetRel]
    exact List.mem_map.mpr ⟨glyph.source, glyph.source_mem, rfl⟩
  · rw [hget, hgetRel]
    exact List.mem_map.mpr ⟨glyph.target, glyph.target_mem, rfl⟩

/-- **Decoded common-graph occurrence.**  Reading only the actual canonical output, the decoded
common graph has the same occurrence index bounded, the occurrence payload equal to the supplied
request occurrence, and both endpoints as participants. -/
theorem decodedCore_drawingBatch_glyph_occurrence
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch : SuppliedDrawingBatch request.graph) (position : Fin batch.glyphs.length) :
    let decoded :=
      decodedCore (canonicalAssemble enumeration (attachSourceDrawingBatch request (some batch)))
    ∃ bound : (batch.glyphs.get position).toBondGlyph.interactionIndex <
        decoded.graph.interactions.length,
      decoded.graph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩ =
        request.graph.interactions.get (batch.glyphs.get position).interactionIndex ∧
      (batch.glyphs.get position).toBondGlyph.source ∈
        (decoded.graph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1 ∧
      (batch.glyphs.get position).toBondGlyph.target ∈
        (decoded.graph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1 := by
  let decoded :=
    decodedCore (canonicalAssemble enumeration (attachSourceDrawingBatch request (some batch)))
  let glyph := batch.glyphs.get position
  let payload := glyph.toBondGlyph
  have hgraph : decoded.graph = request.graph := by
    unfold decoded
    rw [decodedCore_attachSourceDrawingBatch_graph]
  have hboundReq : payload.interactionIndex < request.graph.interactions.length :=
    glyph.interactionIndex.isLt
  have hbound : payload.interactionIndex < decoded.graph.interactions.length := by
    rw [hgraph]
    exact hboundReq
  have hlist : request.graph.interactions = decoded.graph.interactions :=
    congrArg (fun graph : FiniteAtomInteractionHypergraph V => graph.interactions) hgraph.symm
  have hget : decoded.graph.interactions.get ⟨payload.interactionIndex, hbound⟩ =
      request.graph.interactions.get glyph.interactionIndex :=
    (list_get_eq_of_eq hlist glyph.interactionIndex ⟨payload.interactionIndex, hbound⟩ rfl).symm
  refine ⟨hbound, hget, ?_, ?_⟩
  · rw [hget]
    exact glyph.source_mem_of_nat_bound hboundReq
  · rw [hget]
    exact glyph.target_mem_of_nat_bound hboundReq

end Occurrences

/-! ## Reconstruction of proof-carrying raw records -/

section Reconstruction

variable [DecidableEq V] [Fintype V]

/-- Rebuild a proof-carrying supplied glyph from an exact retention payload plus bounds and
endpoint memberships.  The proofs are arguments, so callers can obtain them from a decoded common
graph. -/
def reconstructSuppliedGlyph (graph : FiniteAtomInteractionHypergraph V)
    (payload : BondGlyph V)
    (bound : payload.interactionIndex < graph.interactions.length)
    (source_mem : payload.source ∈
      (graph.interactions.get ⟨payload.interactionIndex, bound⟩).1)
    (target_mem : payload.target ∈
      (graph.interactions.get ⟨payload.interactionIndex, bound⟩).1) :
    SuppliedBondGlyph graph where
  interactionIndex := ⟨payload.interactionIndex, bound⟩
  source := payload.source
  target := payload.target
  source_mem := source_mem
  target_mem := target_mem
  oriented := payload.oriented
  hashConvention? := payload.hashConvention?
  wavyGeometry? := payload.wavyGeometry?
  purpose? := payload.purpose?

/-- The reconstructed record compiles back to exactly the payload it was built from. -/
@[simp] theorem reconstructSuppliedGlyph_toBondGlyph
    (graph : FiniteAtomInteractionHypergraph V) (payload : BondGlyph V)
    (bound : payload.interactionIndex < graph.interactions.length)
    (source_mem : payload.source ∈
      (graph.interactions.get ⟨payload.interactionIndex, bound⟩).1)
    (target_mem : payload.target ∈
      (graph.interactions.get ⟨payload.interactionIndex, bound⟩).1) :
    (reconstructSuppliedGlyph graph payload bound source_mem target_mem).toBondGlyph =
      payload := rfl

/-- Reconstructing from any bounds/memberships for the same payload recovers the original supplied
glyph.  The two membership arguments are proposition-valued, so proof irrelevance identifies them. -/
theorem reconstructSuppliedGlyph_eq (graph : FiniteAtomInteractionHypergraph V)
    (original : SuppliedBondGlyph graph)
    (bound : original.toBondGlyph.interactionIndex < graph.interactions.length)
    (source_mem : original.toBondGlyph.source ∈
      (graph.interactions.get ⟨original.toBondGlyph.interactionIndex, bound⟩).1)
    (target_mem : original.toBondGlyph.target ∈
      (graph.interactions.get ⟨original.toBondGlyph.interactionIndex, bound⟩).1) :
    reconstructSuppliedGlyph graph original.toBondGlyph bound source_mem target_mem = original := by
  obtain ⟨index, source, target, sourceMem, targetMem, oriented, hash, wavy, purpose⟩ := original
  simp only [SuppliedBondGlyph.toBondGlyph, reconstructSuppliedGlyph]

/-- The proof-carrying glyph is reconstructible from the decoded common graph, with both bounds
and memberships read there. -/
theorem decodedCore_drawingBatch_glyph_reconstruct
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (batch : SuppliedDrawingBatch request.graph) (position : Fin batch.glyphs.length) :
    let decoded :=
      decodedCore (canonicalAssemble enumeration (attachSourceDrawingBatch request (some batch)))
    ∃ (bound : (batch.glyphs.get position).toBondGlyph.interactionIndex <
          decoded.graph.interactions.length)
      (source_mem : (batch.glyphs.get position).toBondGlyph.source ∈
        (decoded.graph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1)
      (target_mem : (batch.glyphs.get position).toBondGlyph.target ∈
        (decoded.graph.interactions.get
          ⟨(batch.glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1),
      (reconstructSuppliedGlyph decoded.graph
        (batch.glyphs.get position).toBondGlyph bound source_mem target_mem).toBondGlyph =
        (batch.glyphs.get position).toBondGlyph := by
  obtain ⟨bound, _, source_mem, target_mem⟩ :=
    decodedCore_drawingBatch_glyph_occurrence enumeration request batch position
  exact ⟨bound, source_mem, target_mem, reconstructSuppliedGlyph_toBondGlyph _ _ _ _ _⟩

/-- Rebuild a proof-carrying batch crossing from an exact retention payload, bounds in the batch's
own glyph list, and the two payload equations. -/
def reconstructBatchCrossing (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (payload : BondCrossingGlyph V)
    (firstBound : payload.firstCueIndex < glyphs.length)
    (secondBound : payload.secondCueIndex < glyphs.length) :
    DrawingBatchCrossing graph glyphs where
  first := ⟨payload.firstCueIndex, firstBound⟩
  second := ⟨payload.secondCueIndex, secondBound⟩
  crossing := payload.crossing

/-- Compiling the reconstructed crossing at prefix `0` recovers exactly the payload. -/
theorem compileBatchCrossing_reconstruct
    (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (payload : BondCrossingGlyph V)
    (firstBound : payload.firstCueIndex < glyphs.length)
    (secondBound : payload.secondCueIndex < glyphs.length)
    (firstPayload : payload.first =
      (glyphs.get ⟨payload.firstCueIndex, firstBound⟩).toBondGlyph)
    (secondPayload : payload.second =
      (glyphs.get ⟨payload.secondCueIndex, secondBound⟩).toBondGlyph) :
    compileBatchCrossing graph glyphs 0
        (reconstructBatchCrossing graph glyphs payload firstBound secondBound) =
        payload := by
  cases payload with
  | mk firstCueIndex secondCueIndex first second crossing =>
      simp only [compileBatchCrossing, compileSuppliedCrossing, reconstructBatchCrossing]
      rw [← firstPayload, ← secondPayload]
      simp

/-- The compiled crossing's own cue indices are bounded in the batch's glyph list, and the two
compiled payloads satisfy the reconstruction equations.  Hence every compiled crossing is
reconstructible from its exact payload alone. -/
theorem compiled_crossing_reconstructible
    (graph : FiniteAtomInteractionHypergraph V)
    (glyphs : List (SuppliedBondGlyph graph)) (crossing : DrawingBatchCrossing graph glyphs) :
    ∃ (firstBound : (compileBatchCrossing graph glyphs 0 crossing).firstCueIndex < glyphs.length)
      (secondBound : (compileBatchCrossing graph glyphs 0 crossing).secondCueIndex < glyphs.length),
      (compileBatchCrossing graph glyphs 0 crossing).first =
        (glyphs.get ⟨(compileBatchCrossing graph glyphs 0 crossing).firstCueIndex,
          firstBound⟩).toBondGlyph ∧
      (compileBatchCrossing graph glyphs 0 crossing).second =
        (glyphs.get ⟨(compileBatchCrossing graph glyphs 0 crossing).secondCueIndex,
          secondBound⟩).toBondGlyph ∧
      compileBatchCrossing graph glyphs 0
        (reconstructBatchCrossing graph glyphs (compileBatchCrossing graph glyphs 0 crossing)
          firstBound secondBound) =
        compileBatchCrossing graph glyphs 0 crossing := by
  have hfirst : (compileBatchCrossing graph glyphs 0 crossing).firstCueIndex <
      glyphs.length := by
    simp [compileBatchCrossing]
  have hsecond : (compileBatchCrossing graph glyphs 0 crossing).secondCueIndex <
      glyphs.length := by
    simp [compileBatchCrossing]
  have hfirstPayload : (compileBatchCrossing graph glyphs 0 crossing).first =
      (glyphs.get ⟨(compileBatchCrossing graph glyphs 0 crossing).firstCueIndex,
        hfirst⟩).toBondGlyph := by
    simp [compileBatchCrossing]
  have hsecondPayload : (compileBatchCrossing graph glyphs 0 crossing).second =
      (glyphs.get ⟨(compileBatchCrossing graph glyphs 0 crossing).secondCueIndex,
        hsecond⟩).toBondGlyph := by
    simp [compileBatchCrossing]
  exact ⟨hfirst, hsecond, hfirstPayload, hsecondPayload,
    compileBatchCrossing_reconstruct graph glyphs (compileBatchCrossing graph glyphs 0 crossing)
      hfirst hsecond hfirstPayload hsecondPayload⟩

end Reconstruction

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the decisive endpoints -/

assert_kernel_only TetraStereo.OneCenter.freshDrawingSource_none_ne_some_empty
assert_kernel_only TetraStereo.OneCenter.attachSourceDrawingBatch_conventions
assert_kernel_only TetraStereo.OneCenter.attachSourceDrawingBatch_preserves_nonconvention
assert_kernel_only TetraStereo.OneCenter.attachSourceDrawingBatch_prefix
assert_kernel_only TetraStereo.OneCenter.attachSourceDrawingBatch_dropLast
assert_kernel_only TetraStereo.OneCenter.attachSourceDrawingBatch_getLast?
assert_kernel_only TetraStereo.OneCenter.attachSourceDrawingBatch_prior_cues?_none
assert_kernel_only TetraStereo.OneCenter.attachSourceDrawingBatch_prior_cues?_some_nil
assert_kernel_only TetraStereo.OneCenter.attachSourceDrawingBatch_last_cues?
assert_kernel_only TetraStereo.OneCenter.decodedCore_attachSourceDrawingBatch
assert_kernel_only TetraStereo.OneCenter.decodedPriorRequest_canonicalAssemble
assert_kernel_only TetraStereo.OneCenter.decodedDrawingPrior_canonicalAssemble
assert_kernel_only TetraStereo.OneCenter.decodedDrawingBatch?_canonicalAssemble
assert_kernel_only TetraStereo.OneCenter.decodeDrawingBatch_canonicalAssemble
assert_kernel_only TetraStereo.OneCenter.decodeDrawingBatchFromCanonical_canonicalAssemble
assert_kernel_only TetraStereo.OneCenter.decodeDrawingBatch_canonicalAssemble_absent
assert_kernel_only TetraStereo.OneCenter.decodeDrawingBatch_canonicalAssemble_present_empty
assert_kernel_only TetraStereo.OneCenter.decodeDrawingBatch_canonicalAssemble_glyph_get?
assert_kernel_only TetraStereo.OneCenter.decodeDrawingBatch_canonicalAssemble_crossing_get?
assert_kernel_only TetraStereo.OneCenter.canonical_drawingBatch_glyph_occurrence
assert_kernel_only TetraStereo.OneCenter.decodedCore_drawingBatch_glyph_occurrence
assert_kernel_only TetraStereo.OneCenter.decodedCore_drawingBatch_glyph_reconstruct
assert_kernel_only TetraStereo.OneCenter.compileBatchCrossing_reconstruct
assert_kernel_only TetraStereo.OneCenter.compiled_crossing_reconstructible
