import TetraStereo.OneCenter.OrganicStereoDrawingConventions
import TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport
open OrganicStereoSpatialSupportMolecularAssembly

variable {V W : Type}

/-!
# Source-supplied bond-glyph ingress

This leaf is the *structural* bridge from a source-supplied bond glyph to the existing drawing
convention channel.  Nothing here interprets a wedge, chooses a hash convention, decides that a
style is recommended, or judges stereochemical applicability.

## The supplied record

`SuppliedBondGlyph graph` stores:

* a source interaction occurrence as `Fin graph.interactions.length`;
* both endpoint atoms, in the supplied written order;
* a proof that each endpoint belongs to *that exact* occurrence (the participant list of the
  interaction at the supplied bound);
* the complete existing `IUPACDrawing2006.ST0.OrientedBond` record (style and explicit narrow end);
* the optional existing `HashConvention`, `WavyGeometry` and `BondPurpose` records.

The ingress deliberately requires no binary interaction, no interaction kind, no arity equal to
two and no stereochemical applicability.  `Fin graph.interactions.length` plus the two membership
proofs is the *whole* structural restriction; in particular an interaction may have any arity
`≥ 2`, as `FiniteAtomInteractionHypergraph` allows.  The interpretation of the retained tokens is
out of scope and is never derived here.

`SuppliedBondGlyph.toBondGlyph` compiles the record to the retention-layer `BondGlyph` with its
plain `Nat` occurrence index; the bound proof is not stored in the retention layer.

## Attaching cues to real evidence

`attachGlyphCues` appends generated `bondGlyph` cues to the *last existing*
`OrganicConventionSource` of an actual `OrganicMolecularEvidence`, or creates one provenance record
when the convention channel is empty.  Appending preserves the pre-existing cue sequence as a
prefix and preserves every other field of every pre-existing record, including the
absence/present-empty distinction (`appendCues` and `attachCuesToLast` are the identity on an empty
cue list).  Every non-convention field of the evidence is untouched, so all correlations between
the graph, conformation, optional channels, coordinates, roles, diagram data and frames survive.

The main structural theorem `assembled_glyph_occurrence` shows that after the *actual* upstream
`assemble`, each inserted glyph still names the same bounded interaction occurrence and both
memberships hold there.  The canonical results use the *actual* `canonicalAssemble` and the actual
`decodedCore` decoder: the decoded augmented core is exactly the attached request, and the
canonical convention channel is exactly the common-enumeration encoding of the augmented channel.
-/

section Supplied

variable [DecidableEq V] [Fintype V]

/-! ## The supplied source record -/

/-- A source-supplied bond glyph.  The occurrence index is a bounded `Fin`, and both endpoints
carry membership proofs for that exact occurrence.  No interaction kind, arity restriction beyond
the graph's own `≥ 2`, or stereochemical judgment is required. -/
structure SuppliedBondGlyph (graph : FiniteAtomInteractionHypergraph V) where
  /-- The supplied interaction occurrence, bounded by the actual graph. -/
  interactionIndex : Fin graph.interactions.length
  /-- First endpoint in the supplied written order. -/
  source : V
  /-- Second endpoint in the supplied written order. -/
  target : V
  /-- The source endpoint is a participant of exactly this occurrence. -/
  source_mem : source ∈ (graph.interactions.get interactionIndex).1
  /-- The target endpoint is a participant of exactly this occurrence. -/
  target_mem : target ∈ (graph.interactions.get interactionIndex).1
  /-- The complete supplied orientation record: style and explicit narrow end. -/
  oriented : IUPACDrawing2006.ST0.OrientedBond
  /-- The supplied hash-convention token, absent or present exactly as supplied. -/
  hashConvention? : Option IUPACDrawing2006.ST0.HashConvention := none
  /-- The supplied wavy-geometry record, absent or present exactly as supplied. -/
  wavyGeometry? : Option IUPACDrawing2006.ST0.WavyGeometry := none
  /-- The supplied bond-purpose token, absent or present exactly as supplied. -/
  purpose? : Option IUPACDrawing2006.ST0.BondPurpose := none

namespace SuppliedBondGlyph

variable {graph : FiniteAtomInteractionHypergraph V}

/-- Compile the supplied record to the retention-layer glyph.  The occurrence bound is dropped
from the stored payload: `BondGlyph.interactionIndex` is the plain numeral. -/
def toBondGlyph (glyph : SuppliedBondGlyph graph) : BondGlyph V where
  interactionIndex := glyph.interactionIndex.val
  source := glyph.source
  target := glyph.target
  oriented := glyph.oriented
  hashConvention? := glyph.hashConvention?
  wavyGeometry? := glyph.wavyGeometry?
  purpose? := glyph.purpose?

/-- The compiled retention-layer cue.  It is exactly `ConventionCue.bondGlyph` applied to the
compiled glyph, so the ordered cue list retains glyph occurrence order and repeats. -/
def toCue (glyph : SuppliedBondGlyph graph) : ConventionCue V :=
  ConventionCue.bondGlyph glyph.toBondGlyph

/-! ### Exact payload recovery -/

@[simp] theorem toBondGlyph_interactionIndex (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.interactionIndex = glyph.interactionIndex.val := rfl

@[simp] theorem toBondGlyph_source (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.source = glyph.source := rfl

@[simp] theorem toBondGlyph_target (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.target = glyph.target := rfl

@[simp] theorem toBondGlyph_oriented (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.oriented = glyph.oriented := rfl

@[simp] theorem toBondGlyph_style (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.oriented.style = glyph.oriented.style := rfl

@[simp] theorem toBondGlyph_narrowEnd (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.oriented.narrowEnd = glyph.oriented.narrowEnd := rfl

@[simp] theorem toBondGlyph_hashConvention? (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.hashConvention? = glyph.hashConvention? := rfl

@[simp] theorem toBondGlyph_wavyGeometry? (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.wavyGeometry? = glyph.wavyGeometry? := rfl

@[simp] theorem toBondGlyph_purpose? (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.purpose? = glyph.purpose? := rfl

/-- The exact retention-layer record assembled from the supplied fields. -/
theorem toBondGlyph_eq_mk (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph =
      { interactionIndex := glyph.interactionIndex.val
        source := glyph.source
        target := glyph.target
        oriented := glyph.oriented
        hashConvention? := glyph.hashConvention?
        wavyGeometry? := glyph.wavyGeometry?
        purpose? := glyph.purpose? } := rfl

/-- Both endpoints survive in the supplied written order. -/
@[simp] theorem toCue_atomReferences (glyph : SuppliedBondGlyph graph) :
    glyph.toCue.atomReferences = [glyph.source, glyph.target] := rfl

/-- A bond glyph has no single-atom focus: `atom? = none` records the absence of a unique atom,
not the absence of references. -/
@[simp] theorem toCue_atom? (glyph : SuppliedBondGlyph graph) :
    glyph.toCue.atom? = none := rfl

/-- The compiled cue carries no non-atom locant. -/
@[simp] theorem toCue_locants (glyph : SuppliedBondGlyph graph) :
    glyph.toCue.locants = [] := rfl

/-- The compiled cue carries no Haworth numbering. -/
@[simp] theorem toCue_haworthNumbering? (glyph : SuppliedBondGlyph graph) :
    glyph.toCue.haworthNumbering? = none := rfl

/-! ### Structural endpoint evidence -/

/-- The source endpoint belongs to the bounded occurrence at the supplied `Fin` index. -/
theorem source_mem_occurrence (glyph : SuppliedBondGlyph graph) :
    glyph.source ∈ (graph.interactions.get glyph.interactionIndex).1 :=
  glyph.source_mem

/-- The target endpoint belongs to the bounded occurrence at the supplied `Fin` index. -/
theorem target_mem_occurrence (glyph : SuppliedBondGlyph graph) :
    glyph.target ∈ (graph.interactions.get glyph.interactionIndex).1 :=
  glyph.target_mem

/-- The stored numeral index is the bound value. -/
theorem interactionIndex_val (glyph : SuppliedBondGlyph graph) :
    glyph.toBondGlyph.interactionIndex = glyph.interactionIndex.val := rfl

/-- Both memberships can be read at any proof of the same numeral bound. -/
theorem source_mem_of_nat_bound (glyph : SuppliedBondGlyph graph)
    (bound : glyph.interactionIndex.val < graph.interactions.length) :
    glyph.source ∈ (graph.interactions.get ⟨glyph.interactionIndex.val, bound⟩).1 := by
  have indexEq : (⟨glyph.interactionIndex.val, bound⟩ : Fin graph.interactions.length) =
      glyph.interactionIndex := Fin.ext rfl
  rw [indexEq]
  exact glyph.source_mem

/-- Both memberships can be read at any proof of the same numeral bound. -/
theorem target_mem_of_nat_bound (glyph : SuppliedBondGlyph graph)
    (bound : glyph.interactionIndex.val < graph.interactions.length) :
    glyph.target ∈ (graph.interactions.get ⟨glyph.interactionIndex.val, bound⟩).1 := by
  have indexEq : (⟨glyph.interactionIndex.val, bound⟩ : Fin graph.interactions.length) =
      glyph.interactionIndex := Fin.ext rfl
  rw [indexEq]
  exact glyph.target_mem

/-! ### Relabelling -/

/-- Relabelling a supplied glyph moves both endpoints through the same equivalence and copies the
occurrence index and every source token.  The graph itself is not relabelled here; this theorem is
about the compiled retention payload only. -/
@[simp] theorem toBondGlyph_mapAtom (e : V ≃ W) (glyph : SuppliedBondGlyph graph) :
    (glyph.toBondGlyph).mapAtom e =
      { glyph.toBondGlyph with source := e glyph.source, target := e glyph.target } := by
  cases glyph with
  | mk interactionIndex source target sourceMem targetMem oriented hashConvention
      wavyGeometry purpose => rfl

/-- The two endpoints of a compiled cue both move through the same equivalence. -/
@[simp] theorem toCue_mapAtom_atomReferences (e : V ≃ W)
    (glyph : SuppliedBondGlyph graph) :
    ((glyph.toCue).mapAtom e).atomReferences = [e glyph.source, e glyph.target] := by
  rfl

/-! ### Injectivity -/

/-- Compilation to the retention layer is injective.  The two membership proofs are
proposition-valued and are identified by proof irrelevance. -/
theorem toBondGlyph_injective :
    Function.Injective (SuppliedBondGlyph.toBondGlyph (graph := graph)) := by
  intro first second equal
  cases first with
  | mk firstIndex firstSource firstTarget firstSourceMem firstTargetMem
      firstOriented firstHash firstWavy firstPurpose =>
    cases second with
    | mk secondIndex secondSource secondTarget secondSourceMem secondTargetMem
        secondOriented secondHash secondWavy secondPurpose =>
      simp only [SuppliedBondGlyph.toBondGlyph, BondGlyph.mk.injEq] at equal
      obtain ⟨indexValue, sourceValue, targetValue, orientedValue, hashValue,
        wavyValue, purposeValue⟩ := equal
      have indexEq : firstIndex = secondIndex := Fin.ext indexValue
      cases indexEq
      cases sourceValue
      cases targetValue
      cases orientedValue
      cases hashValue
      cases wavyValue
      cases purposeValue
      have sourceMemEq : firstSourceMem = secondSourceMem := Subsingleton.elim _ _
      have targetMemEq : firstTargetMem = secondTargetMem := Subsingleton.elim _ _
      cases sourceMemEq
      cases targetMemEq
      rfl

end SuppliedBondGlyph

end Supplied

/-! ## Extending the existing convention source and channel -/

namespace OrganicConventionSource

/-- Append cues to a source record's cue list.  The empty append is the identity, so an absent cue
channel (`none`) stays absent rather than becoming a present empty list.  With a nonempty append,
`none` and `some []` both become `some extra`; the pre-existing cue list (when present) is kept as
a prefix. -/
def appendCues (source : OrganicConventionSource V) :
    List (ConventionCue V) → OrganicConventionSource V
  | [] => source
  | extra => { source with cues? := some (source.cues?.getD [] ++ extra) }

@[simp] theorem appendCues_nil (source : OrganicConventionSource V) :
    source.appendCues [] = source := rfl

@[simp] theorem appendCues_convention? (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) :
    (source.appendCues extra).convention? = source.convention? := by
  cases extra <;> rfl

@[simp] theorem appendCues_scope? (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) :
    (source.appendCues extra).scope? = source.scope? := by
  cases extra <;> rfl

@[simp] theorem appendCues_referenceFrame? (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) :
    (source.appendCues extra).referenceFrame? = source.referenceFrame? := by
  cases extra <;> rfl

/-- The appended cue list, when the preceding list is present. -/
theorem appendCues_cues?_of_some (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) {old : List (ConventionCue V)}
    (nonempty : extra ≠ []) (observed : source.cues? = some old) :
    (source.appendCues extra).cues? = some (old ++ extra) := by
  cases extra with
  | nil => exact absurd rfl nonempty
  | cons head tail => simp [appendCues, observed]

/-- The appended cue list, when the preceding list is absent: the result is present and contains
exactly the appended cues. -/
theorem appendCues_cues?_of_none (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) (nonempty : extra ≠ []) (observed : source.cues? = none) :
    (source.appendCues extra).cues? = some extra := by
  cases extra with
  | nil => exact absurd rfl nonempty
  | cons head tail => simp [appendCues, observed]

/-- Exact cue-list recovery, uniformly for every append, including the identity append.  This is
the ordered-list theorem behind multiplicity and duplicate retention. -/
theorem appendCues_getD_of_some (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) {old : List (ConventionCue V)}
    (observed : source.cues? = some old) :
    (source.appendCues extra).cues?.getD [] = old ++ extra := by
  cases extra with
  | nil => simp [appendCues, observed]
  | cons head tail => simp [appendCues, observed]

/-- Exact cue-list recovery when the preceding list is absent. -/
theorem appendCues_getD_of_none (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) (observed : source.cues? = none) :
    (source.appendCues extra).cues?.getD [] = extra := by
  cases extra with
  | nil => simp [appendCues, observed]
  | cons head tail => simp [appendCues, observed]

/-- The pre-existing cues remain a prefix of the appended cue sequence, uniformly for every
append (the empty append keeps the sequence unchanged). -/
theorem appendCues_prefix (source : OrganicConventionSource V)
    (extra : List (ConventionCue V)) :
    source.cues?.getD [] <+: (source.appendCues extra).cues?.getD [] := by
  cases observed : source.cues? with
  | none =>
      rw [appendCues_getD_of_none source extra observed]
      exact ⟨extra, by simp⟩
  | some old =>
      rw [appendCues_getD_of_some source extra observed]
      exact ⟨extra, by simp⟩

end OrganicConventionSource

namespace ConventionChannel

/-- Append generated cues to the last existing source record of the channel, or create one
provenance record when the channel is empty.  An empty append is the identity. -/
def attachCuesToLast (extra : List (ConventionCue V)) (channel : ConventionChannel V) :
    ConventionChannel V :=
  match extra with
  | [] => channel
  | _ =>
      match channel.getLast? with
      | none => [{ cues? := some extra }]
      | some last => channel.dropLast ++ [last.appendCues extra]

/-- The identity on an empty append. -/
@[simp] theorem attachCuesToLast_nil (channel : ConventionChannel V) :
    attachCuesToLast ([] : List (ConventionCue V)) channel = channel := rfl

/-- The merge branch, at a supplied last record. -/
theorem attachCuesToLast_of_getLast? (extra : List (ConventionCue V))
    (channel : ConventionChannel V) {last : OrganicConventionSource V}
    (nonempty : extra ≠ []) (observed : channel.getLast? = some last) :
    attachCuesToLast extra channel = channel.dropLast ++ [last.appendCues extra] := by
  cases extra with
  | nil => exact absurd rfl nonempty
  | cons head tail => simp only [attachCuesToLast, observed]

/-- The fresh-record branch, when the channel is empty. -/
theorem attachCuesToLast_of_getLast?_none (extra : List (ConventionCue V))
    (channel : ConventionChannel V) (nonempty : extra ≠ [])
    (observed : channel.getLast? = none) :
    attachCuesToLast extra channel = [{ cues? := some extra }] := by
  cases extra with
  | nil => exact absurd rfl nonempty
  | cons head tail => simp only [attachCuesToLast, observed]

/-- The last record of the augmented channel carries exactly the old last record with the cues
appended.  This is the lookup theorem for the appended cue sequence. -/
theorem attachCuesToLast_getLast?_of_some (extra : List (ConventionCue V))
    (channel : ConventionChannel V) {last : OrganicConventionSource V}
    (nonempty : extra ≠ []) (observed : channel.getLast? = some last) :
    (attachCuesToLast extra channel).getLast? = some (last.appendCues extra) := by
  rw [attachCuesToLast_of_getLast? extra channel nonempty observed]
  rw [List.getLast?_append]
  simp

/-- The fresh branch's last record carries exactly the appended cues. -/
theorem attachCuesToLast_getLast?_of_none (extra : List (ConventionCue V))
    (channel : ConventionChannel V) (nonempty : extra ≠ [])
    (observed : channel.getLast? = none) :
    (attachCuesToLast extra channel).getLast? =
      some ({ cues? := some extra } : OrganicConventionSource V) := by
  rw [attachCuesToLast_of_getLast?_none extra channel nonempty observed]
  simp

/-- Uniform last-record characterization for a nonempty append. -/
theorem attachCuesToLast_getLast? (extra : List (ConventionCue V))
    (channel : ConventionChannel V) (nonempty : extra ≠ []) :
    (attachCuesToLast extra channel).getLast? =
      some (match channel.getLast? with
        | none => ({ cues? := some extra } : OrganicConventionSource V)
        | some last => last.appendCues extra) := by
  cases observed : channel.getLast? with
  | none =>
      rw [attachCuesToLast_getLast?_of_none extra channel nonempty observed]
  | some last =>
      rw [attachCuesToLast_getLast?_of_some extra channel (last := last) nonempty observed]

/-- Every pre-existing channel record except the last is literally unchanged. -/
theorem attachCuesToLast_dropLast_of_some (extra : List (ConventionCue V))
    (channel : ConventionChannel V) {last : OrganicConventionSource V}
    (nonempty : extra ≠ []) (observed : channel.getLast? = some last) :
    (attachCuesToLast extra channel).dropLast = channel.dropLast := by
  rw [attachCuesToLast_of_getLast? extra channel nonempty observed]
  simp

/-- When the channel is empty, the augmented channel has exactly one fresh record. -/
theorem attachCuesToLast_dropLast_of_none (extra : List (ConventionCue V))
    (channel : ConventionChannel V) (nonempty : extra ≠ [])
    (observed : channel.getLast? = none) :
    (attachCuesToLast extra channel).dropLast = [] := by
  rw [attachCuesToLast_of_getLast?_none extra channel nonempty observed]
  simp

/-- Ordered encoding lookup at the last record.  This records that the canonical common atom
enumeration is applied to every endpoint of every appended cue. -/
@[simp] theorem encode_getLast? (e : V ≃ W) (channel : ConventionChannel V) :
    (encode e channel).getLast? =
      channel.getLast?.map (OrganicConventionSource.encode e) := by
  unfold encode
  rw [List.getLast?_map]

end ConventionChannel

/-! ## Compiling supplied glyph lists -/

section Compile

variable [DecidableEq V] [Fintype V]
variable (graph : FiniteAtomInteractionHypergraph V)

/-- Compile an ordered list of supplied glyphs to retention-layer glyphs.  The list map preserves
order, length, and every duplicate position. -/
def compileSuppliedGlyphs (glyphs : List (SuppliedBondGlyph graph)) : List (BondGlyph V) :=
  glyphs.map SuppliedBondGlyph.toBondGlyph

/-- Compile an ordered list of supplied glyphs directly to ordered convention cues. -/
def compileSuppliedCues (glyphs : List (SuppliedBondGlyph graph)) : List (ConventionCue V) :=
  glyphs.map SuppliedBondGlyph.toCue

/-- The two compilations agree: mapping the compiled glyphs through `ConventionCue.bondGlyph`
gives exactly the compiled cues. -/
theorem compileSuppliedGlyphs_map_bondGlyph (glyphs : List (SuppliedBondGlyph graph)) :
    (compileSuppliedGlyphs graph glyphs).map ConventionCue.bondGlyph =
      compileSuppliedCues graph glyphs := by
  unfold compileSuppliedGlyphs compileSuppliedCues SuppliedBondGlyph.toCue
  rw [List.map_map]
  rfl

/-- Ordered length retention. -/
@[simp] theorem compileSuppliedGlyphs_length (glyphs : List (SuppliedBondGlyph graph)) :
    (compileSuppliedGlyphs graph glyphs).length = glyphs.length := by
  simp [compileSuppliedGlyphs]

/-- Ordered length retention for cues. -/
@[simp] theorem compileSuppliedCues_length (glyphs : List (SuppliedBondGlyph graph)) :
    (compileSuppliedCues graph glyphs).length = glyphs.length := by
  simp [compileSuppliedCues]

/-- Exact ordered lookup, position by position.  Duplicates therefore remain duplicates. -/
theorem compileSuppliedGlyphs_get?_bounded (glyphs : List (SuppliedBondGlyph graph))
    (index : Nat) (bound : index < glyphs.length) :
    (compileSuppliedGlyphs graph glyphs)[index]? =
      some (glyphs[index]'bound).toBondGlyph := by
  unfold compileSuppliedGlyphs
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  rfl

/-- Exact ordered cue lookup, position by position. -/
theorem compileSuppliedCues_get?_bounded (glyphs : List (SuppliedBondGlyph graph))
    (index : Nat) (bound : index < glyphs.length) :
    (compileSuppliedCues graph glyphs)[index]? = some (glyphs[index]'bound).toCue := by
  unfold compileSuppliedCues
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  rfl

/-- Two positions hold the same compiled glyph exactly when they hold the same supplied glyph.
This is the multiplicity theorem for the compiled glyph list. -/
theorem compileSuppliedGlyphs_get?_eq_iff (glyphs : List (SuppliedBondGlyph graph))
    (first second : Nat) :
    (compileSuppliedGlyphs graph glyphs)[first]? =
        (compileSuppliedGlyphs graph glyphs)[second]? ↔
      glyphs[first]? = glyphs[second]? := by
  unfold compileSuppliedGlyphs
  rw [List.getElem?_map, List.getElem?_map]
  constructor
  · intro equal
    cases firstValue : glyphs[first]? with
    | none =>
        cases secondValue : glyphs[second]? with
        | none => rfl
        | some actual =>
            rw [firstValue, secondValue] at equal
            simp at equal
    | some actual =>
        cases secondValue : glyphs[second]? with
        | none =>
            rw [firstValue, secondValue] at equal
            simp at equal
        | some other =>
            rw [firstValue, secondValue] at equal
            simp only [Option.map_some, Option.some.injEq] at equal
            rw [SuppliedBondGlyph.toBondGlyph_injective (graph := graph) equal]
  · intro equal
    rw [equal]

/-- Membership in the compiled glyph list, with the exact supplied witness. -/
theorem compileSuppliedGlyphs_mem_iff (glyphs : List (SuppliedBondGlyph graph))
    (compiled : BondGlyph V) :
    compiled ∈ compileSuppliedGlyphs graph glyphs ↔
      ∃ supplied ∈ glyphs, supplied.toBondGlyph = compiled := by
  unfold compileSuppliedGlyphs
  simp [List.mem_map]

/-- Membership in the compiled cue list, with the exact supplied witness. -/
theorem compileSuppliedCues_mem_iff (glyphs : List (SuppliedBondGlyph graph))
    (cue : ConventionCue V) :
    cue ∈ compileSuppliedCues graph glyphs ↔
      ∃ supplied ∈ glyphs, supplied.toCue = cue := by
  unfold compileSuppliedCues
  simp [List.mem_map]

/-- Empty supplied list compiles to an empty cue list. -/
@[simp] theorem compileSuppliedCues_nil :
    compileSuppliedCues graph ([] : List (SuppliedBondGlyph graph)) = [] := rfl

end Compile

/-! ## Attaching generated cues to real evidence -/

section Evidence

variable [DecidableEq V] [Fintype V]

/-- Append generated bond-glyph cues to a real molecular-evidence request.  Only the existing
convention channel changes; every other field is copied literally. -/
def attachGlyphCues (request : OrganicMolecularEvidence V) (glyphs : List (BondGlyph V)) :
    OrganicMolecularEvidence V :=
  { request with
    conventions :=
      ConventionChannel.attachCuesToLast (glyphs.map ConventionCue.bondGlyph)
        request.conventions }

/-- The augmented convention channel, exactly. -/
@[simp] theorem attachGlyphCues_conventions (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).conventions =
      ConventionChannel.attachCuesToLast (glyphs.map ConventionCue.bondGlyph)
        request.conventions := rfl

/-- No glyphs means no change at all. -/
@[simp] theorem attachGlyphCues_nil (request : OrganicMolecularEvidence V) :
    attachGlyphCues request [] = request := by
  unfold attachGlyphCues
  simp

@[simp] theorem attachGlyphCues_graph (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).graph = request.graph := rfl

@[simp] theorem attachGlyphCues_conformation (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).conformation = request.conformation := rfl

@[simp] theorem attachGlyphCues_rationalPositions? (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).rationalPositions? = request.rationalPositions? := rfl

@[simp] theorem attachGlyphCues_electronic? (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).electronic? = request.electronic? := rfl

@[simp] theorem attachGlyphCues_paths? (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).paths? = request.paths? := rfl

@[simp] theorem attachGlyphCues_bands? (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).bands? = request.bands? := rfl

@[simp] theorem attachGlyphCues_roles (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).roles = request.roles := rfl

@[simp] theorem attachGlyphCues_diagram? (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).diagram? = request.diagram? := rfl

@[simp] theorem attachGlyphCues_diagramPartial? (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).diagramPartial? = request.diagramPartial? := rfl

@[simp] theorem attachGlyphCues_diagramIncidence (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).diagramIncidence = request.diagramIncidence := rfl

@[simp] theorem attachGlyphCues_fragments (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).fragments = request.fragments := rfl

@[simp] theorem attachGlyphCues_cages (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).cages = request.cages := rfl

@[simp] theorem attachGlyphCues_residueLedger? (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).residueLedger? = request.residueLedger? := rfl

@[simp] theorem attachGlyphCues_frames (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).frames = request.frames := rfl

/-- Bundled statement: attachment changes no non-convention core channel. -/
theorem attachGlyphCues_preserves_nonconvention (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (attachGlyphCues request glyphs).graph = request.graph ∧
    (attachGlyphCues request glyphs).conformation = request.conformation ∧
    (attachGlyphCues request glyphs).rationalPositions? = request.rationalPositions? ∧
    (attachGlyphCues request glyphs).electronic? = request.electronic? ∧
    (attachGlyphCues request glyphs).paths? = request.paths? ∧
    (attachGlyphCues request glyphs).bands? = request.bands? ∧
    (attachGlyphCues request glyphs).roles = request.roles ∧
    (attachGlyphCues request glyphs).diagram? = request.diagram? ∧
    (attachGlyphCues request glyphs).diagramPartial? = request.diagramPartial? ∧
    (attachGlyphCues request glyphs).diagramIncidence = request.diagramIncidence ∧
    (attachGlyphCues request glyphs).fragments = request.fragments ∧
    (attachGlyphCues request glyphs).cages = request.cages ∧
    (attachGlyphCues request glyphs).residueLedger? = request.residueLedger? ∧
    (attachGlyphCues request glyphs).frames = request.frames := by
  simp

/-- The last pre-existing convention record is unchanged except for the appended cue sequence. -/
theorem attachGlyphCues_last_cues (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) (nonempty : glyphs ≠ [])
    {last : OrganicConventionSource V}
    (observed : request.conventions.getLast? = some last) :
    (attachGlyphCues request glyphs).conventions.getLast? =
      some (last.appendCues (glyphs.map ConventionCue.bondGlyph)) := by
  rw [attachGlyphCues_conventions]
  have mappedNonempty : glyphs.map ConventionCue.bondGlyph ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  exact ConventionChannel.attachCuesToLast_getLast?_of_some
    (glyphs.map ConventionCue.bondGlyph) request.conventions (last := last) mappedNonempty observed

/-- Every pre-existing convention record except the last is unchanged. -/
theorem attachGlyphCues_dropLast (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) (nonempty : glyphs ≠ []) :
    (attachGlyphCues request glyphs).conventions.dropLast =
      request.conventions.dropLast := by
  rw [attachGlyphCues_conventions]
  have mappedNonempty : glyphs.map ConventionCue.bondGlyph ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  cases observed : request.conventions.getLast? with
  | none =>
      rw [ConventionChannel.attachCuesToLast_of_getLast?_none
        (glyphs.map ConventionCue.bondGlyph) request.conventions mappedNonempty observed]
      have emptyChannel : request.conventions = [] :=
        List.getLast?_eq_none_iff.mp observed
      rw [emptyChannel]
      rfl
  | some last =>
      exact ConventionChannel.attachCuesToLast_dropLast_of_some
        (glyphs.map ConventionCue.bondGlyph) request.conventions (last := last)
        mappedNonempty observed

/-- A record created before the augmented last record keeps a prefix of the augmented cue
sequence (uniformly, including the empty append). -/
theorem attachGlyphCues_last_prefix (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) {last : OrganicConventionSource V}
    (_observed : request.conventions.getLast? = some last) :
    last.cues?.getD [] <+:
      (last.appendCues (glyphs.map ConventionCue.bondGlyph)).cues?.getD [] :=
  OrganicConventionSource.appendCues_prefix last (glyphs.map ConventionCue.bondGlyph)

/-! ## Source ingress into evidence -/

/-- Compile supplied source glyphs and attach their cues to a real evidence request. -/
def attachSourceGlyphs (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) : OrganicMolecularEvidence V :=
  attachGlyphCues request (compileSuppliedGlyphs request.graph glyphs)

/-- The exact augmented convention channel, in terms of the supplied cues. -/
@[simp] theorem attachSourceGlyphs_conventions (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).conventions =
      ConventionChannel.attachCuesToLast (compileSuppliedCues request.graph glyphs)
        request.conventions := by
  unfold attachSourceGlyphs
  rw [attachGlyphCues_conventions, compileSuppliedGlyphs_map_bondGlyph]

/-- No supplied glyphs means no change at all. -/
@[simp] theorem attachSourceGlyphs_nil (request : OrganicMolecularEvidence V) :
    attachSourceGlyphs request [] = request := by
  simp [attachSourceGlyphs, compileSuppliedGlyphs]

@[simp] theorem attachSourceGlyphs_graph (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).graph = request.graph := rfl

@[simp] theorem attachSourceGlyphs_conformation (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).conformation = request.conformation := rfl

@[simp] theorem attachSourceGlyphs_rationalPositions? (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).rationalPositions? = request.rationalPositions? := rfl

@[simp] theorem attachSourceGlyphs_electronic? (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).electronic? = request.electronic? := rfl

@[simp] theorem attachSourceGlyphs_paths? (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).paths? = request.paths? := rfl

@[simp] theorem attachSourceGlyphs_bands? (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).bands? = request.bands? := rfl

@[simp] theorem attachSourceGlyphs_roles (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).roles = request.roles := rfl

@[simp] theorem attachSourceGlyphs_diagram? (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).diagram? = request.diagram? := rfl

@[simp] theorem attachSourceGlyphs_diagramPartial? (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).diagramPartial? = request.diagramPartial? := rfl

@[simp] theorem attachSourceGlyphs_diagramIncidence (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).diagramIncidence = request.diagramIncidence := rfl

@[simp] theorem attachSourceGlyphs_fragments (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).fragments = request.fragments := rfl

@[simp] theorem attachSourceGlyphs_cages (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).cages = request.cages := rfl

@[simp] theorem attachSourceGlyphs_residueLedger? (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).residueLedger? = request.residueLedger? := rfl

@[simp] theorem attachSourceGlyphs_frames (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).frames = request.frames := rfl

/-- Bundled statement for the source ingress: no non-convention core channel changes. -/
theorem attachSourceGlyphs_preserves_nonconvention (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (attachSourceGlyphs request glyphs).graph = request.graph ∧
    (attachSourceGlyphs request glyphs).conformation = request.conformation ∧
    (attachSourceGlyphs request glyphs).rationalPositions? = request.rationalPositions? ∧
    (attachSourceGlyphs request glyphs).electronic? = request.electronic? ∧
    (attachSourceGlyphs request glyphs).paths? = request.paths? ∧
    (attachSourceGlyphs request glyphs).bands? = request.bands? ∧
    (attachSourceGlyphs request glyphs).roles = request.roles ∧
    (attachSourceGlyphs request glyphs).diagram? = request.diagram? ∧
    (attachSourceGlyphs request glyphs).diagramPartial? = request.diagramPartial? ∧
    (attachSourceGlyphs request glyphs).diagramIncidence = request.diagramIncidence ∧
    (attachSourceGlyphs request glyphs).fragments = request.fragments ∧
    (attachSourceGlyphs request glyphs).cages = request.cages ∧
    (attachSourceGlyphs request glyphs).residueLedger? = request.residueLedger? ∧
    (attachSourceGlyphs request glyphs).frames = request.frames := by
  simp [attachSourceGlyphs]

/-! ## The assembled graph and retained occurrences -/

/-- The actual upstream assembly preserves the request graph, for *every* pair of optional
path/band channels. -/
theorem assemble_stateGraph_eq_request_graph (request : OrganicMolecularEvidence V) :
    (assemble request).stateGraph = request.graph := by
  cases observed : request.bands? with
  | none => exact assemble_graph_of_no_bands request observed
  | some bands =>
      rw [assemble_graph_of_bands request bands observed,
        request.bands_graph_eq bands observed]

/-- The interaction list of the assembled graph is exactly the request interaction list. -/
theorem assembled_interactions_eq_request (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (assemble (attachSourceGlyphs request glyphs)).stateGraph.interactions =
      request.graph.interactions := by
  rw [assemble_stateGraph_eq_request_graph (attachSourceGlyphs request glyphs),
    attachSourceGlyphs_graph]

/-- Transport of an indexed list element across a list equality, with the numeral index written
explicitly. -/
theorem list_get_eq_of_eq {α : Type*} {first second : List α} (equal : first = second)
    (leftIndex : Fin first.length) (rightIndex : Fin second.length)
    (sameValue : (leftIndex : Nat) = (rightIndex : Nat)) :
    first.get leftIndex = second.get rightIndex := by
  rw [List.get_of_eq equal]
  have indexEq :
      (⟨(leftIndex : Nat), equal ▸ leftIndex.isLt⟩ : Fin second.length) = rightIndex :=
    Fin.ext sameValue
  rw [indexEq]

/-- **Bounded occurrence retention.**  Every inserted source glyph still names the same bounded
interaction occurrence after the actual upstream assembly, and both of its endpoints are
participants of that occurrence.  The bound is the supplied numeral; the occurrence payload is
literally the request graph's occurrence. -/
theorem assembled_glyph_occurrence (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) (position : Fin glyphs.length) :
    ∃ bound : (glyphs.get position).toBondGlyph.interactionIndex <
        (assemble (attachSourceGlyphs request glyphs)).stateGraph.interactions.length,
      (glyphs.get position).toBondGlyph.source ∈
          ((assemble (attachSourceGlyphs request glyphs)).stateGraph.interactions.get
            ⟨(glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1 ∧
        (glyphs.get position).toBondGlyph.target ∈
          ((assemble (attachSourceGlyphs request glyphs)).stateGraph.interactions.get
            ⟨(glyphs.get position).toBondGlyph.interactionIndex, bound⟩).1 := by
  let request' := attachSourceGlyphs request glyphs
  let glyph := glyphs.get position
  let compiled := glyph.toBondGlyph
  have hgraph : (assemble request').stateGraph = request.graph :=
    (assemble_stateGraph_eq_request_graph request').trans
      (attachSourceGlyphs_graph request glyphs)
  have hlist : request.graph.interactions =
      (assemble request').stateGraph.interactions :=
    congrArg (fun graph : FiniteAtomInteractionHypergraph V => graph.interactions) hgraph.symm
  have hbound : compiled.interactionIndex <
      (assemble request').stateGraph.interactions.length := by
    rw [hgraph]
    exact glyph.interactionIndex.isLt
  refine ⟨hbound, ?_, ?_⟩
  · have hget : request.graph.interactions.get glyph.interactionIndex =
        (assemble request').stateGraph.interactions.get
          ⟨compiled.interactionIndex, hbound⟩ :=
      list_get_eq_of_eq hlist glyph.interactionIndex
        ⟨compiled.interactionIndex, hbound⟩ rfl
    rw [← hget]
    simpa [compiled, glyph] using glyph.source_mem
  · have hget : request.graph.interactions.get glyph.interactionIndex =
        (assemble request').stateGraph.interactions.get
          ⟨compiled.interactionIndex, hbound⟩ :=
      list_get_eq_of_eq hlist glyph.interactionIndex
        ⟨compiled.interactionIndex, hbound⟩ rfl
    rw [← hget]
    simpa [compiled, glyph] using glyph.target_mem

/-- The bounded occurrence is the *same* occurrence as the supplied one, not merely a bounded
one: its participant list is the supplied interaction's participant list. -/
theorem assembled_glyph_occurrence_eq (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) (position : Fin glyphs.length) :
    ∃ bound : (glyphs.get position).toBondGlyph.interactionIndex <
        (assemble (attachSourceGlyphs request glyphs)).stateGraph.interactions.length,
      (assemble (attachSourceGlyphs request glyphs)).stateGraph.interactions.get
          ⟨(glyphs.get position).toBondGlyph.interactionIndex, bound⟩ =
        request.graph.interactions.get (glyphs.get position).interactionIndex := by
  let request' := attachSourceGlyphs request glyphs
  let glyph := glyphs.get position
  let compiled := glyph.toBondGlyph
  have hgraph : (assemble request').stateGraph = request.graph :=
    (assemble_stateGraph_eq_request_graph request').trans
      (attachSourceGlyphs_graph request glyphs)
  have hbound : compiled.interactionIndex <
      (assemble request').stateGraph.interactions.length := by
    rw [hgraph]
    exact glyph.interactionIndex.isLt
  refine ⟨hbound, ?_⟩
  have hlist : request.graph.interactions =
      (assemble request').stateGraph.interactions :=
    congrArg (fun graph : FiniteAtomInteractionHypergraph V => graph.interactions) hgraph.symm
  exact (list_get_eq_of_eq hlist glyph.interactionIndex
    ⟨compiled.interactionIndex, hbound⟩ rfl).symm

/-! ## Exact canonical recovery -/

/-- Encoding exposes exactly the source convention channel under the common enumeration. -/
theorem ingress_encodeDescription_conventions {E B : Type*} [Fintype E] [Fintype B]
    (atomEquiv : V ≃ Fin (Fintype.card V)) (edgeEquiv : E ≃ Fin (Fintype.card E))
    (bandEquiv : B ≃ Fin (Fintype.card B)) (description : WholeState V E B) :
    (encodeDescription atomEquiv edgeEquiv bandEquiv description).conventions =
      ConventionChannel.encode atomEquiv description.conventions := by
  unfold encodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- The canonical assembly's convention channel is the common-enumeration encoding of the actual
assembled convention channel. -/
theorem canonicalAssemble_state_conventions (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).state.conventions =
      (letI : Fintype (assemble request).edgeIndex := (assemble request).fintypeEdgeIndex
       letI : Fintype (assemble request).bandIndex := (assemble request).fintypeBandIndex
       ConventionChannel.encode enumeration (assemble request).state.conventions) := by
  rw [canonicalAssemble_state]
  letI : Fintype (assemble request).edgeIndex := (assemble request).fintypeEdgeIndex
  letI : Fintype (assemble request).bandIndex := (assemble request).fintypeBandIndex
  exact ingress_encodeDescription_conventions enumeration
    (Fintype.equivFin (assemble request).edgeIndex)
    (Fintype.equivFin (assemble request).bandIndex) (assemble request).state

/-- The canonical assembly's convention channel is the common-enumeration encoding of the request
convention channel. -/
theorem canonicalAssemble_conventions (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).state.conventions =
      ConventionChannel.encode enumeration request.conventions := by
  rw [canonicalAssemble_state_conventions]
  have annotations := (assemble_annotation_projections request).2.2.2.2.2.2.1
  simpa using congrArg (ConventionChannel.encode enumeration) annotations

/-- The canonical assembly of an augmented request carries exactly the encoded augmented
convention channel.  Every cue endpoint is therefore reindexed by the one common enumeration. -/
theorem canonicalAssemble_attachGlyphCues_conventions
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (canonicalAssemble enumeration (attachGlyphCues request glyphs)).state.conventions =
      ConventionChannel.encode enumeration
        (ConventionChannel.attachCuesToLast (glyphs.map ConventionCue.bondGlyph)
          request.conventions) := by
  rw [canonicalAssemble_conventions, attachGlyphCues_conventions]

/-- The corresponding statement for source-supplied glyphs. -/
theorem canonicalAssemble_attachSourceGlyphs_conventions
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (canonicalAssemble enumeration (attachSourceGlyphs request glyphs)).state.conventions =
      ConventionChannel.encode enumeration
        (ConventionChannel.attachCuesToLast (compileSuppliedCues request.graph glyphs)
          request.conventions) := by
  rw [canonicalAssemble_conventions, attachSourceGlyphs_conventions]

/-- At the canonical output, the last convention record is the common enumeration encoding of the
last pre-existing record with the generated cues appended.  This is the exact canonical lookup of
the appended cue sequence, including duplicates and order. -/
theorem canonicalAssemble_attachGlyphCues_last_cues
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) (nonempty : glyphs ≠ [])
    {last : OrganicConventionSource V}
    (observed : request.conventions.getLast? = some last) :
    (canonicalAssemble enumeration (attachGlyphCues request glyphs)).state.conventions.getLast? =
      some (OrganicConventionSource.encode enumeration
        (last.appendCues (glyphs.map ConventionCue.bondGlyph))) := by
  rw [canonicalAssemble_attachGlyphCues_conventions, ConventionChannel.encode_getLast?]
  have mappedNonempty : glyphs.map ConventionCue.bondGlyph ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  rw [ConventionChannel.attachCuesToLast_getLast?_of_some
    (glyphs.map ConventionCue.bondGlyph) request.conventions (last := last) mappedNonempty
    observed]
  rfl

omit [DecidableEq V] [Fintype V] in
/-- Every endpoint of a generated cue is reindexed by the same external equivalence, and the
written order is retained.  In particular this holds for the canonical common enumeration. -/
theorem encoded_glyph_endpoints (e : V ≃ W) (glyph : BondGlyph V) :
    ((ConventionCue.bondGlyph glyph).mapAtom e).atomReferences =
      [e glyph.source, e glyph.target] := by
  simp

/-- The canonical decoder of the actual canonical assembly recovers the augmented request
exactly. -/
theorem decode_canonicalAssemble_attachGlyphCues
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    decode (canonicalDecode (canonicalAssemble enumeration (attachGlyphCues request glyphs))) =
      attachGlyphCues request glyphs :=
  decode_canonicalAssemble enumeration (attachGlyphCues request glyphs)

/-- The actual `decodedCore` of the canonical assembly of the augmented request is exactly the
augmented request. -/
theorem decodedCore_attachGlyphCues (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) (glyphs : List (BondGlyph V)) :
    decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs)) =
      attachGlyphCues request glyphs := by
  simpa [decodedCore] using
    decode_canonicalAssemble enumeration (attachGlyphCues request glyphs)

/-- The decoded augmented core's convention channel is exactly the augmented channel. -/
theorem decodedCore_attachGlyphCues_conventions
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).conventions =
      ConventionChannel.attachCuesToLast (glyphs.map ConventionCue.bondGlyph)
        request.conventions := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_conventions]

@[simp] theorem decodedCore_attachGlyphCues_graph
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).graph =
      request.graph := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_graph]

@[simp] theorem decodedCore_attachGlyphCues_conformation
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).conformation =
      request.conformation := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_conformation]

@[simp] theorem decodedCore_attachGlyphCues_rationalPositions?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).rationalPositions? =
      request.rationalPositions? := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_rationalPositions?]

@[simp] theorem decodedCore_attachGlyphCues_electronic?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).electronic? =
      request.electronic? := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_electronic?]

@[simp] theorem decodedCore_attachGlyphCues_paths?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).paths? =
      request.paths? := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_paths?]

@[simp] theorem decodedCore_attachGlyphCues_bands?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).bands? =
      request.bands? := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_bands?]

@[simp] theorem decodedCore_attachGlyphCues_roles
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).roles =
      request.roles := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_roles]

@[simp] theorem decodedCore_attachGlyphCues_diagram?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).diagram? =
      request.diagram? := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_diagram?]

@[simp] theorem decodedCore_attachGlyphCues_diagramPartial?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).diagramPartial? =
      request.diagramPartial? := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_diagramPartial?]

@[simp] theorem decodedCore_attachGlyphCues_diagramIncidence
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).diagramIncidence =
      request.diagramIncidence := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_diagramIncidence]

@[simp] theorem decodedCore_attachGlyphCues_fragments
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).fragments =
      request.fragments := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_fragments]

@[simp] theorem decodedCore_attachGlyphCues_cages
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).cages =
      request.cages := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_cages]

@[simp] theorem decodedCore_attachGlyphCues_residueLedger?
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).residueLedger? =
      request.residueLedger? := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_residueLedger?]

@[simp] theorem decodedCore_attachGlyphCues_frames
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (BondGlyph V)) :
    (decodedCore (canonicalAssemble enumeration (attachGlyphCues request glyphs))).frames =
      request.frames := by
  rw [decodedCore_attachGlyphCues, attachGlyphCues_frames]

/-- Source-supplied version of exact canonical recovery. -/
theorem decode_canonicalAssemble_attachSourceGlyphs
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    decode (canonicalDecode (canonicalAssemble enumeration (attachSourceGlyphs request glyphs))) =
      attachSourceGlyphs request glyphs :=
  decode_canonicalAssemble enumeration (attachSourceGlyphs request glyphs)

/-- The actual `decodedCore` recovers the source-augmented request exactly. -/
theorem decodedCore_attachSourceGlyphs (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    decodedCore (canonicalAssemble enumeration (attachSourceGlyphs request glyphs)) =
      attachSourceGlyphs request glyphs := by
  simpa [decodedCore] using
    decode_canonicalAssemble enumeration (attachSourceGlyphs request glyphs)

/-- The decoded source-augmented core carries exactly the augmented convention channel. -/
theorem decodedCore_attachSourceGlyphs_conventions
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (decodedCore (canonicalAssemble enumeration (attachSourceGlyphs request glyphs))).conventions =
      ConventionChannel.attachCuesToLast (compileSuppliedCues request.graph glyphs)
        request.conventions := by
  rw [decodedCore_attachSourceGlyphs, attachSourceGlyphs_conventions]

/-- The decoded source-augmented core keeps the original graph exactly. -/
@[simp] theorem decodedCore_attachSourceGlyphs_graph
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (decodedCore (canonicalAssemble enumeration (attachSourceGlyphs request glyphs))).graph =
      request.graph := by
  rw [decodedCore_attachSourceGlyphs, attachSourceGlyphs_graph]

/-- The decoded source-augmented core keeps the original conformation exactly. -/
@[simp] theorem decodedCore_attachSourceGlyphs_conformation
    (enumeration : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (glyphs : List (SuppliedBondGlyph request.graph)) :
    (decodedCore (canonicalAssemble enumeration (attachSourceGlyphs request glyphs))).conformation =
      request.conformation := by
  rw [decodedCore_attachSourceGlyphs, attachSourceGlyphs_conformation]

/-! ## A concrete retention pair

Two glyphs with the same legacy projection data (occurrence index, written endpoint order, style,
narrow end) but different supplied hash conventions remain two distinct cues.  This is retention of
source metadata, not a claim about physical representation: no interpretation of either hash
convention is used or asserted. -/

/-- The shared legacy projection payload on the two-atom label type `Fin 2`. -/
def retentionLegacyGlyph : BondGlyph (Fin 2) where
  interactionIndex := 0
  source := 0
  target := 1
  oriented := { style := .hashedWedge, narrowEnd := .source }

/-- The same legacy projection with the preferred wedged hash token. -/
def retentionPreferredHash : BondGlyph (Fin 2) :=
  { retentionLegacyGlyph with hashConvention? := some .preferredWedged }

/-- The same legacy projection with the reverse-wedged hash token. -/
def retentionReverseHash : BondGlyph (Fin 2) :=
  { retentionLegacyGlyph with hashConvention? := some .reverseWedged }

/-- The legacy projection data agree exactly. -/
theorem retention_same_legacy_projection :
    retentionPreferredHash.oriented = retentionReverseHash.oriented ∧
    retentionPreferredHash.interactionIndex = retentionReverseHash.interactionIndex ∧
    retentionPreferredHash.source = retentionReverseHash.source ∧
    retentionPreferredHash.target = retentionReverseHash.target := by
  simp [retentionPreferredHash, retentionReverseHash, retentionLegacyGlyph]

/-- The supplied hash metadata differ. -/
theorem retention_different_hash_metadata :
    retentionPreferredHash.hashConvention? ≠ retentionReverseHash.hashConvention? := by
  simp [retentionPreferredHash, retentionReverseHash, retentionLegacyGlyph]

/-- The two cues are distinct even though their legacy projection data coincide. -/
theorem retention_distinct_cues :
    ConventionCue.bondGlyph retentionPreferredHash ≠
      ConventionCue.bondGlyph retentionReverseHash := by
  intro equal
  have glyphEq : retentionPreferredHash = retentionReverseHash :=
    ConventionCue.bondGlyph_injective equal
  exact retention_different_hash_metadata
    (congrArg BondGlyph.hashConvention? glyphEq)

/-- Both cues are retained, in order, in the ordered cue list. -/
theorem retention_both_listed :
    (ConventionCue.bondGlyph retentionPreferredHash) ∈
        [ConventionCue.bondGlyph retentionPreferredHash,
         ConventionCue.bondGlyph retentionReverseHash] ∧
      (ConventionCue.bondGlyph retentionReverseHash) ∈
        [ConventionCue.bondGlyph retentionPreferredHash,
         ConventionCue.bondGlyph retentionReverseHash] ∧
      (ConventionCue.bondGlyph retentionPreferredHash) ≠
        ConventionCue.bondGlyph retentionReverseHash := by
  exact ⟨by simp, by simp, retention_distinct_cues⟩

end Evidence

end TetraStereo.OneCenter
