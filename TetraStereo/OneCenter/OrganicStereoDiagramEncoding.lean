import TetraStereo.OneCenter.OrganicStereoFiniteEncoding

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Diagram-evidence encoding for finite atom-labelled organic sources

This module fills the *drawing-annotation* compatibility channel between an independently
specified finite chemical source and the existing format-neutral `AuthoritativeChemicalInput`
representation.  It does not extend chemical coverage by itself and it does not interpret any
drawing primitive.

The source is the same arbitrary finite atom type `V` used by
`FiniteAtomInteractionHypergraph`.  On top of it we define independent drawing annotations:

* `positions? : Option (V → CartesianPoint2)` — exact rational two-dimensional positions for the
  atoms that have them; `none` records the absence of that evidence channel;
* an **ordered** list of bond annotations with a source endpoint, a target endpoint, one of the
  already existing `DiagramBondStyle` constructors and one of the already existing
  `DiagramConfigurationScope` constructors (including the `relative`/`racemic` group numbers);
* an **ordered** list of atom-parity annotations with an atom label, an existing
  `TetrahedralInputParity` token and a scope.

Every atom reference — bond endpoints, atom-parity labels and position indices — is mapped through
the *same* equivalence `e : V ≃ Fin (Fintype.card V)` that the certified molecule encoding uses.
Consequently the index at which a drawing annotation names an atom is exactly the index at which
`graph.encode e` stores that atom's `SemanticAtom` data (`encodedDiagram_index_agrees_with_graph`).

The encoded `DiagramConfiguration` is attached to the authoritative source without touching the
molecule or the spatial channel: `encodeAuthoritativeWithDiagram` keeps `molecule := graph.encode e`
and `spatial?` verbatim, and only sets `diagram?`.  A new certificate proof obligation is exactly
the source-side endpoint-distinctness bound; the diagram index well-formedness conditions (bounds
on bond endpoints, positions length, atom-configuration indices) are then theorems.

Two important boundaries are made explicit in the types rather than hidden:

* The existing public `DiagramBond` has **no** source-interaction identifier.  Concrete
  interaction-occurrence indices are therefore retained in a separate, source-bound sidecar
  (`SourceBoundBondIncidence`), and bare-diagram erasure is proved **not injective** on that
  metadata (`bareEncoded_not_injective_of_distinct_incidence`, with the concrete
  `example_encodedDiagram_not_injective`).
* Incidence is a separate refinement bound to actual participants at a concrete source index.  The
  sidecar has no kind restriction: an annotation may be attached to a multicenter or otherwise
  non-binary / non-covalent interaction, and the example below does exactly that.

Encoded incidence rows are refined by `EncodedBondIncidenceEntry.Valid`: the stored bond position
must be in range for the decoded drawing, and both endpoint indices must be exactly that bond's
encoded endpoints.  `decodeIncidence?` is a checked decoder that rejects invalid raw rows, while
every bundle produced by `encodeDiagramBundle` is proved `Valid` and has its entire ordered ledger
recovered (`decodeIncidence?_encodeDiagramBundle`).

Parity tokens are preserved syntactically and only syntactically.  `OrderedReferenceFrame` records
an explicitly supplied ordered neighbour frame; its encoding uses the same `e` as the graph, and
`reordered_neighbours_change_token` shows that reordering the supplied neighbour list changes the
encoded token.  Nothing here proves physical parity invariance under an independently reordered
reference frame, and no wedge interpretation, CIP priority solver or desired `R`/`S` label is used
or produced.

No `spatial?` or `diagram?` channel is invented.  Absence is preserved exactly:
`encodeAuthoritativeWithDiagram` with `source? = none` has `diagram? = none`, positions `none`
encodes to `atomPositions? = none`, and with both optional channels absent the construction is
literally the existing `FiniteAtomInteractionHypergraph.encodeAuthoritative`.
-/

/-- Bridge between the repository's local list lookup and core `getElem?`.  Restated privately here
because the corresponding bridge in `OrganicStereoFiniteEncoding` is private to that module. -/
private theorem listGet?_eq_getElem? {α : Type*} (values : List α) (index : ℕ) :
    listGet? values index = values[index]? := by
  induction values generalizing index with
  | nil => simp [listGet?]
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => simpa [listGet?] using inductionHypothesis index

/-! ## Source-side drawing annotations over an arbitrary finite atom type -/

/-- One source-side bond annotation.  The endpoints are independent atom labels and are kept in
their written order (`source` then `target`).  Style and scope are the existing public
constructors, so every style and every scope group number already supported by
`DiagramBond` is representable. -/
structure SourceDiagramBond (V : Type*) where
  source : V
  target : V
  style : DiagramBondStyle
  scope : DiagramConfigurationScope := .absolute
  deriving DecidableEq, Repr

/-- One source-side atom-parity annotation.  The parity token is a syntactic input token; this
structure attaches no interpretation to it. -/
structure SourceDiagramAtom (V : Type*) where
  atom : V
  parity : TetrahedralInputParity
  scope : DiagramConfigurationScope := .absolute
  deriving DecidableEq, Repr

/-- Independent finite drawing-annotation data over the source atom type `V`.  The lists are
ordered and may contain repeated entries: order and multiplicity are part of the data. -/
structure OrganicDiagramSource (V : Type*) where
  /-- Exact rational positions for the atoms whose position is supplied. -/
  positions? : Option (V → CartesianPoint2) := none
  /-- Ordered, possibly repeated bond annotations. -/
  bonds : List (SourceDiagramBond V) := []
  /-- Ordered, possibly repeated atom-parity annotations. -/
  atomConfigurations : List (SourceDiagramAtom V) := []

namespace OrganicDiagramSource

variable {V : Type*} [Fintype V]

/-- Source-side bound needed for the encoded diagram to satisfy the existing index
well-formedness contract: a bond annotation may not be a self-loop.  This is an assumption about
the source drawing data, kept separate from the encoding. -/
def EndpointDistinct (source : OrganicDiagramSource V) : Prop :=
  ∀ bond, bond ∈ source.bonds → bond.source ≠ bond.target

/-! ### Encoding through the common enumeration -/

/-- Map one source bond annotation into `Fin (Fintype.card V)` indices.  Endpoint order, style and
scope (including any group number) are copied; nothing is sorted or interpreted. -/
def encodeBond (e : V ≃ Fin (Fintype.card V)) (bond : SourceDiagramBond V) : DiagramBond :=
  { source := (e bond.source).val
    target := (e bond.target).val
    style := bond.style
    scope := bond.scope }

/-- Map one source atom-parity annotation into indices.  The parity token and the scope are
copied syntactically. -/
def encodeAtomConfiguration (e : V ≃ Fin (Fintype.card V))
    (configuration : SourceDiagramAtom V) : DiagramAtomConfiguration :=
  { atom := (e configuration.atom).val
    parity := configuration.parity
    scope := configuration.scope }

/-- Encode optional positions as an optional list in enumeration order.  `none` stays `none`; a
present function is materialised as the list `i ↦ positions (e.symm i)`, which has exactly
`Fintype.card V` entries by construction. -/
def encodePositions? (e : V ≃ Fin (Fintype.card V)) :
    Option (V → CartesianPoint2) → Option (List CartesianPoint2)
  | none => none
  | some positions =>
      some (List.ofFn fun index : Fin (Fintype.card V) => positions (e.symm index))

/-- Encode the complete drawing-annotation data into the existing public
`DiagramConfiguration`. -/
def encodeDiagram (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) : DiagramConfiguration :=
  { atomPositions? := encodePositions? e source.positions?
    bonds := source.bonds.map (encodeBond e)
    atomConfigurations := source.atomConfigurations.map (encodeAtomConfiguration e) }

@[simp] theorem encodeBond_source (e : V ≃ Fin (Fintype.card V))
    (bond : SourceDiagramBond V) :
    (encodeBond e bond).source = (e bond.source).val := rfl

@[simp] theorem encodeBond_target (e : V ≃ Fin (Fintype.card V))
    (bond : SourceDiagramBond V) :
    (encodeBond e bond).target = (e bond.target).val := rfl

@[simp] theorem encodeBond_style (e : V ≃ Fin (Fintype.card V))
    (bond : SourceDiagramBond V) :
    (encodeBond e bond).style = bond.style := rfl

@[simp] theorem encodeBond_scope (e : V ≃ Fin (Fintype.card V))
    (bond : SourceDiagramBond V) :
    (encodeBond e bond).scope = bond.scope := rfl

@[simp] theorem encodeAtomConfiguration_atom (e : V ≃ Fin (Fintype.card V))
    (configuration : SourceDiagramAtom V) :
    (encodeAtomConfiguration e configuration).atom = (e configuration.atom).val := rfl

@[simp] theorem encodeAtomConfiguration_parity (e : V ≃ Fin (Fintype.card V))
    (configuration : SourceDiagramAtom V) :
    (encodeAtomConfiguration e configuration).parity = configuration.parity := rfl

@[simp] theorem encodeAtomConfiguration_scope (e : V ≃ Fin (Fintype.card V))
    (configuration : SourceDiagramAtom V) :
    (encodeAtomConfiguration e configuration).scope = configuration.scope := rfl

@[simp] theorem encodePositions?_none (e : V ≃ Fin (Fintype.card V)) :
    encodePositions? e none = none := rfl

@[simp] theorem encodePositions?_some (e : V ≃ Fin (Fintype.card V))
    (positions : V → CartesianPoint2) :
    encodePositions? e (some positions) =
      some (List.ofFn fun index : Fin (Fintype.card V) => positions (e.symm index)) := rfl

@[simp] theorem encodePositions?_isSome (e : V ≃ Fin (Fintype.card V))
    (positions? : Option (V → CartesianPoint2)) :
    (encodePositions? e positions?).isSome = positions?.isSome := by
  cases positions? with
  | none => rfl
  | some positions => rfl

/-- Presence and absence of the positions channel are preserved exactly. -/
theorem encodePositions?_eq_none_iff (e : V ≃ Fin (Fintype.card V))
    (positions? : Option (V → CartesianPoint2)) :
    encodePositions? e positions? = none ↔ positions? = none := by
  cases positions? with
  | none => simp
  | some positions => simp

@[simp] theorem encodeDiagram_atomPositions? (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    (encodeDiagram e source).atomPositions? = encodePositions? e source.positions? := rfl

@[simp] theorem encodeDiagram_bonds (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    (encodeDiagram e source).bonds = source.bonds.map (encodeBond e) := rfl

@[simp] theorem encodeDiagram_atomConfigurations (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    (encodeDiagram e source).atomConfigurations =
      source.atomConfigurations.map (encodeAtomConfiguration e) := rfl

@[simp] theorem encodeDiagram_bonds_length (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    (encodeDiagram e source).bonds.length = source.bonds.length := by
  simp

@[simp] theorem encodeDiagram_atomConfigurations_length (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    (encodeDiagram e source).atomConfigurations.length = source.atomConfigurations.length := by
  simp

/-- The positions channel is absent after encoding exactly when it was absent before. -/
theorem encodeDiagram_atomPositions?_eq_none_iff (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    (encodeDiagram e source).atomPositions? = none ↔ source.positions? = none := by
  rw [encodeDiagram_atomPositions?, encodePositions?_eq_none_iff]

/-- A present positions function is materialised at exactly its enumeration indices. -/
theorem encodeDiagram_atomPositions?_some (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (positions : V → CartesianPoint2)
    (observed : source.positions? = some positions) :
    (encodeDiagram e source).atomPositions? =
      some (List.ofFn fun index : Fin (Fintype.card V) => positions (e.symm index)) := by
  simp [encodeDiagram, encodePositions?, observed]

/-! ### Index bounds for the existing diagram well-formedness contract -/

/-- A non-self-loop source bond encodes to in-range, distinct indices. -/
theorem encodeBond_bounds (e : V ≃ Fin (Fintype.card V)) (bond : SourceDiagramBond V)
    (distinct : bond.source ≠ bond.target) :
    (fun encoded : DiagramBond =>
      decide (encoded.source < Fintype.card V) && decide (encoded.target < Fintype.card V) &&
        decide (encoded.source ≠ encoded.target)) (encodeBond e bond) = true := by
  simp only [encodeBond_source, encodeBond_target, Bool.and_eq_true_iff,
    decide_eq_true_eq]
  repeat' constructor
  · exact (e bond.source).isLt
  · exact (e bond.target).isLt
  · exact fun equal => distinct (e.injective (Fin.ext equal))

/-- Every encoded atom-parity reference is in range. -/
theorem encodeAtomConfiguration_bound (e : V ≃ Fin (Fintype.card V))
    (configuration : SourceDiagramAtom V) :
    decide ((encodeAtomConfiguration e configuration).atom < Fintype.card V) = true :=
  decide_eq_true (e configuration.atom).isLt

/-- All encoded bond annotations satisfy the existing diagram bond condition. -/
theorem encodeDiagram_bonds_bounds (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (distinct : source.EndpointDistinct) :
    (encodeDiagram e source).bonds.all (fun bond =>
      decide (bond.source < Fintype.card V) && decide (bond.target < Fintype.card V) &&
        decide (bond.source ≠ bond.target)) = true := by
  rw [encodeDiagram_bonds, List.all_map]
  exact List.all_eq_true.mpr fun bond membership =>
    encodeBond_bounds e bond (distinct bond membership)

/-- All encoded atom-parity annotations satisfy the existing diagram atom condition. -/
theorem encodeDiagram_atomConfigurations_bounds (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    (encodeDiagram e source).atomConfigurations.all
      (fun atomConfiguration =>
        decide (atomConfiguration.atom < Fintype.card V)) = true := by
  rw [encodeDiagram_atomConfigurations, List.all_map]
  exact List.all_eq_true.mpr fun configuration _ =>
    encodeAtomConfiguration_bound e configuration

/-- If positions are present, the encoded list has exactly the source atom count. -/
theorem encodeDiagram_positions_fit (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    (match (encodeDiagram e source).atomPositions? with
     | none => True
     | some positions => positions.length = Fintype.card V) := by
  cases observed : source.positions? with
  | none => simp [encodeDiagram, encodePositions?, observed]
  | some positions => simp [encodeDiagram, encodePositions?, observed]

/-! ### The same enumeration as the graph -/

/-- The index at which the encoded diagram names an atom is exactly the index at which the
certified molecule encoding stores that atom's semantic data.  All drawing atom references
therefore pass through the same `e` as the graph. -/
theorem encodedDiagram_index_agrees_with_graph [DecidableEq V]
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (atom : V) :
    listGet? (graph.encode e).atoms (e atom).val = some (graph.atomData atom) := by
  simpa using graph.encode_atomAt e (e atom)

/-- Bond source references agree with the graph encoding. -/
theorem encodeBond_source_agrees_with_graph [DecidableEq V]
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (bond : SourceDiagramBond V) :
    listGet? (graph.encode e).atoms (encodeBond e bond).source =
      some (graph.atomData bond.source) :=
  encodedDiagram_index_agrees_with_graph graph e bond.source

/-- Bond target references agree with the graph encoding. -/
theorem encodeBond_target_agrees_with_graph [DecidableEq V]
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (bond : SourceDiagramBond V) :
    listGet? (graph.encode e).atoms (encodeBond e bond).target =
      some (graph.atomData bond.target) :=
  encodedDiagram_index_agrees_with_graph graph e bond.target

/-- Atom-parity references agree with the graph encoding. -/
theorem encodeAtomConfiguration_agrees_with_graph [DecidableEq V]
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (configuration : SourceDiagramAtom V) :
    listGet? (graph.encode e).atoms (encodeAtomConfiguration e configuration).atom =
      some (graph.atomData configuration.atom) :=
  encodedDiagram_index_agrees_with_graph graph e configuration.atom

/-! ### Decoding and round trips -/

/-- Decode one index back to an independent atom label.  Out-of-range indices have no label. -/
def decodeBond? (e : V ≃ Fin (Fintype.card V)) (bond : DiagramBond) :
    Option (SourceDiagramBond V) := do
  let source ← FiniteAtomInteractionHypergraph.decodeIndex? e bond.source
  let target ← FiniteAtomInteractionHypergraph.decodeIndex? e bond.target
  some { source := source, target := target, style := bond.style, scope := bond.scope }

/-- Decoding an encoded bond recovers the source bond exactly, endpoints and all annotation
fields included. -/
@[simp] theorem decodeBond?_encodeBond (e : V ≃ Fin (Fintype.card V))
    (bond : SourceDiagramBond V) :
    decodeBond? e (encodeBond e bond) = some bond := by
  simp [decodeBond?, encodeBond, FiniteAtomInteractionHypergraph.decodeIndex?_encode]

/-- Decode one atom-parity annotation. -/
def decodeAtomConfiguration? (e : V ≃ Fin (Fintype.card V))
    (configuration : DiagramAtomConfiguration) : Option (SourceDiagramAtom V) := do
  let atom ← FiniteAtomInteractionHypergraph.decodeIndex? e configuration.atom
  some { atom := atom, parity := configuration.parity, scope := configuration.scope }

/-- Decoding an encoded atom-parity annotation recovers the source annotation exactly; the parity
token is recovered as the same syntactic token. -/
@[simp] theorem decodeAtomConfiguration?_encodeAtomConfiguration
    (e : V ≃ Fin (Fintype.card V)) (configuration : SourceDiagramAtom V) :
    decodeAtomConfiguration? e (encodeAtomConfiguration e configuration) = some configuration := by
  simp [decodeAtomConfiguration?, encodeAtomConfiguration,
    FiniteAtomInteractionHypergraph.decodeIndex?_encode]

/-- Decode an optional positions channel.  `none` is decoded to `some none`; a present list is
accepted only at exactly the source cardinality, otherwise decoding fails rather than
reinterpreting a malformed list. -/
def decodePositions? (e : V ≃ Fin (Fintype.card V)) (diagram : DiagramConfiguration) :
    Option (Option (V → CartesianPoint2)) :=
  match diagram.atomPositions? with
  | none => some none
  | some positions =>
      if h : positions.length = Fintype.card V then
        some (some fun atom =>
          positions.get ⟨(e atom).val, by rw [h]; exact (e atom).isLt⟩)
      else none

/-- Decoding a list of encoded positions recovers the source position at every atom. -/
private theorem ofFn_positions_get (e : V ≃ Fin (Fintype.card V))
    (positions : V → CartesianPoint2) (atom : V) :
    (List.ofFn fun index : Fin (Fintype.card V) => positions (e.symm index)).get
        ⟨(e atom).val, by
          rw [List.length_ofFn]
          exact (e atom).isLt⟩ = positions atom := by
  rw [List.get_ofFn]
  simp

/-- General decode step for the positions channel. -/
theorem decodePositions?_encode (e : V ≃ Fin (Fintype.card V))
    (positions? : Option (V → CartesianPoint2)) (diagram : DiagramConfiguration)
    (observed : diagram.atomPositions? = encodePositions? e positions?) :
    decodePositions? e diagram = some positions? := by
  unfold decodePositions?
  rw [observed]
  cases positions? with
  | none => rfl
  | some positions =>
      simp only [encodePositions?, List.length_ofFn]
      refine congrArg some ?_
      refine congrArg some ?_
      funext atom
      exact ofFn_positions_get e positions atom

/-- Decoding an encoded diagram recovers its positions channel exactly. -/
theorem decodePositions?_encodeDiagram (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    decodePositions? e (encodeDiagram e source) = some source.positions? :=
  decodePositions?_encode e source.positions? (encodeDiagram e source) rfl

/-- Whole-list bond round trip: the encoded ordered bond list decodes to the source list exactly,
so order and multiplicity are retained. -/
theorem mapM_decodeBond?_encodeBonds (e : V ≃ Fin (Fintype.card V))
    (bonds : List (SourceDiagramBond V)) :
    (bonds.map (encodeBond e)).mapM (decodeBond? e) = some bonds := by
  induction bonds with
  | nil => rfl
  | cons bond bonds inductionHypothesis =>
      simp [decodeBond?_encodeBond e bond, inductionHypothesis]

/-- Whole-list atom-parity round trip. -/
theorem mapM_decodeAtomConfiguration?_encodeAtomConfigurations
    (e : V ≃ Fin (Fintype.card V)) (configurations : List (SourceDiagramAtom V)) :
    (configurations.map (encodeAtomConfiguration e)).mapM (decodeAtomConfiguration? e) =
      some configurations := by
  induction configurations with
  | nil => rfl
  | cons configuration configurations inductionHypothesis =>
      simp [decodeAtomConfiguration?_encodeAtomConfiguration e configuration,
        inductionHypothesis]

/-- Decode a complete `DiagramConfiguration` back to independent source drawing data. -/
def decodeDiagram? (e : V ≃ Fin (Fintype.card V))
    (diagram : DiagramConfiguration) : Option (OrganicDiagramSource V) :=
  Option.bind (decodePositions? e diagram) fun positions? =>
    Option.bind (diagram.bonds.mapM (decodeBond? e)) fun bonds =>
      Option.bind (diagram.atomConfigurations.mapM (decodeAtomConfiguration? e))
        fun atomConfigurations =>
          some { positions? := positions?
                 bonds := bonds
                 atomConfigurations := atomConfigurations }

/-- Decode-after-encode: the encoded diagram determines its source drawing data exactly. -/
theorem decodeDiagram?_encodeDiagram (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) :
    decodeDiagram? e (encodeDiagram e source) = some source := by
  unfold decodeDiagram?
  rw [decodePositions?_encode e source.positions? (encodeDiagram e source) rfl]
  simp only [Option.bind_some]
  dsimp only [encodeDiagram]
  rw [mapM_decodeBond?_encodeBonds e source.bonds]
  simp only [Option.bind_some]
  rw [mapM_decodeAtomConfiguration?_encodeAtomConfigurations e source.atomConfigurations]
  rfl

/-- The diagram encoding is injective: distinct source drawing data cannot encode to the same
public `DiagramConfiguration`. -/
theorem encodeDiagram_injective (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective (encodeDiagram e) := by
  intro first second equal
  have decoded := congrArg (decodeDiagram? e) equal
  simpa [decodeDiagram?_encodeDiagram e first, decodeDiagram?_encodeDiagram e second] using decoded

/-- The bond map is injective, so list multiplicity is retained by the encoding. -/
theorem encodeBond_injective (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective (encodeBond e) := by
  intro first second equal
  have decoded := congrArg (decodeBond? e) equal
  simpa [decodeBond?_encodeBond e first, decodeBond?_encodeBond e second] using decoded

/-- Bond-list encoding is injective: repeated and differently ordered source bonds remain
distinct after encoding. -/
theorem encodeBonds_injective (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective fun bonds : List (SourceDiagramBond V) => bonds.map (encodeBond e) := by
  intro first second equal
  exact (List.map_inj_right fun _ _ same => encodeBond_injective e same).mp equal

/-- Ordered lookup of an encoded bond: position, endpoints, style and scope at a source position
are exactly the encoding of the source bond at that same position. -/
theorem encodeDiagram_bondAt (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (index : ℕ) (bound : index < source.bonds.length) :
    listGet? (encodeDiagram e source).bonds index =
      some (encodeBond e (source.bonds.get ⟨index, bound⟩)) := by
  rw [encodeDiagram_bonds]
  have mappedBound : index < (source.bonds.map (encodeBond e)).length := by
    rw [List.length_map]
    exact bound
  rw [listGet?_eq_getElem?, List.getElem?_eq_getElem mappedBound, List.getElem_map]
  rfl

/-- Ordered lookup of an encoded atom-parity annotation. -/
theorem encodeDiagram_atomConfigurationAt (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (index : ℕ)
    (bound : index < source.atomConfigurations.length) :
    listGet? (encodeDiagram e source).atomConfigurations index =
      some (encodeAtomConfiguration e (source.atomConfigurations.get ⟨index, bound⟩)) := by
  rw [encodeDiagram_atomConfigurations]
  have mappedBound : index <
      (source.atomConfigurations.map (encodeAtomConfiguration e)).length := by
    rw [List.length_map]
    exact bound
  rw [listGet?_eq_getElem?, List.getElem?_eq_getElem mappedBound, List.getElem_map]
  rfl

/-! ### Enumeration transport -/

/-- The index permutation induced by changing the enumeration from `first` to `second`.  Every
drawing atom reference is transported by this one permutation; there is no per-channel choice. -/
def enumerationChange (first second : V ≃ Fin (Fintype.card V)) :
    Fin (Fintype.card V) ≃ Fin (Fintype.card V) :=
  first.symm.trans second

@[simp] theorem enumerationChange_apply_first
    (first second : V ≃ Fin (Fintype.card V)) (atom : V) :
    enumerationChange first second (first atom) = second atom := by
  simp [enumerationChange]

/-- Under a change of enumeration, an encoded bond has its endpoints transported by the common
index permutation; style and scope are untouched. -/
theorem encodeBond_relabel (bond : SourceDiagramBond V)
    (first second : V ≃ Fin (Fintype.card V)) :
    (encodeBond second bond).source =
        (enumerationChange first second
          ⟨(encodeBond first bond).source, (first bond.source).isLt⟩).val ∧
      (encodeBond second bond).target =
        (enumerationChange first second
          ⟨(encodeBond first bond).target, (first bond.target).isLt⟩).val ∧
      (encodeBond second bond).style = (encodeBond first bond).style ∧
      (encodeBond second bond).scope = (encodeBond first bond).scope := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;>
    simp [encodeBond, enumerationChange]

/-- Under a change of enumeration, an encoded atom-parity annotation has its atom reference
transported by the common index permutation; parity token and scope are untouched. -/
theorem encodeAtomConfiguration_relabel (configuration : SourceDiagramAtom V)
    (first second : V ≃ Fin (Fintype.card V)) :
    (encodeAtomConfiguration second configuration).atom =
        (enumerationChange first second
          ⟨(encodeAtomConfiguration first configuration).atom,
            (first configuration.atom).isLt⟩).val ∧
      (encodeAtomConfiguration second configuration).parity =
        (encodeAtomConfiguration first configuration).parity ∧
      (encodeAtomConfiguration second configuration).scope =
        (encodeAtomConfiguration first configuration).scope := by
  refine ⟨?_, rfl, rfl⟩
  simp [encodeAtomConfiguration, enumerationChange]

/-- The encoded position of a source atom is present at exactly the enumeration index of that
atom. -/
theorem encodeDiagram_positions_at (source : OrganicDiagramSource V)
    (e : V ≃ Fin (Fintype.card V)) (positions : V → CartesianPoint2)
    (observed : source.positions? = some positions) (atom : V) :
    listGet? ((encodeDiagram e source).atomPositions?.getD []) (e atom).val =
      some (positions atom) := by
  rw [encodeDiagram_atomPositions?, observed, encodePositions?_some]
  simp only [Option.getD_some]
  rw [listGet?_eq_some_get (index := ⟨(e atom).val, by
    rw [List.length_ofFn]
    exact (e atom).isLt⟩)]
  exact congrArg some (ofFn_positions_get e positions atom)

/-- Position transport: the same atom has its encoded position at the index prescribed by either
enumeration. -/
theorem encodeDiagram_positions_relabel (source : OrganicDiagramSource V)
    (first second : V ≃ Fin (Fintype.card V)) (atom : V) :
    listGet? ((encodeDiagram second source).atomPositions?.getD []) (second atom).val =
      listGet? ((encodeDiagram first source).atomPositions?.getD []) (first atom).val := by
  cases observed : source.positions? with
  | none =>
      simp only [encodeDiagram, encodePositions?, observed, Option.getD_none]
      rfl
  | some positions =>
      rw [encodeDiagram_positions_at source second positions observed atom,
        encodeDiagram_positions_at source first positions observed atom]

end OrganicDiagramSource

/-! ## Partial position sidecar

The legacy `positions? : Option (V → CartesianPoint2)` channel is all-or-nothing.  Independent
sources often know only some coordinates.  `SourcePartialPositions` records, atom by atom, either
an exact rational position or the absence of one; absence is `none` and is therefore distinct
from every supplied coordinate, including the origin.  This sidecar is *supplementary*: it does
not alter the legacy channel and it is not representable in `DiagramConfiguration`. -/

/-- Partial drawing-position evidence over independent atom labels. -/
structure SourcePartialPositions (V : Type*) where
  positions : V → Option CartesianPoint2

namespace SourcePartialPositions

variable {V : Type*} [Fintype V]

/-- Encode the partial sidecar in enumeration order.  Every atom reference is mapped through the
same `e` used for the graph and the diagram. -/
def encode (e : V ≃ Fin (Fintype.card V)) (partialEvidence : SourcePartialPositions V) :
    Fin (Fintype.card V) → Option CartesianPoint2 :=
  fun index => partialEvidence.positions (e.symm index)

@[simp] theorem encode_apply (e : V ≃ Fin (Fintype.card V))
    (partialEvidence : SourcePartialPositions V) (atom : V) :
    partialEvidence.encode e (e atom) = partialEvidence.positions atom := by
  simp [encode]

/-- Decode a partial sidecar back to independent atom labels. -/
def decode (e : V ≃ Fin (Fintype.card V))
    (positions : Fin (Fintype.card V) → Option CartesianPoint2) : SourcePartialPositions V :=
  { positions := fun atom => positions (e atom) }

/-- Decode-after-encode recovers the partial sidecar exactly, including every absence. -/
@[simp] theorem decode_encode (e : V ≃ Fin (Fintype.card V))
    (partialEvidence : SourcePartialPositions V) :
    decode e (encode e partialEvidence) = partialEvidence := by
  cases partialEvidence with
  | mk positions =>
      simp [decode, encode]

/-- The partial encoding is injective: two sidecars with the same encoded partial coordinates are
the same sidecar. -/
theorem encode_injective (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective (encode e) := by
  intro first second equal
  cases first with
  | mk firstPositions =>
      cases second with
      | mk secondPositions =>
          have pointwise : firstPositions = secondPositions := by
            funext atom
            have applied := congrArg (fun values => values (e atom)) equal
            simpa [encode] using applied
          rw [pointwise]

omit [Fintype V] in
/-- Absence of a partial position is distinct from any supplied coordinate: in particular, an
unknown coordinate cannot be confused with the origin. -/
theorem absent_ne_origin (partialEvidence : SourcePartialPositions V) (atom : V) :
    partialEvidence.positions atom = none → partialEvidence.positions atom ≠ some ⟨0, 0⟩ := by
  intro absent supplied
  rw [absent] at supplied
  cases supplied

end SourcePartialPositions

/-! ## Attaching the encoded diagram to an authoritative source -/

namespace AuthoritativeChemicalInput

/-- Replace only the optional diagram channel.  The molecule and the spatial channel are
untouched, including their absence. -/
def withDiagram? (input : AuthoritativeChemicalInput)
    (diagram? : Option DiagramConfiguration) : AuthoritativeChemicalInput :=
  { input with diagram? := diagram? }

@[simp] theorem withDiagram?_molecule (input : AuthoritativeChemicalInput)
    (diagram? : Option DiagramConfiguration) :
    (input.withDiagram? diagram?).molecule = input.molecule := rfl

@[simp] theorem withDiagram?_spatial? (input : AuthoritativeChemicalInput)
    (diagram? : Option DiagramConfiguration) :
    (input.withDiagram? diagram?).spatial? = input.spatial? := rfl

@[simp] theorem withDiagram?_diagram? (input : AuthoritativeChemicalInput)
    (diagram? : Option DiagramConfiguration) :
    (input.withDiagram? diagram?).diagram? = diagram? := rfl

end AuthoritativeChemicalInput

/-- The spatial-channel fitting predicate used as a certificate proof bound.  It is exactly the
existing `SpatialIndicesWellFormed` obligation, repackaged at the source cardinality so that it can
be supplied before the encoded input is built. -/
def SpatialEvidenceFits (spatial? : Option SpatialConfiguration) (atomCount : ℕ) : Prop :=
  match spatial? with
  | none => True
  | some spatial => spatial.positions.length = atomCount

section AuthoritativeAttachment

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The authoritative source with the molecule encoded by the graph and the spatial channel
passed through verbatim; the diagram channel is still absent. -/
def encodeAuthoritativeWithSpatial (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (spatial? : Option SpatialConfiguration := none) : AuthoritativeChemicalInput :=
  { molecule := graph.encode e
    spatial? := spatial? }

/-- Attach encoded drawing evidence to the authoritative source.  The molecule is exactly
`graph.encode e`, the spatial channel is preserved verbatim, and only `diagram?` is populated (or
left absent when no source drawing data is supplied). -/
def encodeAuthoritativeWithDiagram (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V))
    (spatial? : Option SpatialConfiguration := none) : AuthoritativeChemicalInput :=
  { molecule := graph.encode e
    spatial? := spatial?
    diagram? := source?.map (OrganicDiagramSource.encodeDiagram e) }

@[simp] theorem encodeAuthoritativeWithDiagram_molecule
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration) :
    (encodeAuthoritativeWithDiagram graph e source? spatial?).molecule = graph.encode e := rfl

@[simp] theorem encodeAuthoritativeWithDiagram_spatial?
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration) :
    (encodeAuthoritativeWithDiagram graph e source? spatial?).spatial? = spatial? := rfl

@[simp] theorem encodeAuthoritativeWithDiagram_diagram?
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration) :
    (encodeAuthoritativeWithDiagram graph e source? spatial?).diagram? =
      source?.map (OrganicDiagramSource.encodeDiagram e) := rfl

@[simp] theorem encodeAuthoritativeWithDiagram_diagram?_none
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (spatial? : Option SpatialConfiguration) :
    (encodeAuthoritativeWithDiagram graph e none spatial?).diagram? = none := rfl

@[simp] theorem encodeAuthoritativeWithDiagram_diagram?_some
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (spatial? : Option SpatialConfiguration) :
    (encodeAuthoritativeWithDiagram graph e (some source) spatial?).diagram? =
      some (OrganicDiagramSource.encodeDiagram e source) := rfl

/-- The diagram channel is present exactly when source drawing data was supplied. -/
theorem encodeAuthoritativeWithDiagram_diagram?_isSome
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration) :
    (encodeAuthoritativeWithDiagram graph e source? spatial?).diagram?.isSome =
      source?.isSome := by
  cases source? with
  | none => rfl
  | some source => rfl

/-- The construction is literally "attach the encoded diagram to the authoritative source":
only the diagram channel is updated. -/
theorem encodeAuthoritativeWithDiagram_eq_attach
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration) :
    encodeAuthoritativeWithDiagram graph e source? spatial? =
      (encodeAuthoritativeWithSpatial graph e spatial?).withDiagram?
        (source?.map (OrganicDiagramSource.encodeDiagram e)) := rfl

/-- The molecule is exactly the one produced by the existing certified encoding. -/
theorem encodeAuthoritativeWithDiagram_molecule_eq_encodeAuthoritative
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration) :
    (encodeAuthoritativeWithDiagram graph e source? spatial?).molecule =
      (graph.encodeAuthoritative e).molecule := rfl

/-- With both optional evidence channels absent the construction is *literally* the existing
encoding, so no spatial or diagram evidence is invented. -/
@[simp] theorem encodeAuthoritativeWithDiagram_none_none
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V)) :
    encodeAuthoritativeWithDiagram graph e (none : Option (OrganicDiagramSource V)) none =
      graph.encodeAuthoritative e := rfl

/-- Spatial-index well-formedness of the attached source is exactly the supplied fitting
bound. -/
theorem encodeAuthoritativeWithDiagram_spatialIndices_iff
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration) :
    (encodeAuthoritativeWithDiagram graph e source? spatial?).SpatialIndicesWellFormed ↔
      SpatialEvidenceFits spatial? (Fintype.card V) := by
  cases spatial? with
  | none =>
      simp [AuthoritativeChemicalInput.SpatialIndicesWellFormed, SpatialEvidenceFits,
        encodeAuthoritativeWithDiagram]
  | some spatial =>
      simp [AuthoritativeChemicalInput.SpatialIndicesWellFormed, SpatialEvidenceFits,
        encodeAuthoritativeWithDiagram, graph.encode_atomCount e]

/-- The full structural certificate for the attached source.  The only new source-level
obligations, beyond the molecule certificate that already holds for every finite graph, are the
spatial fitting bound and the endpoint-distinctness bound on present drawing data. -/
theorem encodeAuthoritativeWithDiagram_structurallyWellFormed
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration)
    (spatialFits : SpatialEvidenceFits spatial? (Fintype.card V))
    (endpointDistinct : ∀ source, source? = some source → source.EndpointDistinct) :
    (encodeAuthoritativeWithDiagram graph e source? spatial?).StructurallyWellFormed := by
  refine ⟨graph.encode_structurallyWellFormed e, ?_, ?_⟩
  · simpa [AuthoritativeChemicalInput.SpatialIndicesWellFormed, SpatialEvidenceFits,
      encodeAuthoritativeWithDiagram, graph.encode_atomCount e] using spatialFits
  · cases sourceObserved : source? with
    | none =>
        simp [encodeAuthoritativeWithDiagram,
          AuthoritativeChemicalInput.DiagramIndicesWellFormed]
    | some source =>
        have distinct := endpointDistinct source sourceObserved
        show (match (OrganicDiagramSource.encodeDiagram e source).atomPositions? with
            | none => True
            | some positions => positions.length = (graph.encode e).atomCount) ∧
          (OrganicDiagramSource.encodeDiagram e source).bonds.all (fun bond =>
            decide (bond.source < (graph.encode e).atomCount) &&
              decide (bond.target < (graph.encode e).atomCount) &&
                decide (bond.source ≠ bond.target)) = true ∧
          (OrganicDiagramSource.encodeDiagram e source).atomConfigurations.all
            (fun atomConfiguration =>
              decide (atomConfiguration.atom < (graph.encode e).atomCount)) = true
        rw [graph.encode_atomCount e]
        exact ⟨OrganicDiagramSource.encodeDiagram_positions_fit e source,
          OrganicDiagramSource.encodeDiagram_bonds_bounds e source distinct,
          OrganicDiagramSource.encodeDiagram_atomConfigurations_bounds e source⟩

/-- The attached source satisfies the executable structural certificate. -/
theorem encodeAuthoritativeWithDiagram_structurallyWellFormed?
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration)
    (spatialFits : SpatialEvidenceFits spatial? (Fintype.card V))
    (endpointDistinct : ∀ source, source? = some source → source.EndpointDistinct) :
    (encodeAuthoritativeWithDiagram graph e source? spatial?).structurallyWellFormed? = true :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff _).mpr
    (encodeAuthoritativeWithDiagram_structurallyWellFormed graph e source? spatial?
      spatialFits endpointDistinct)

/-- Certified authoritative input carrying the encoded drawing evidence. -/
def certifiedWithOptionalDiagram (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration)
    (spatialFits : SpatialEvidenceFits spatial? (Fintype.card V))
    (endpointDistinct : ∀ source, source? = some source → source.EndpointDistinct) :
    CertifiedAuthoritativeChemicalInput :=
  { input := encodeAuthoritativeWithDiagram graph e source? spatial?
    structurallyWellFormed :=
      encodeAuthoritativeWithDiagram_structurallyWellFormed graph e source? spatial?
        spatialFits endpointDistinct }

@[simp] theorem certifiedWithOptionalDiagram_input
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source? : Option (OrganicDiagramSource V)) (spatial? : Option SpatialConfiguration)
    (spatialFits : SpatialEvidenceFits spatial? (Fintype.card V))
    (endpointDistinct : ∀ source, source? = some source → source.EndpointDistinct) :
    (certifiedWithOptionalDiagram graph e source? spatial? spatialFits endpointDistinct).input =
      encodeAuthoritativeWithDiagram graph e source? spatial? := rfl

/-- Certified attachment of drawing evidence to a source with no spatial channel.  This is the
common case: the spatial channel stays absent exactly as in `certifiedEncoding`. -/
def certifiedDiagramEncoding (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (source : OrganicDiagramSource V)
    (endpointDistinct : source.EndpointDistinct) : CertifiedAuthoritativeChemicalInput :=
  certifiedWithOptionalDiagram graph e (some source) none trivial
    (by
      intro other observed
      exact (Option.some.inj observed) ▸ endpointDistinct)

@[simp] theorem certifiedDiagramEncoding_input
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (endpointDistinct : source.EndpointDistinct) :
    (certifiedDiagramEncoding graph e source endpointDistinct).input =
      encodeAuthoritativeWithDiagram graph e (some source) none := rfl

/-- The certified attachment keeps the spatial channel absent. -/
@[simp] theorem certifiedDiagramEncoding_spatial?
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (endpointDistinct : source.EndpointDistinct) :
    (certifiedDiagramEncoding graph e source endpointDistinct).input.spatial? = none := rfl

/-- The certified attachment carries exactly the encoded diagram. -/
@[simp] theorem certifiedDiagramEncoding_diagram?
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (endpointDistinct : source.EndpointDistinct) :
    (certifiedDiagramEncoding graph e source endpointDistinct).input.diagram? =
      some (OrganicDiagramSource.encodeDiagram e source) := rfl

end AuthoritativeAttachment

/-! ## Source-bound incidence sidecar

The existing public `DiagramBond`/`DiagramConfiguration` has no field naming a source
interaction, and one drawing bond annotation may correspond to several source interaction
occurrences (or to none during construction).  Incidence is therefore kept in an explicit,
*sparse* and *multi-valued* ledger.  Each row attaches a concrete drawing-bond occurrence index
(a position in the ordered bond list) to a concrete source interaction occurrence and carries
membership evidence for both annotated endpoints in that interaction's participant list.  There
is deliberately no hypothesis restricting the interaction to a binary covalent bond. -/

section SourceBoundSidecar

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- One sparse incidence row.  Several rows may name the same bond occurrence, and a bond
occurrence may have no row at all. -/
structure BondIncidenceEntry (graph : FiniteAtomInteractionHypergraph V)
    (source : OrganicDiagramSource V) where
  /-- Position of the drawing-bond occurrence in the ordered source bond list. -/
  bondIndex : Fin source.bonds.length
  /-- Concrete source interaction occurrence. -/
  interactionIndex : Fin graph.interactions.length
  /-- The annotated source endpoint is a participant of the named source interaction. -/
  source_mem : (source.bonds.get bondIndex).source ∈
    (graph.interactions.get interactionIndex).1
  /-- The annotated target endpoint is a participant of the named source interaction. -/
  target_mem : (source.bonds.get bondIndex).target ∈
    (graph.interactions.get interactionIndex).1

/-- A sparse, multi-valued incidence ledger. -/
structure SourceBoundBondIncidence (graph : FiniteAtomInteractionHypergraph V)
    (source : OrganicDiagramSource V) where
  entries : List (BondIncidenceEntry graph source) := []

/-- The encoded interaction index corresponding to a source interaction index.  Encoding preserves
the interaction list length, so every source occurrence names exactly one encoded occurrence. -/
def encodedInteractionIndex (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length) :
    Fin (graph.encode e).interactions.length :=
  Fin.cast (graph.encode_interactions_length e).symm index

/-- Exact lookup at an encoded interaction index. -/
theorem encodedInteraction_get (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length) :
    (graph.encode e).interactions.get (encodedInteractionIndex graph e index) =
      FiniteAtomInteractionHypergraph.encodeInteraction e (graph.interactions.get index) := by
  show (List.map (FiniteAtomInteractionHypergraph.encodeInteraction e) graph.interactions).get
      (encodedInteractionIndex graph e index) =
    FiniteAtomInteractionHypergraph.encodeInteraction e (graph.interactions.get index)
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  rfl

/-- Encoded participants are exactly the enumeration of the source participants. -/
theorem encodedInteraction_participants_get (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length) :
    ((graph.encode e).interactions.get (encodedInteractionIndex graph e index)).participants =
      (graph.interactions.get index).1.map fun atom => (e atom).val := by
  rw [encodedInteraction_get]
  rfl

/-- A source participant is an encoded participant at the corresponding encoded occurrence. -/
theorem encoded_mem_of_source_mem (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length)
    {atom : V} (member : atom ∈ (graph.interactions.get index).1) :
    (e atom).val ∈ ((graph.encode e).interactions.get
      (encodedInteractionIndex graph e index)).participants := by
  rw [encodedInteraction_participants_get]
  exact List.mem_map.mpr ⟨atom, member, rfl⟩

/-! ### Inverting the interaction-index transport

The encoder maps a source interaction occurrence into the encoded occurrence with the same
position.  A decoder needs the inverse transport, and it must use the actual length equality of
`graph.encode e`, not an arbitrary index.  The lemmas below state that inverse and show that
participant membership transports back through it. -/

/-- The inverse of `encodedInteractionIndex`, using the actual length equality of the graph
encoding. -/
def decodedInteractionIndex (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.encode e).interactions.length) : Fin graph.interactions.length :=
  Fin.cast (graph.encode_interactions_length e) index

/-- The interaction-index transports are mutually inverse. -/
@[simp] theorem decodedInteractionIndex_encodedInteractionIndex
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (index : Fin graph.interactions.length) :
    decodedInteractionIndex graph e (encodedInteractionIndex graph e index) = index := by
  apply Fin.ext
  rfl

/-- The interaction-index transports are mutually inverse in the other direction. -/
@[simp] theorem encodedInteractionIndex_decodedInteractionIndex
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.encode e).interactions.length) :
    encodedInteractionIndex graph e (decodedInteractionIndex graph e index) = index := by
  apply Fin.ext
  rfl

/-- Exact lookup at an arbitrary encoded occurrence, expressed through the inverse transport.
Unlike `encodedInteraction_get`, this lemma does not presuppose that the encoded index was
produced by `encodedInteractionIndex`. -/
theorem encodedInteraction_get_decoded (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.encode e).interactions.length) :
    (graph.encode e).interactions.get index =
      FiniteAtomInteractionHypergraph.encodeInteraction e
        (graph.interactions.get (decodedInteractionIndex graph e index)) := by
  show (List.map (FiniteAtomInteractionHypergraph.encodeInteraction e) graph.interactions).get
      index =
    FiniteAtomInteractionHypergraph.encodeInteraction e
      (graph.interactions.get (decodedInteractionIndex graph e index))
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  rfl

/-- Participants at an arbitrary encoded occurrence are the enumeration of the participants of
the source occurrence named by the inverse transport. -/
theorem encodedInteraction_participants_get_decoded
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.encode e).interactions.length) :
    ((graph.encode e).interactions.get index).participants =
      (graph.interactions.get (decodedInteractionIndex graph e index)).1.map
        (fun atom => (e atom).val) := by
  rw [encodedInteraction_get_decoded]
  rfl

/-- Membership at an encoded occurrence decodes to membership of the same atom at the source
occurrence selected by the inverse interaction-index transport. -/
theorem mem_source_of_mem_encoded (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.encode e).interactions.length) {endpoint : ℕ}
    (member : endpoint ∈ ((graph.encode e).interactions.get index).participants) :
    ∃ atom : V, atom ∈
        (graph.interactions.get (decodedInteractionIndex graph e index)).1 ∧
      (e atom).val = endpoint := by
  rw [encodedInteraction_participants_get_decoded] at member
  exact List.mem_map.mp member

/-- One encoded ledger row: the bond-occurrence position is retained, the interaction occurrence
and both endpoint labels are mapped through the common `e`, and membership evidence is
transported. -/
structure EncodedBondIncidenceEntry (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) where
  bondIndex : ℕ
  interactionIndex : Fin (graph.encode e).interactions.length
  sourceEndpoint : ℕ
  targetEndpoint : ℕ
  source_mem : sourceEndpoint ∈
    ((graph.encode e).interactions.get interactionIndex).participants
  target_mem : targetEndpoint ∈
    ((graph.encode e).interactions.get interactionIndex).participants

namespace BondIncidenceEntry

variable {graph : FiniteAtomInteractionHypergraph V} {source : OrganicDiagramSource V}

/-- Encode one ledger row, preserving its bond-occurrence position and transporting every atom
reference through the same `e` as the graph and the diagram. -/
def encode (entry : BondIncidenceEntry graph source) (e : V ≃ Fin (Fintype.card V)) :
    EncodedBondIncidenceEntry graph e :=
  { bondIndex := entry.bondIndex.val
    interactionIndex := encodedInteractionIndex graph e entry.interactionIndex
    sourceEndpoint := (e (source.bonds.get entry.bondIndex).source).val
    targetEndpoint := (e (source.bonds.get entry.bondIndex).target).val
    source_mem := encoded_mem_of_source_mem graph e entry.interactionIndex entry.source_mem
    target_mem := encoded_mem_of_source_mem graph e entry.interactionIndex entry.target_mem }

@[simp] theorem encode_bondIndex (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (entry.encode e).bondIndex = entry.bondIndex.val := rfl

@[simp] theorem encode_interactionIndex (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (entry.encode e).interactionIndex =
      encodedInteractionIndex graph e entry.interactionIndex := rfl

@[simp] theorem encode_sourceEndpoint (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (entry.encode e).sourceEndpoint =
      (e (source.bonds.get entry.bondIndex).source).val := rfl

@[simp] theorem encode_targetEndpoint (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (entry.encode e).targetEndpoint =
      (e (source.bonds.get entry.bondIndex).target).val := rfl

/-- Separate encoded incidence refinement for the source endpoint. -/
theorem encode_source_mem (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (entry.encode e).sourceEndpoint ∈
      ((graph.encode e).interactions.get (entry.encode e).interactionIndex).participants :=
  (entry.encode e).source_mem

/-- Separate encoded incidence refinement for the target endpoint. -/
theorem encode_target_mem (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (entry.encode e).targetEndpoint ∈
      ((graph.encode e).interactions.get (entry.encode e).interactionIndex).participants :=
  (entry.encode e).target_mem

end BondIncidenceEntry

namespace SourceBoundBondIncidence

variable {graph : FiniteAtomInteractionHypergraph V} {source : OrganicDiagramSource V}

/-- Transport the whole sparse ledger, row by row and in order.  No row is dropped, duplicated,
or reordered. -/
def encode (incidence : SourceBoundBondIncidence graph source)
    (e : V ≃ Fin (Fintype.card V)) : List (EncodedBondIncidenceEntry graph e) :=
  incidence.entries.map fun entry => entry.encode e

@[simp] theorem encode_length (incidence : SourceBoundBondIncidence graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (incidence.encode e).length = incidence.entries.length := by
  simp [encode]

/-- The encoded ledger is literally the ordered image of the source ledger. -/
theorem encode_eq_map (incidence : SourceBoundBondIncidence graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    incidence.encode e = incidence.entries.map (fun entry => entry.encode e) := rfl

end SourceBoundBondIncidence

/-! ### Validity refinement and actual decoding for encoded incidence rows

An `EncodedBondIncidenceEntry` on its own has an arbitrary `bondIndex` and endpoint numbers that
are only constrained to be participants of the named encoded interaction.  It is therefore not
yet tied to the drawn bond it is supposed to annotate.  `Valid` adds exactly that tie, and
`decode` / `decodeIfValid?` turn a valid raw row back into a bounded source row.

No original source or ledger is an input to any decoder below: the source is recovered from the
stored legacy diagram, and the rows are decoded against that recovered source. -/

namespace EncodedBondIncidenceEntry

variable {graph : FiniteAtomInteractionHypergraph V}
variable {source : OrganicDiagramSource V}
variable {e : V ≃ Fin (Fintype.card V)}

/-- Validity refinement for one encoded incidence row against a source drawing annotation.  It
requires the stored bond position to be an actual position in the source bond list and both stored
endpoint indices to be exactly the encodings of that bond's endpoints.  The interaction occurrence
is already typed at `(graph.encode e).interactions.length`; the decoder transports it back through
`decodedInteractionIndex`. -/
structure Valid (entry : EncodedBondIncidenceEntry graph e)
    (source : OrganicDiagramSource V) : Prop where
  bondIndex_lt : entry.bondIndex < source.bonds.length
  sourceEndpoint_eq : entry.sourceEndpoint =
    (e (source.bonds.get ⟨entry.bondIndex, bondIndex_lt⟩).source).val
  targetEndpoint_eq : entry.targetEndpoint =
    (e (source.bonds.get ⟨entry.bondIndex, bondIndex_lt⟩).target).val

/-- The stored bond position is in range for the actual encoded diagram, not merely for an
abstract source. -/
theorem Valid.diagram_bondIndex_lt {entry : EncodedBondIncidenceEntry graph e}
    (valid : entry.Valid source) :
    entry.bondIndex < (OrganicDiagramSource.encodeDiagram e source).bonds.length := by
  simpa [OrganicDiagramSource.encodeDiagram_bonds] using valid.bondIndex_lt

/-- The stored endpoint indices are exactly the endpoints of the actual encoded diagram bond at
the stored position.  This is the diagram-level form of `Valid`. -/
theorem Valid.diagram_bondAt {entry : EncodedBondIncidenceEntry graph e}
    (valid : entry.Valid source) :
    ∃ bond : DiagramBond,
      listGet? (OrganicDiagramSource.encodeDiagram e source).bonds entry.bondIndex = some bond ∧
        bond.source = entry.sourceEndpoint ∧ bond.target = entry.targetEndpoint := by
  refine ⟨OrganicDiagramSource.encodeBond e
      (source.bonds.get ⟨entry.bondIndex, valid.bondIndex_lt⟩),
    OrganicDiagramSource.encodeDiagram_bondAt e source entry.bondIndex valid.bondIndex_lt,
    ?_, ?_⟩
  · exact valid.sourceEndpoint_eq.symm
  · exact valid.targetEndpoint_eq.symm

/-- Decode one validity-certified encoded row to a bounded source row.  The bond occurrence is
reconstructed as a `Fin source.bonds.length`, the interaction occurrence is transported back with
`decodedInteractionIndex`, and both participant-membership proofs are transported from the encoded
interaction to the source interaction. -/
def decode (entry : EncodedBondIncidenceEntry graph e)
    (source : OrganicDiagramSource V) (valid : entry.Valid source) :
    BondIncidenceEntry graph source where
  bondIndex := ⟨entry.bondIndex, valid.bondIndex_lt⟩
  interactionIndex := decodedInteractionIndex graph e entry.interactionIndex
  source_mem := by
    have member := entry.source_mem
    rw [encodedInteraction_participants_get_decoded] at member
    obtain ⟨atom, atom_member, atom_encode⟩ := List.mem_map.mp member
    have atom_eq : atom =
        (source.bonds.get ⟨entry.bondIndex, valid.bondIndex_lt⟩).source := by
      apply e.injective
      apply Fin.ext
      rw [atom_encode, valid.sourceEndpoint_eq]
    simpa [atom_eq] using atom_member
  target_mem := by
    have member := entry.target_mem
    rw [encodedInteraction_participants_get_decoded] at member
    obtain ⟨atom, atom_member, atom_encode⟩ := List.mem_map.mp member
    have atom_eq : atom =
        (source.bonds.get ⟨entry.bondIndex, valid.bondIndex_lt⟩).target := by
      apply e.injective
      apply Fin.ext
      rw [atom_encode, valid.targetEndpoint_eq]
    simpa [atom_eq] using atom_member

/-- Checked decoder for one raw encoded row.  It rejects an out-of-range bond position and endpoint
indices that are not exactly the endpoints of the decoded bond.  Only rows passing both checks are
decoded; no original source row is consulted. -/
def decodeIfValid? (entry : EncodedBondIncidenceEntry graph e)
    (source : OrganicDiagramSource V) : Option (BondIncidenceEntry graph source) :=
  if bondIndex_lt : entry.bondIndex < source.bonds.length then
    if sourceEndpoint_eq : entry.sourceEndpoint =
        (e (source.bonds.get ⟨entry.bondIndex, bondIndex_lt⟩).source).val then
      if targetEndpoint_eq : entry.targetEndpoint =
          (e (source.bonds.get ⟨entry.bondIndex, bondIndex_lt⟩).target).val then
        some (decode entry source
          { bondIndex_lt := bondIndex_lt
            sourceEndpoint_eq := sourceEndpoint_eq
            targetEndpoint_eq := targetEndpoint_eq })
      else none
    else none
  else none

/-- On a valid row the checked decoder succeeds and agrees with the validity-certified decoder. -/
theorem decodeIfValid?_eq_some_decode (entry : EncodedBondIncidenceEntry graph e)
    (source : OrganicDiagramSource V) (valid : entry.Valid source) :
    entry.decodeIfValid? source = some (entry.decode source valid) := by
  unfold decodeIfValid?
  rw [dif_pos valid.bondIndex_lt, dif_pos valid.sourceEndpoint_eq,
    dif_pos valid.targetEndpoint_eq]

/-- An out-of-range bond position is rejected rather than reinterpreted. -/
theorem decodeIfValid?_eq_none_of_bondIndex (entry : EncodedBondIncidenceEntry graph e)
    (source : OrganicDiagramSource V)
    (outOfBounds : ¬ entry.bondIndex < source.bonds.length) :
    entry.decodeIfValid? source = none := by
  unfold decodeIfValid?
  rw [dif_neg outOfBounds]

/-- Every encoded source row satisfies the validity refinement, using exactly the input row's
bound and endpoints.  This is the discharge of `Valid` for encoder images. -/
def Valid.ofEncode (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) : (entry.encode e).Valid source where
  bondIndex_lt := entry.bondIndex.isLt
  sourceEndpoint_eq := rfl
  targetEndpoint_eq := rfl

/-- Decoding an encoded row returns the original source row exactly. -/
theorem decode_ofEncode (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (entry.encode e).decode source (Valid.ofEncode entry e) = entry := by
  rfl

/-- Checked decoding of an encoded row returns the original source row exactly. -/
@[simp] theorem decodeIfValid?_ofEncode (entry : BondIncidenceEntry graph source)
    (e : V ≃ Fin (Fintype.card V)) :
    (entry.encode e).decodeIfValid? source = some entry := by
  rw [decodeIfValid?_eq_some_decode (entry.encode e) source (Valid.ofEncode entry e)]
  rw [decode_ofEncode]

/-- Whole-ledger checked decoding of the ordered encoded ledger.  Order and multiplicity are
retained: the result is the list of decoded rows in exactly the input order. -/
theorem mapM_decodeIfValid?_ofEncode (source : OrganicDiagramSource V)
    (entries : List (BondIncidenceEntry graph source)) :
    (entries.map (fun entry => entry.encode e)).mapM
        (fun entry => entry.decodeIfValid? source) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
      simp [decodeIfValid?_ofEncode, inductionHypothesis]

/-- Every validity-certified list of encoded rows decodes to some ordered source list.  This is
the "valid bundles do not reject" direction of the checked decoder. -/
theorem mapM_decodeIfValid?_eq_some_of_valid (source : OrganicDiagramSource V)
    (entries : List (EncodedBondIncidenceEntry graph e))
    (valid : ∀ entry, entry ∈ entries → entry.Valid source) :
    ∃ decoded, entries.mapM (fun entry => entry.decodeIfValid? source) = some decoded := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons entry entries inductionHypothesis =>
      have headValid : entry.Valid source := valid entry (by simp)
      have tailValid : ∀ other, other ∈ entries → other.Valid source :=
        fun other member => valid other (List.mem_cons_of_mem entry member)
      obtain ⟨decodedTail, decodedTail_eq⟩ := inductionHypothesis tailValid
      refine ⟨entry.decode source headValid :: decodedTail, ?_⟩
      rw [List.mapM_cons]
      rw [decodeIfValid?_eq_some_decode entry source headValid]
      rw [decodedTail_eq]
      rfl

/-- If one row of a list fails the checked decoder, the whole ordered decoding fails. -/
theorem mapM_eq_none_of_mem {α β : Type*} {f : α → Option β}
    {values : List α} {value : α} (member : value ∈ values) (failure : f value = none) :
    values.mapM f = none := by
  induction values with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [List.mapM_cons]
      rcases List.mem_cons.mp member with equal | memberTail
      · subst value
        simp [failure]
      · cases observed : f head with
        | none => simp
        | some headValue =>
            have tailFailure := inductionHypothesis memberTail
            simp [tailFailure]

end EncodedBondIncidenceEntry

end SourceBoundSidecar

section SourceBoundDiagramCarrier

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Annotated source drawing data: the bare drawing data plus its incidence sidecar. -/
structure SourceBoundDiagram (graph : FiniteAtomInteractionHypergraph V) where
  source : OrganicDiagramSource V
  incidence : SourceBoundBondIncidence graph source

end SourceBoundDiagramCarrier

namespace SourceBoundDiagram

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {graph : FiniteAtomInteractionHypergraph V}

/-- Erase the sidecar, keeping only the drawing data that the public diagram types can express. -/
def eraseIncidence (annotated : SourceBoundDiagram graph) : OrganicDiagramSource V :=
  annotated.source

/-- The encoded bare diagram of an annotated record.  By construction it cannot depend on the
sidecar, because the public `DiagramConfiguration` has no interaction-occurrence field. -/
def bareEncoded (e : V ≃ Fin (Fintype.card V)) (annotated : SourceBoundDiagram graph) :
    DiagramConfiguration :=
  OrganicDiagramSource.encodeDiagram e annotated.source

/-- The encoded bare diagram is independent of the sidecar. -/
theorem bareEncoded_ignores_incidence (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V)
    (first second : SourceBoundBondIncidence graph source) :
    bareEncoded e ⟨source, first⟩ = bareEncoded e ⟨source, second⟩ := rfl

/-- **Non-injectivity of bare-diagram erasure.**  Whenever two distinct source-bound sidecars
exist over the same drawing data, the encoded public diagram cannot distinguish them: the bare
`DiagramConfiguration` is not injective on the source-bound metadata. -/
theorem bareEncoded_not_injective_of_distinct_incidence
    (e : V ≃ Fin (Fintype.card V)) (source : OrganicDiagramSource V)
    {first second : SourceBoundBondIncidence graph source} (distinct : first ≠ second) :
    ¬ Function.Injective fun annotated : SourceBoundDiagram graph =>
      OrganicDiagramSource.encodeDiagram e annotated.source := by
  intro injective
  have imagesEqual : OrganicDiagramSource.encodeDiagram e
        (SourceBoundDiagram.mk source first).source =
      OrganicDiagramSource.encodeDiagram e (SourceBoundDiagram.mk source second).source := rfl
  have recordsEqual : SourceBoundDiagram.mk source first =
      SourceBoundDiagram.mk source second := injective imagesEqual
  have incidenceEqual : first = second := by
    injection recordsEqual with _ fieldEqual
  exact distinct incidenceEqual

/-- Unencoded erasure of the sidecar is likewise not injective whenever two distinct sidecars
exist over the same drawing data. -/
theorem eraseIncidence_not_injective_of_distinct_incidence
    (source : OrganicDiagramSource V)
    {first second : SourceBoundBondIncidence graph source} (distinct : first ≠ second) :
    ¬ Function.Injective fun annotated : SourceBoundDiagram graph => annotated.source := by
  intro injective
  have recordsEqual : SourceBoundDiagram.mk source first =
      SourceBoundDiagram.mk source second := injective rfl
  have incidenceEqual : first = second := by
    injection recordsEqual with _ fieldEqual
  exact distinct incidenceEqual

end SourceBoundDiagram

/-! ## Actual bundled encoding

The certified authoritative input alone cannot carry partial positions or incidence rows.  The
bundle below stores the certified source together with the encoded sidecars.  It does not store
the source drawing data as an opaque parameter: the source is recovered from the bundle by
decoding.

* The partial-position sidecar has an unconditional exact inverse (`decodePartialPositions`).
* The incidence sidecar has a *checked* decoder (`decodeIncidence?`): it decodes the stored legacy
  diagram, then turns each raw encoded row into a bounded source row only if the row is `Valid`
  against that decoded source.  Arbitrary raw bundles with out-of-range bond positions or endpoints
  not matching the drawn bond are rejected; every bundle produced by `encodeDiagramBundle` carries
  a proof of `Valid`, and the decoder recovers the complete ordered ledger.

The earlier `incidence = incidence.encode e` field lemma alone was only a stored-image statement;
`decodeIncidence?_encodeDiagramBundle` is the actual ordered recovery theorem. -/

section EncodedBundle

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Certified authoritative source plus the encoded supplementary sidecars. -/
structure EncodedDiagramBundle (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) where
  /-- The certified authoritative input, including the encoded legacy diagram channel. -/
  certified : CertifiedAuthoritativeChemicalInput
  /-- The encoded partial-position sidecar, indexed by the common enumeration. -/
  partialPositions : Fin (Fintype.card V) → Option CartesianPoint2
  /-- The encoded sparse incidence ledger. -/
  incidence : List (EncodedBondIncidenceEntry graph e)

/-- Bundle the certified authoritative encoding together with both encoded sidecars. -/
def encodeDiagramBundle (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (source : OrganicDiagramSource V)
    (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) : EncodedDiagramBundle graph e :=
  { certified := certifiedDiagramEncoding graph e source endpointDistinct
    partialPositions := partialEvidence.encode e
    incidence := incidence.encode e }

@[simp] theorem encodeDiagramBundle_certified (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (source : OrganicDiagramSource V)
    (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).certified =
      certifiedDiagramEncoding graph e source endpointDistinct := rfl

@[simp] theorem encodeDiagramBundle_partialPositions
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).partialPositions =
      partialEvidence.encode e := rfl

@[simp] theorem encodeDiagramBundle_incidence (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (source : OrganicDiagramSource V)
    (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).incidence =
      incidence.encode e := rfl

namespace EncodedDiagramBundle

variable {graph : FiniteAtomInteractionHypergraph V}
variable {e : V ≃ Fin (Fintype.card V)}

/-- The legacy diagram channel stored in the bundle. -/
def diagram? (bundle : EncodedDiagramBundle graph e) : Option DiagramConfiguration :=
  bundle.certified.input.diagram?

/-- Decode the full source drawing data from the bundle's legacy diagram channel. -/
def decodeDiagram? (bundle : EncodedDiagramBundle graph e) :
    Option (OrganicDiagramSource V) :=
  match bundle.diagram? with
  | none => none
  | some diagram => OrganicDiagramSource.decodeDiagram? e diagram

/-- Decode the partial-position sidecar back to independent atom labels. -/
def decodePartialPositions (bundle : EncodedDiagramBundle graph e) :
    SourcePartialPositions V :=
  SourcePartialPositions.decode e bundle.partialPositions

/-- The bundle recovers the full source drawing data exactly, without any extra source parameter. -/
theorem decodeDiagram?_encodeDiagramBundle (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (source : OrganicDiagramSource V)
    (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).decodeDiagram? =
      some source := by
  simp [EncodedDiagramBundle.decodeDiagram?, EncodedDiagramBundle.diagram?,
    encodeDiagramBundle, OrganicDiagramSource.decodeDiagram?_encodeDiagram]

/-- The bundle recovers the partial-position sidecar exactly, absences included. -/
@[simp] theorem decodePartialPositions_encodeDiagramBundle
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).decodePartialPositions =
      partialEvidence := by
  simp [EncodedDiagramBundle.decodePartialPositions, encodeDiagramBundle,
    SourcePartialPositions.decode_encode]

/-- The bundle retains the whole encoded incidence ledger; nothing is dropped. -/
theorem encodeDiagramBundle_retains_incidence
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).incidence =
      incidence.encode e := rfl

/-- The bundle's certified input carries exactly the encoded legacy diagram. -/
@[simp] theorem encodeDiagramBundle_diagram?
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (source : OrganicDiagramSource V) (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).diagram? =
      some (OrganicDiagramSource.encodeDiagram e source) := by
  simp [EncodedDiagramBundle.diagram?, encodeDiagramBundle]

/-- Bundle refinement.  It ties the certified molecule to the actual encoded graph, ties the stored
legacy diagram to a source drawing annotation, and requires every raw encoded incidence row to be
valid against that same source (in particular, its bond position is in range and its endpoints are
exactly the drawn bond's endpoints).  The existential source is a proposition, not a stored input
or output payload; the stored diagram determines it because `encodeDiagram` is injective. -/
def Valid (bundle : EncodedDiagramBundle graph e) : Prop :=
  bundle.certified.input.molecule = graph.encode e ∧
    ∃ source : OrganicDiagramSource V,
      bundle.diagram? = some (OrganicDiagramSource.encodeDiagram e source) ∧
      ∀ entry, entry ∈ bundle.incidence → entry.Valid source

/-- Checked whole-bundle decoder for the incidence sidecar.  It decodes the stored legacy diagram,
then decodes each raw encoded row against the decoded source.  It takes neither the original source
nor the original ledger as input, and it returns `none` as soon as the certified molecule is not
the encoded graph, the diagram is absent or undecodable, or any row fails the validity check. -/
def decodeIncidence? (bundle : EncodedDiagramBundle graph e) :
    Option (Σ source : OrganicDiagramSource V, SourceBoundBondIncidence graph source) :=
  if _molecule_eq : bundle.certified.input.molecule = graph.encode e then
    match bundle.diagram? with
    | none => none
    | some diagram =>
        match OrganicDiagramSource.decodeDiagram? e diagram with
        | none => none
        | some source =>
            match bundle.incidence.mapM (fun entry => entry.decodeIfValid? source) with
            | none => none
            | some entries => some ⟨source, { entries := entries }⟩
  else none

/-- The bundle produced by `encodeDiagramBundle` satisfies the refinement: its certified molecule is
the encoded graph, its stored diagram is the encoded source drawing, and every encoded row is valid
against that source. -/
theorem encodeDiagramBundle_valid
    (source : OrganicDiagramSource V) (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).Valid := by
  refine ⟨rfl, source, ?_, ?_⟩
  · rfl
  · intro entry member
    rw [encodeDiagramBundle_incidence] at member
    obtain ⟨original, _original_member, equal⟩ := List.mem_map.mp member
    rw [← equal]
    exact EncodedBondIncidenceEntry.Valid.ofEncode original e

/-- **Entire ledger recovery.**  The checked bundle decoder recovers both the source drawing data
and the complete ordered incidence ledger from a bundle produced by `encodeDiagramBundle`, without
any original source or ledger parameter.  Since the result is the whole list, order and
multiplicity are preserved. -/
theorem decodeIncidence?_encodeDiagramBundle
    (source : OrganicDiagramSource V) (partialEvidence : SourcePartialPositions V)
    (incidence : SourceBoundBondIncidence graph source)
    (endpointDistinct : source.EndpointDistinct) :
    (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).decodeIncidence? =
      some ⟨source, incidence⟩ := by
  unfold decodeIncidence?
  have molecule_eq :
      (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).certified.input.molecule =
        graph.encode e := rfl
  rw [dif_pos molecule_eq]
  rw [encodeDiagramBundle_diagram?]
  dsimp only
  rw [OrganicDiagramSource.decodeDiagram?_encodeDiagram]
  dsimp only
  rw [show (encodeDiagramBundle graph e source partialEvidence incidence endpointDistinct).incidence =
      incidence.entries.map (fun entry => entry.encode e) from rfl]
  rw [EncodedBondIncidenceEntry.mapM_decodeIfValid?_ofEncode]

/-- Every valid bundle is accepted by the checked decoder.  Combined with
`decodeIncidence?_eq_none_of_bondIndex_out_of_bounds`, this is the "accept valid / reject invalid"
behaviour of the partial decoder. -/
theorem decodeIncidence?_eq_some_of_valid (bundle : EncodedDiagramBundle graph e)
    (valid : bundle.Valid) :
    ∃ source : OrganicDiagramSource V,
      ∃ ledger : SourceBoundBondIncidence graph source,
        bundle.decodeIncidence? = some ⟨source, ledger⟩ := by
  obtain ⟨molecule_eq, source, diagram_eq, entries_valid⟩ := valid
  obtain ⟨decodedEntries, decodedEntries_eq⟩ :=
    EncodedBondIncidenceEntry.mapM_decodeIfValid?_eq_some_of_valid source bundle.incidence
      entries_valid
  refine ⟨source, { entries := decodedEntries }, ?_⟩
  unfold decodeIncidence?
  rw [dif_pos molecule_eq]
  rw [diagram_eq]
  dsimp only
  rw [OrganicDiagramSource.decodeDiagram?_encodeDiagram]
  dsimp only
  rw [decodedEntries_eq]

/-- An out-of-range bond position makes the checked decoder reject the whole bundle.  The decoder
therefore does not reinterpret arbitrary `bondIndex` values as positions in the drawn bond list. -/
theorem decodeIncidence?_eq_none_of_bondIndex_out_of_bounds
    (bundle : EncodedDiagramBundle graph e) (source : OrganicDiagramSource V)
    (diagram_eq : bundle.diagram? = some (OrganicDiagramSource.encodeDiagram e source))
    {entry : EncodedBondIncidenceEntry graph e} (member : entry ∈ bundle.incidence)
    (outOfBounds : source.bonds.length ≤ entry.bondIndex) :
    bundle.decodeIncidence? = none := by
  unfold decodeIncidence?
  by_cases molecule_eq : bundle.certified.input.molecule = graph.encode e
  · rw [dif_pos molecule_eq]
    rw [diagram_eq]
    dsimp only
    rw [OrganicDiagramSource.decodeDiagram?_encodeDiagram]
    dsimp only
    have failure : (fun row : EncodedBondIncidenceEntry graph e => row.decodeIfValid? source)
        entry = none :=
      EncodedBondIncidenceEntry.decodeIfValid?_eq_none_of_bondIndex entry source
        (Nat.not_lt.mpr outOfBounds)
    rw [EncodedBondIncidenceEntry.mapM_eq_none_of_mem
      (f := fun row => row.decodeIfValid? source) member failure]
  · rw [dif_neg molecule_eq]

end EncodedDiagramBundle

end EncodedBundle

/-! ## Ordered reference frames

A supplied ordered neighbour frame is encoded through the same `e` as the graph and the diagram.
The parity token is copied syntactically.  The final theorem shows that reordering the supplied
neighbour list changes the encoded token; this is a syntactic observation only, and it is exactly
why no physical parity-invariance claim is made. -/

/-- An explicitly supplied ordered reference frame around one centre atom, with a syntactic
tetrahedral input token. -/
structure OrderedReferenceFrame (V : Type*) where
  centre : V
  neighbours : List V
  parity : TetrahedralInputParity

namespace OrderedReferenceFrame

variable {V : Type*} [Fintype V]

/-- Encode the frame with the same enumeration used for the graph.  The ordered neighbour list is
mapped in order, the centre is mapped by the same equivalence, and the parity token is copied. -/
def encode (e : V ≃ Fin (Fintype.card V)) (frame : OrderedReferenceFrame V) :
    List ℕ × (ℕ × TetrahedralInputParity) :=
  (frame.neighbours.map fun atom => (e atom).val, (e frame.centre).val, frame.parity)

@[simp] theorem encode_neighbours (e : V ≃ Fin (Fintype.card V))
    (frame : OrderedReferenceFrame V) :
    (frame.encode e).1 = frame.neighbours.map fun atom => (e atom).val := rfl

@[simp] theorem encode_centre (e : V ≃ Fin (Fintype.card V))
    (frame : OrderedReferenceFrame V) :
    (frame.encode e).2.1 = (e frame.centre).val := rfl

@[simp] theorem encode_parity (e : V ≃ Fin (Fintype.card V))
    (frame : OrderedReferenceFrame V) :
    (frame.encode e).2.2 = frame.parity := rfl

/-- Every atom named by the frame is referred to by the same index under which the graph encoding
stores it.  This is the formal content of "the frame must use the same enumeration". -/
theorem encode_agrees_with_graph [DecidableEq V]
    (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (frame : OrderedReferenceFrame V) {atom : V}
    (_member : atom ∈ frame.centre :: frame.neighbours) :
    listGet? (graph.encode e).atoms (e atom).val = some (graph.atomData atom) := by
  simpa using graph.encode_atomAt e (e atom)

/-- Reordering the supplied neighbour list changes the encoded ordered token.  This is only a
syntactic statement about the encoding of an ordered list; it is not a statement about physical
parity. -/
theorem reordered_neighbours_change_token (e : V ≃ Fin (Fintype.card V)) {first second : V}
    (distinct : first ≠ second) :
    (((OrderedReferenceFrame.mk first [first, second] .clockwise).encode e).1) ≠
      (((OrderedReferenceFrame.mk first [second, first] .clockwise).encode e).1) := by
  have different : (([first, second] : List V).map fun atom => (e atom).val) ≠
      (([second, first] : List V).map fun atom => (e atom).val) := by
    intro equal
    have valuesEqual : (e first).val = (e second).val := by
      simpa using congrArg (fun values : List ℕ => values.head?) equal
    exact distinct (e.injective (Fin.ext valuesEqual))
  simpa [encode] using different

end OrderedReferenceFrame

/-! ## Concrete non-vacuity witness

One three-atom source with two identical `multicenter` interactions and one bond annotation
between two of the three participants.  This simultaneously exhibits

* a sidecar bound to a *non-binary, non-covalent* interaction (so annotations are not restricted
  to known binary covalent bonds), and
* two distinct sidecars over the same bare drawing data, so bare-diagram erasure is provably not
  injective on the sidecar metadata. -/

namespace DiagramEncodingExample

/-- Hydrogen, atomic number 1. -/
def hydrogen : PeriodicElement where
  atomicNumber := 1
  positive := by decide
  atMost118 := by decide

/-- The single hydrogen semantic atom used for all three example atoms. -/
def hydrogenAtom : SemanticAtom := { element := hydrogen }

/-- Two identical multicenter interactions over all three atoms.  The repeated occurrence is what
makes two distinct sidecars possible. -/
def graph : FiniteAtomInteractionHypergraph (Fin 3) where
  atomData := fun _ => hydrogenAtom
  interactions := [([0, 1, 2], .multicenter 2), ([0, 1, 2], .multicenter 2)]
  arity_ge_two := by
    intro edge membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl <;> decide
  participants_nodup := by
    intro edge membership
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl <;> decide

/-- One bond annotation between atoms 0 and 1, which are participants of the multicenter
interaction but do not exhaust it. -/
def source : OrganicDiagramSource (Fin 3) where
  positions? := none
  bonds := [{ source := 0, target := 1, style := .plain }]
  atomConfigurations := [{ atom := 2, parity := .anticlockwise, scope := .racemic 7 }]

theorem source_endpointDistinct : source.EndpointDistinct := by
  intro bond membership
  simp only [source, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl
  decide

/-- A sparse incidence row naming the bond occurrence at position 0 and source interaction 0. -/
def entryZero : BondIncidenceEntry graph source where
  bondIndex := ⟨0, by decide⟩
  interactionIndex := ⟨0, by decide⟩
  source_mem := by decide
  target_mem := by decide

/-- A sparse incidence row naming the same bond occurrence and source interaction 1.  It has
exactly the same participant evidence, so it is a genuine alternative row for the same bare
drawing data. -/
def entryOne : BondIncidenceEntry graph source where
  bondIndex := ⟨0, by decide⟩
  interactionIndex := ⟨1, by decide⟩
  source_mem := by decide
  target_mem := by decide

/-- The ledger with the single row at interaction 0. -/
def incidenceZero : SourceBoundBondIncidence graph source := { entries := [entryZero] }

/-- The ledger with the single row at interaction 1. -/
def incidenceOne : SourceBoundBondIncidence graph source := { entries := [entryOne] }

theorem entryZero_ne_entryOne : entryZero ≠ entryOne := by
  intro equal
  have interactionEqual := congrArg
    (fun entry : BondIncidenceEntry graph source => entry.interactionIndex) equal
  exact absurd interactionEqual (by decide)

/-- The two ledgers really differ: they name different source interaction occurrences. -/
theorem incidenceZero_ne_incidenceOne : incidenceZero ≠ incidenceOne := by
  intro equal
  have entriesEqual : ([entryZero] : List (BondIncidenceEntry graph source)) = [entryOne] :=
    congrArg
      (fun incidence : SourceBoundBondIncidence graph source => incidence.entries) equal
  have headEqual : (some entryZero : Option (BondIncidenceEntry graph source)) = some entryOne := by
    simpa using congrArg
      (fun entries : List (BondIncidenceEntry graph source) => entries.head?) entriesEqual
  exact entryZero_ne_entryOne (Option.some.inj headEqual)

/-- Incidence rows are genuinely sparse and multi-valued: the same bond occurrence is attached to
two distinct source interaction occurrences. -/
theorem entries_share_bond_occurrence :
    entryZero.bondIndex = entryOne.bondIndex ∧
      entryZero.interactionIndex ≠ entryOne.interactionIndex := by
  refine ⟨rfl, ?_⟩
  intro equal
  exact absurd (congrArg Fin.val equal) (by decide)

/-- The ledger row's interaction names a multicenter interaction, not a binary covalent bond. -/
theorem entryZero_is_multicenter :
    (graph.interactions.get entryZero.interactionIndex).2 =
      SemanticInteractionKind.multicenter 2 := by
  rfl

def annotatedZero : SourceBoundDiagram graph := ⟨source, incidenceZero⟩
def annotatedOne : SourceBoundDiagram graph := ⟨source, incidenceOne⟩

theorem annotatedZero_ne_annotatedOne : annotatedZero ≠ annotatedOne := by
  intro equal
  unfold annotatedZero annotatedOne at equal
  have incidenceEqual : incidenceZero = incidenceOne := by
    injection equal with _ fieldEqual
  exact incidenceZero_ne_incidenceOne incidenceEqual

/-- Bare-diagram erasure is not injective on the sidecar metadata, concretely. -/
theorem example_bareDiagram_not_injective :
    ¬ Function.Injective fun annotated : SourceBoundDiagram graph => annotated.source :=
  SourceBoundDiagram.eraseIncidence_not_injective_of_distinct_incidence
    source incidenceZero_ne_incidenceOne

/-- The encoded public diagram is likewise not injective on the sidecar metadata, for every
enumeration. -/
theorem example_encodedDiagram_not_injective
    (e : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    ¬ Function.Injective fun annotated : SourceBoundDiagram graph =>
      OrganicDiagramSource.encodeDiagram e annotated.source :=
  SourceBoundDiagram.bareEncoded_not_injective_of_distinct_incidence
    e source incidenceZero_ne_incidenceOne

/-- The certificate construction is non-vacuous on the example: the attached source satisfies the
structural certificate. -/
theorem example_certified_structurallyWellFormed
    (e : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    (certifiedDiagramEncoding graph e source source_endpointDistinct).input.StructurallyWellFormed :=
  (certifiedDiagramEncoding graph e source source_endpointDistinct).structurallyWellFormed

end DiagramEncodingExample

end TetraStereo.OneCenter
