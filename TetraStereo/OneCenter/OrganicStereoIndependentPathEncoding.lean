import TetraStereo.OneCenter.OrganicStereoEmbeddedBondPaths
import TetraStereo.OneCenter.OrganicStereoJointCoreEncoding

set_option autoImplicit false

namespace TetraStereo.OneCenter

open scoped unitInterval
open JointCoreEncoding

universe u v

/-!
# Independent physical bond-path data encoded into source-bound embedded paths

`OrganicStereoEmbeddedBondPaths` provides the certified, source-indexed representation
`BondPathTable` / `SourceBoundEmbeddedBondPaths`, but its independent input form
`EdgeIndexedSourceBoundInput` still carries an *already encoded* `AuthoritativeChemicalInput`:
atom endpoints are `Fin molecule.atomCount`, and the source interaction index is
`Fin molecule.interactions.length`.  The only freedom in that input is the edge index type.
`OrganicStereoFiniteEncoding` supplies the independent atom-labelled source
`FiniteAtomInteractionHypergraph V`, and `OrganicStereoRealConfiguration` supplies real
conformations over an arbitrary atom type `V`.

This module closes the remaining atom-label bridge.  Its input is genuinely independent physical
data over an arbitrary finite atom type `V` and an arbitrary finite edge type `E`:

* a finite atom-labelled interaction hypergraph `graph : FiniteAtomInteractionHypergraph V`;
* one real point per atom label, `conformation : MolecularConformation V`;
* for every edge `e : E` an explicit source interaction occurrence
  `interactionOccurrence e : ℕ` together with its proof of being in range — two edges cannot name
  the same occurrence (`interactionOccurrence_injective`), because the existing representation
  realizes each documented occurrence by exactly one edge;
* two distinct endpoint atom labels `source e`, `target e` and the independent agreement that the
  source interaction's ordered participant list is exactly `[source e, target e]` and that its
  kind is one of the default supported pair kinds
  (`SemanticInteractionKind.isSelectedPairKind`, i.e. covalent of any order, aromatic,
  coordinate, or delocalized, restricted to the binary endpoint condition);
* an arbitrary continuous arc `arc e : C(I, EuclideanSpace ℝ (Fin 3))`;
* the independent geometric embedding obligations: arc endpoints are the atom positions, the
  conformation is injective, each arc is injective, arc interiors avoid all atoms, and distinct
  arcs meet only at a common endpoint atom.

None of the existing encoded structures (`BondPathTable`, `RealizesSourceBondPaths`,
`SourceBoundEmbeddedBondPaths`) appears as an input hypothesis.  They are *constructed* here.

The construction uses the *same* atom enumeration for all channels: the graph is encoded by
`graph.encode enumeration`, the real conformation is reindexed by the common atom equivalence
`JointCoreEncoding.sourceAtomEquiv graph enumeration`, and every edge's source occurrence is
mapped by `JointCoreEncoding.encodedIndex graph enumeration`.  The edge type is mapped by the
caller's chosen equivalence `E ≃ Fin (Fintype.card E)`.  The whole source is retained: every
hyperedges (including multicenter, ionic, metallic, hydrogen-bond and `.other` interactions) stays
in the encoded molecule; only the documented subset is referenced by the path table, and
interactions outside it are never used as an edge source.

Main results:

* `toBondPathTable` / `toSourceBound` construct the existing representation;
* exact recovery of every arc value, oriented endpoint index, source occurrence index, documented
  subset, encoded source molecule and conformation;
* `toSourceBound_injective`: the encoding is injective on the entire independent data record, so
  the encoded record determines the graph, the conformation, every occurrence index, every
  endpoint label and every arc (proof fields are recovered by proof irrelevance).  This is
  full-data injectivity, not a constructed total decoder: the non-dependent observers used in the
  proof are total on source-bound records but recover the independent data only on the image of
  `toSourceBound`;
* `enumeration_transport_*`: changing the atom enumeration only relabels indices through the one
  common permutation; the physical arcs, occurrence indices and recovered atom labels are
  unchanged;
* optional, separately stated completeness (`CompleteForSourcePairBonds`) for the default pair
  bond specification, with the induced `CompleteBondPathTable`.

Scope boundaries: this is a representation/transport layer.  It asserts no embedding existence,
no chemical admissibility, no rational or piecewise-linear restriction, and no topological,
chirality or link-classification verdict.  Completeness of the documented subset is never assumed
silently: it is an explicit hypothesis of `toCompleteBondPathTable`.
-/

/-! ## Generic atom- and index-label transport -/

/-- The endpoint lookup of an independent bond path, on the physical atom type.  This mirrors
`SourceBondPath.endpointAt?` before any enumeration is chosen. -/
noncomputable def sourceEndpointAt? {V E : Type*} (source target : E → V) (e : E) (t : I) :
    Option V :=
  if t = 0 then some (source e) else if t = 1 then some (target e) else none

/-- Generic atom-label transport for the independent source: two hypergraphs with the same atom
data function and the same ordered interaction list are the same hypergraph.  The well-formedness
fields are proposition-valued and are identified by proof irrelevance. -/
theorem FiniteAtomInteractionHypergraph.ext_of_atomData_interactions
    {V : Type*} [DecidableEq V] [Fintype V]
    {first second : FiniteAtomInteractionHypergraph V}
    (atomData : first.atomData = second.atomData)
    (interactions : first.interactions = second.interactions) : first = second := by
  obtain ⟨firstAtomData, firstInteractions, firstArity, firstNodup⟩ := first
  obtain ⟨secondAtomData, secondInteractions, secondArity, secondNodup⟩ := second
  dsimp only at atomData interactions
  cases atomData
  cases interactions
  rfl

/-- Heterogeneous congruence for a dependent field/function: equal inputs give heterogeneously
equal values even when the codomain type depends on the input.  This is the transport principle
used to compare the conformation and table fields of the source-bound record. -/
theorem heq_field {α : Sort u} {β : α → Sort v} {a b : α} (h : a = b)
    (f : (x : α) → β x) : HEq (f a) (f b) := by
  cases h
  rfl

/-- Exact encoded interaction lookup, stated directly in terms of the encoded molecule (the
certified wrapper stores the same molecule definitionally). -/
theorem FiniteAtomInteractionHypergraph.encode_get
    {V : Type*} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin graph.interactions.length) :
    (graph.encode enumeration).interactions.get (encodedIndex graph enumeration index) =
      FiniteAtomInteractionHypergraph.encodeInteraction enumeration
        (graph.interactions.get index) := by
  simpa using encoded_get graph enumeration index

/-! ## Independent finite-atom physical bond-path data -/

/-- Independent physical bond-path data over an arbitrary finite atom type `V` and an arbitrary
finite edge type `E`.

Every field is stated on the physical atom labels or on the chosen occurrence index; no encoded
atom index (`Fin atomCount`), no encoded interaction index and no `BondPathTable` appears in the
input.  The only compatibility demanded of an edge with its source interaction is the physical
one: the source hyperedge at the named occurrence lists exactly these two distinct atom labels in
this order, and its kind is one of the default supported pair kinds. -/
structure IndependentBondPathData (V : Type*) [DecidableEq V] [Fintype V]
    (E : Type*) [Fintype E] where
  /-- The independently specified finite atom-labelled interaction hypergraph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- One real point per independent atom label. -/
  conformation : MolecularConformation V
  /-- The concrete source interaction occurrence realized by each edge. -/
  interactionOccurrence : E → ℕ
  /-- Every occurrence index is an actual index of the source interaction list. -/
  interactionOccurrence_lt : ∀ e, interactionOccurrence e < graph.interactions.length
  /-- Two edges never name the same source occurrence. -/
  interactionOccurrence_injective : Function.Injective interactionOccurrence
  /-- Oriented first endpoint atom label. -/
  source : E → V
  /-- Oriented second endpoint atom label. -/
  target : E → V
  /-- The two endpoints of an edge are distinct atoms. -/
  source_ne_target : ∀ e, source e ≠ target e
  /-- Arbitrary continuous arc in ambient real three-space. -/
  arc : E → C(I, EmbeddedReal3)
  /-- Independent participant-list compatibility: the named source interaction lists exactly the
  two endpoint labels, in this order and with multiplicity one. -/
  participants_exact :
    ∀ e, (graph.interactions.get
      ⟨interactionOccurrence e, interactionOccurrence_lt e⟩).1 = [source e, target e]
  /-- Independent kind compatibility: the named source interaction is one of the default supported
  pair-bond kinds.  The binary participant condition above excludes every hyperedge. -/
  kind_selected :
    ∀ e, SemanticInteractionKind.isSelectedPairKind
      (graph.interactions.get ⟨interactionOccurrence e, interactionOccurrence_lt e⟩).2 = true
  /-- Arc start points coincide with the atom positions. -/
  source_endpoint : ∀ e, arc e 0 = conformation (source e)
  /-- Arc end points coincide with the atom positions. -/
  target_endpoint : ∀ e, arc e 1 = conformation (target e)
  /-- Distinct atoms occupy distinct points. -/
  atom_injective : Function.Injective conformation
  /-- Every arc is injective on the unit interval. -/
  arc_injective : ∀ e, Function.Injective (arc e)
  /-- Arc interiors avoid every atom position. -/
  interior_avoids_atoms :
    ∀ e (t : I), t ≠ 0 → t ≠ 1 → ∀ atom, arc e t ≠ conformation atom
  /-- Distinct arcs meet only at a common endpoint atom. -/
  intersects_only_at_common_endpoints :
    ∀ e f (t s : I), e ≠ f → arc e t = arc f s →
      ∃ atom : V,
        sourceEndpointAt? source target e t = some atom ∧
          sourceEndpointAt? source target f s = some atom

namespace IndependentBondPathData

variable {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]

/-- The source occurrence index as a genuine `Fin` index of the source interaction list. -/
def interactionIndex (data : IndependentBondPathData V E) (e : E) :
    Fin data.graph.interactions.length :=
  ⟨data.interactionOccurrence e, data.interactionOccurrence_lt e⟩

@[simp] theorem interactionIndex_val (data : IndependentBondPathData V E) (e : E) :
    (data.interactionIndex e).val = data.interactionOccurrence e := rfl

/-- The participant-list compatibility, restated at `interactionIndex`. -/
theorem interactionIndex_participants_exact (data : IndependentBondPathData V E) (e : E) :
    (data.graph.interactions.get (data.interactionIndex e)).1 = [data.source e, data.target e] :=
  data.participants_exact e

/-- The kind compatibility, restated at `interactionIndex`. -/
theorem interactionIndex_kind_selected (data : IndependentBondPathData V E) (e : E) :
    SemanticInteractionKind.isSelectedPairKind
      (data.graph.interactions.get (data.interactionIndex e)).2 = true :=
  data.kind_selected e

/-- The independent endpoint lookup of an edge. -/
noncomputable abbrev endpointAt? (data : IndependentBondPathData V E) (e : E) (t : I) :
    Option V :=
  sourceEndpointAt? data.source data.target e t

@[simp] theorem endpointAt?_zero (data : IndependentBondPathData V E) (e : E) :
    data.endpointAt? e 0 = some (data.source e) := by
  simp [endpointAt?, sourceEndpointAt?]

@[simp] theorem endpointAt?_one (data : IndependentBondPathData V E) (e : E) :
    data.endpointAt? e 1 = some (data.target e) := by
  simp [endpointAt?, sourceEndpointAt?]

/-! ### The common atom equivalence and the encoded conformation -/

/-- The real conformation expressed at the encoded atom index, using exactly the same atom
equivalence as `graph.encode enumeration`. -/
noncomputable def encodedConformation (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    MolecularConformation (Fin (data.graph.encode enumeration).atomCount) :=
  MolecularConformation.reindex (sourceAtomEquiv data.graph enumeration) data.conformation

@[simp] theorem encodedConformation_apply (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (data.graph.encode enumeration).atomCount) :
    data.encodedConformation enumeration index =
      data.conformation ((sourceAtomEquiv data.graph enumeration).symm index) := rfl

/-- Reindexing the encoded conformation back through the inverse atom equivalence recovers the
original independent conformation exactly. -/
theorem encodedConformation_reindex (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    MolecularConformation.reindex (sourceAtomEquiv data.graph enumeration).symm
        (data.encodedConformation enumeration) = data.conformation :=
  MolecularConformation.reindex_reindex (sourceAtomEquiv data.graph enumeration) data.conformation

/-! ### One encoded source-indexed bond path -/

/-- The encoded `SourceBondPath` of an independent edge.

The source interaction index is the `encodedIndex` of the independent occurrence index, the
oriented endpoints are the `sourceAtomEquiv` images of the independent atom labels, and the arc is
the independent continuous arc unchanged.  The participant equation is derived from the
independent participant-list compatibility; it is not assumed in encoded form. -/
noncomputable def sourceBondPath (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    SourceBondPath (data.graph.encode enumeration) where
  sourceInteraction := encodedIndex data.graph enumeration (data.interactionIndex e)
  source := sourceAtomEquiv data.graph enumeration (data.source e)
  target := sourceAtomEquiv data.graph enumeration (data.target e)
  source_ne_target := by
    intro equal
    exact data.source_ne_target e ((sourceAtomEquiv data.graph enumeration).injective equal)
  participants_exact := by
    rw [FiniteAtomInteractionHypergraph.encode_get data.graph enumeration (data.interactionIndex e)]
    change (data.graph.interactions.get (data.interactionIndex e)).1.map
        (fun atom => (enumeration atom).val) =
      [(sourceAtomEquiv data.graph enumeration (data.source e)).val,
        (sourceAtomEquiv data.graph enumeration (data.target e)).val]
    rw [data.interactionIndex_participants_exact e]
    rfl
  arc := data.arc e

@[simp] theorem sourceBondPath_sourceInteraction (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (data.sourceBondPath enumeration e).sourceInteraction =
      encodedIndex data.graph enumeration (data.interactionIndex e) := rfl

@[simp] theorem sourceBondPath_source (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (data.sourceBondPath enumeration e).source =
      sourceAtomEquiv data.graph enumeration (data.source e) := rfl

@[simp] theorem sourceBondPath_target (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (data.sourceBondPath enumeration e).target =
      sourceAtomEquiv data.graph enumeration (data.target e) := rfl

@[simp] theorem sourceBondPath_arc (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (data.sourceBondPath enumeration e).arc = data.arc e := rfl

@[simp] theorem sourceBondPath_sourceInteraction_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (data.sourceBondPath enumeration e).sourceInteraction.val = data.interactionOccurrence e := by
  unfold sourceBondPath
  simp [encodedIndex, interactionIndex]

@[simp] theorem sourceBondPath_source_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (data.sourceBondPath enumeration e).source.val = (enumeration (data.source e)).val :=
  sourceAtomEquiv_apply_val data.graph enumeration (data.source e)

@[simp] theorem sourceBondPath_target_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (data.sourceBondPath enumeration e).target.val = (enumeration (data.target e)).val :=
  sourceAtomEquiv_apply_val data.graph enumeration (data.target e)

/-- Endpoint lookup commutes with the common atom equivalence: the encoded path's endpoint at a
parameter is the image of the independent endpoint at that parameter. -/
theorem sourceBondPath_endpointAt? (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) (t : I) :
    (data.sourceBondPath enumeration e).endpointAt? t =
      (sourceEndpointAt? data.source data.target e t).map
        (sourceAtomEquiv data.graph enumeration) := by
  unfold SourceBondPath.endpointAt? sourceEndpointAt?
  by_cases zero : t = 0
  · subst zero
    simp
  · by_cases one : t = 1
    · subst one
      simp
    · simp [zero, one]

/-! ### The constructed finite bond-path table -/

/-- The documented source interaction indices, namely the encoded occurrences actually realized by
an edge.  Interactions outside this image stay in the source untouched. -/
def documented (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    Finset (Fin (data.graph.encode enumeration).interactions.length) :=
  Finset.univ.image fun e => encodedIndex data.graph enumeration (data.interactionIndex e)

@[simp] theorem mem_documented_iff (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (data.graph.encode enumeration).interactions.length) :
    index ∈ data.documented enumeration ↔
      ∃ e : E, encodedIndex data.graph enumeration (data.interactionIndex e) = index := by
  simp [documented]

/-- Construct the existing `BondPathTable` from independent physical data.

The molecule is the full encoded graph (all atoms and all interactions, untouched), the
conformation is the common-equivalence reindexing of the independent real conformation, and the
edge family is the family of encoded `SourceBondPath`s.  The realization obligations are proved
from the independent physical conditions. -/
noncomputable def toBondPathTable (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    BondPathTable E (data.graph.encode enumeration) (data.encodedConformation enumeration) where
  documented := data.documented enumeration
  edge := data.sourceBondPath enumeration
  valid :=
    { documented_genuine := by
        intro index hindex
        obtain ⟨e, rfl⟩ := (data.mem_documented_iff enumeration index).mp hindex
        unfold IsGenuinePairBondAt SemanticInteraction.IsGenuinePairBond
          SemanticInteraction.IsSelectedPairBond SemanticInteraction.IsSelectedPairBondWith
        refine ⟨?_, ?_⟩
        · rw [FiniteAtomInteractionHypergraph.encode_get data.graph enumeration
            (data.interactionIndex e)]
          simpa [FiniteAtomInteractionHypergraph.encodeInteraction]
            using data.interactionIndex_kind_selected e
        · unfold SemanticInteraction.HasBinaryEndpoints
          refine ⟨(sourceAtomEquiv data.graph enumeration (data.source e)).val,
            (sourceAtomEquiv data.graph enumeration (data.target e)).val,
            (sourceAtomEquiv data.graph enumeration (data.source e)).isLt,
            (sourceAtomEquiv data.graph enumeration (data.target e)).isLt, ?_, ?_⟩
          · intro equal
            exact data.source_ne_target e
              ((sourceAtomEquiv data.graph enumeration).injective (Fin.ext equal))
          · rw [FiniteAtomInteractionHypergraph.encode_get data.graph enumeration
              (data.interactionIndex e)]
            change (data.graph.interactions.get (data.interactionIndex e)).1.map
                (fun atom => (enumeration atom).val) =
              [(sourceAtomEquiv data.graph enumeration (data.source e)).val,
                (sourceAtomEquiv data.graph enumeration (data.target e)).val]
            rw [data.interactionIndex_participants_exact e]
            rfl
      edge_documented := by
        intro e
        exact (data.mem_documented_iff enumeration _).mpr ⟨e, rfl⟩
      exact_coverage := by
        intro index hindex
        obtain ⟨e, he⟩ := (data.mem_documented_iff enumeration index).mp hindex
        refine ⟨e, ?_, ?_⟩
        · simpa [sourceBondPath_sourceInteraction] using he
        · intro f hf
          have hf' : encodedIndex data.graph enumeration
              (data.interactionIndex f) = encodedIndex data.graph enumeration
                (data.interactionIndex e) := by
            rw [he]
            simpa [sourceBondPath_sourceInteraction, interactionIndex] using hf
          have hindexEq : data.interactionIndex f = data.interactionIndex e :=
            Fin.cast_injective
              (FiniteAtomInteractionHypergraph.encode_interactions_length data.graph enumeration).symm
              hf'
          exact data.interactionOccurrence_injective
            (by simpa [interactionIndex] using hindexEq)
      source_endpoint := by
        intro e
        change data.arc e 0 = data.conformation
          ((sourceAtomEquiv data.graph enumeration).symm
            (sourceAtomEquiv data.graph enumeration (data.source e)))
        rw [Equiv.symm_apply_apply]
        exact data.source_endpoint e
      target_endpoint := by
        intro e
        change data.arc e 1 = data.conformation
          ((sourceAtomEquiv data.graph enumeration).symm
            (sourceAtomEquiv data.graph enumeration (data.target e)))
        rw [Equiv.symm_apply_apply]
        exact data.target_endpoint e
      atom_injective := by
        intro first second equal
        exact (sourceAtomEquiv data.graph enumeration).symm.injective
          (data.atom_injective (by
            simpa [encodedConformation, MolecularConformation.reindex] using equal))
      arc_injective := by
        intro e
        simpa [sourceBondPath_arc] using data.arc_injective e
      interior_avoids_atoms := by
        intro e t ht0 ht1 atom
        simpa [sourceBondPath_arc, encodedConformation, MolecularConformation.reindex] using
          data.interior_avoids_atoms e t ht0 ht1
            ((sourceAtomEquiv data.graph enumeration).symm atom)
      intersects_only_at_common_endpoints := by
        intro e f t s hne hmeet
        have hmeet' : data.arc e t = data.arc f s := by
          simpa [sourceBondPath_arc] using hmeet
        obtain ⟨atom, hatomE, hatomF⟩ :=
          data.intersects_only_at_common_endpoints e f t s hne hmeet'
        refine ⟨sourceAtomEquiv data.graph enumeration atom, ?_, ?_⟩
        · simp [sourceBondPath_endpointAt?, hatomE]
        · simp [sourceBondPath_endpointAt?, hatomF] }

@[simp] theorem toBondPathTable_documented (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (data.toBondPathTable enumeration).documented = data.documented enumeration := rfl

@[simp] theorem toBondPathTable_edge (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (data.toBondPathTable enumeration).edge e = data.sourceBondPath enumeration e := rfl

@[simp] theorem toBondPathTable_sourceInteraction_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    ((data.toBondPathTable enumeration).edge e).sourceInteraction.val =
      data.interactionOccurrence e :=
  data.sourceBondPath_sourceInteraction_val enumeration e

@[simp] theorem toBondPathTable_source_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    ((data.toBondPathTable enumeration).edge e).source.val =
      (enumeration (data.source e)).val :=
  data.sourceBondPath_source_val enumeration e

@[simp] theorem toBondPathTable_target_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    ((data.toBondPathTable enumeration).edge e).target.val =
      (enumeration (data.target e)).val :=
  data.sourceBondPath_target_val enumeration e

@[simp] theorem toBondPathTable_arc (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) (t : I) :
    ((data.toBondPathTable enumeration).edge e).arc t = data.arc e t := rfl

/-- The recovered atom label of an encoded endpoint index: applying the inverse common atom
equivalence recovers the independent physical atom label. -/
theorem toBondPathTable_recovered_source (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (sourceAtomEquiv data.graph enumeration).symm
        ((data.toBondPathTable enumeration).edge e).source = data.source e := by
  rw [toBondPathTable_edge, sourceBondPath_source]
  exact (sourceAtomEquiv data.graph enumeration).symm_apply_apply (data.source e)

/-- The recovered atom label of the encoded target index. -/
theorem toBondPathTable_recovered_target (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (e : E) :
    (sourceAtomEquiv data.graph enumeration).symm
        ((data.toBondPathTable enumeration).edge e).target = data.target e := by
  rw [toBondPathTable_edge, sourceBondPath_target]
  exact (sourceAtomEquiv data.graph enumeration).symm_apply_apply (data.target e)

/-! ### Constructing the existing source-bound record -/

/-- The independent `EdgeIndexedSourceBoundInput`: the encoded authoritative source together with
the common-equivalence conformation and the constructed table. -/
noncomputable def toEdgeIndexed (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) : EdgeIndexedSourceBoundInput E where
  source := data.graph.encodeAuthoritative enumeration
  conformation := data.encodedConformation enumeration
  table := data.toBondPathTable enumeration

/-- Construct the existing `SourceBoundEmbeddedBondPaths` using an explicit chosen equivalence of
the edge type with `Fin (Fintype.card E)`. -/
noncomputable def toSourceBound (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) : SourceBoundEmbeddedBondPaths where
  source := data.graph.encodeAuthoritative enumeration
  edgeCount := Fintype.card E
  conformation := data.encodedConformation enumeration
  table := (data.toBondPathTable enumeration).reindex edgeEquiv

@[simp] theorem toSourceBound_source (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    (data.toSourceBound enumeration edgeEquiv).source =
      data.graph.encodeAuthoritative enumeration := rfl

@[simp] theorem toSourceBound_edgeCount (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    (data.toSourceBound enumeration edgeEquiv).edgeCount = Fintype.card E := rfl

@[simp] theorem toSourceBound_conformation (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    (data.toSourceBound enumeration edgeEquiv).conformation =
      data.encodedConformation enumeration := rfl

/-- Exact recovery of the table edge at the chosen edge index. -/
theorem toSourceBound_edge (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    (data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e) =
      data.sourceBondPath enumeration e := by
  show ((data.toBondPathTable enumeration).reindex edgeEquiv).edge (edgeEquiv e) =
    data.sourceBondPath enumeration e
  rw [BondPathTable.reindex_edge]
  simp

/-- Exact recovery of every arc value. -/
@[simp] theorem toSourceBound_arc (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) (t : I) :
    ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).arc t =
      data.arc e t := by
  rw [toSourceBound_edge]
  rfl

/-- Exact recovery of the encoded oriented source atom index. -/
@[simp] theorem toSourceBound_source_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).source.val =
      (enumeration (data.source e)).val := by
  rw [toSourceBound_edge]
  exact data.sourceBondPath_source_val enumeration e

/-- Exact recovery of the encoded oriented target atom index. -/
@[simp] theorem toSourceBound_target_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).target.val =
      (enumeration (data.target e)).val := by
  rw [toSourceBound_edge]
  exact data.sourceBondPath_target_val enumeration e

/-- Exact recovery of the source interaction occurrence index. -/
@[simp] theorem toSourceBound_sourceInteraction_val (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).sourceInteraction.val =
      data.interactionOccurrence e := by
  rw [toSourceBound_edge]
  exact data.sourceBondPath_sourceInteraction_val enumeration e

/-- The recovered physical atom label of the encoded source endpoint. -/
theorem toSourceBound_recovered_source (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    (sourceAtomEquiv data.graph enumeration).symm
        ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).source =
      data.source e := by
  rw [toSourceBound_edge]
  exact data.toBondPathTable_recovered_source enumeration e

/-- The recovered physical atom label of the encoded target endpoint. -/
theorem toSourceBound_recovered_target (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    (sourceAtomEquiv data.graph enumeration).symm
        ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).target =
      data.target e := by
  rw [toSourceBound_edge]
  exact data.toBondPathTable_recovered_target enumeration e

/-! ### Preservation of the whole source -/

/-- Every source interaction is retained, in order, with its participants mapped by the shared
enumeration and its kind copied verbatim.  Nothing outside the documented subset is dropped. -/
@[simp] theorem toSourceBound_interactions (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    (data.toSourceBound enumeration edgeEquiv).source.molecule.interactions =
      data.graph.interactions.map (FiniteAtomInteractionHypergraph.encodeInteraction enumeration) := rfl

/-- The number of retained source interactions is exactly the independent source count. -/
@[simp] theorem toSourceBound_interactions_length (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    (data.toSourceBound enumeration edgeEquiv).source.molecule.interactions.length =
      data.graph.interactions.length := by
  rw [toSourceBound_interactions, List.length_map]

/-- The retained source interaction kinds are exactly the independent source kinds, including
`.other` authority codes and multicenter / ionic kinds. -/
@[simp] theorem toSourceBound_interactionKinds (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    (data.toSourceBound enumeration edgeEquiv).source.molecule.interactions.map
        SemanticInteraction.kind =
      data.graph.interactions.map (fun edge => edge.2) := by
  rw [toSourceBound_interactions, List.map_map]
  rfl

/-- The atom data stored at the shared enumeration index of `atom` is exactly the independent
source atom data at `atom`. -/
@[simp] theorem toSourceBound_atomAt (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (atom : V) :
    listGet? (data.toSourceBound enumeration edgeEquiv).source.molecule.atoms
        (enumeration atom).val = some (data.graph.atomData atom) := by
  simpa using data.graph.encode_atomAt enumeration (enumeration atom)

/-- The whole encoded source-bound record retains the encoded authoritative source. -/
@[simp] theorem toSourceBound_sourceProjection (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    SourceBoundEmbeddedBondPaths.sourceProjection
        (data.toSourceBound enumeration edgeEquiv) =
      data.graph.encodeAuthoritative enumeration := rfl

/-- Interactions outside the documented subset are never used as an edge source: they remain in
the source untouched. -/
theorem not_realized_of_not_documented (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    {index : Fin (data.graph.encode enumeration).interactions.length}
    (hindex : index ∉ (data.toBondPathTable enumeration).documented) :
    ¬ ∃ e : E, ((data.toBondPathTable enumeration).edge e).sourceInteraction = index :=
  BondPathTable.not_realized_of_not_documented _ hindex

/-! ### Non-dependent decoding projections

The source-bound record stores its conformation and its table at the encoded atom index, so the
Lean types of those fields depend on the record.  In order to compare two records without
dependent elimination, we read the physical data back through functions whose result types are
fixed: an atom label as `Option V`, an occurrence index as `ℕ`, and an arc as a continuous map
into real three-space.  These projections are used only to prove injectivity of the encoding. -/

/-- Total, non-dependent reading of an encoded atom index as a physical atom label.  The bound
check makes the function defined for every record, including records outside the image of the
independent construction. -/
noncomputable def indexToAtom? (enumeration : V ≃ Fin (Fintype.card V))
    {n : ℕ} (index : Fin n) : Option V :=
  if h : index.val < Fintype.card V then
    some (enumeration.symm ⟨index.val, h⟩)
  else none

/-- On the encoded index produced by the shared source equivalence, the bound-checked reading is
exactly the inverse image of the independent atom label. -/
theorem indexToAtom?_sourceAtomEquiv (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) (atom : V) :
    indexToAtom? enumeration (sourceAtomEquiv data.graph enumeration atom) = some atom := by
  unfold indexToAtom?
  have bound : (sourceAtomEquiv data.graph enumeration atom).val < Fintype.card V := by
    rw [sourceAtomEquiv_apply_val]
    exact (enumeration atom).isLt
  rw [dif_pos bound]
  congr 1
  rw [show (⟨(sourceAtomEquiv data.graph enumeration atom).val, bound⟩ :
      Fin (Fintype.card V)) = enumeration atom from Fin.ext rfl]
  exact enumeration.symm_apply_apply atom

/-- Total reading of a chosen physical edge as an index into the record's own edge table.  The
bound check makes the function defined even for records whose edge count is not `card E`. -/
noncomputable def recordEdgeIndex (edgeEquiv : E ≃ Fin (Fintype.card E))
    (record : SourceBoundEmbeddedBondPaths) (e : E) : Option (Fin record.edgeCount) :=
  if h : (edgeEquiv e).val < record.edgeCount then
    some ⟨(edgeEquiv e).val, h⟩
  else none

/-- On the constructed record the edge projection is the chosen edge equivalence. -/
theorem recordEdgeIndex_toSourceBound (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    recordEdgeIndex edgeEquiv (data.toSourceBound enumeration edgeEquiv) e =
      some (edgeEquiv e) := by
  unfold recordEdgeIndex
  have bound : (edgeEquiv e).val <
      (data.toSourceBound enumeration edgeEquiv).edgeCount := by
    rw [toSourceBound_edgeCount]
    exact (edgeEquiv e).isLt
  rw [dif_pos bound]
  congr 1

/-- The source interaction occurrence index recorded by the table edge of an independent edge. -/
noncomputable def recordOccurrence (edgeEquiv : E ≃ Fin (Fintype.card E))
    (record : SourceBoundEmbeddedBondPaths) (e : E) : Option ℕ :=
  (recordEdgeIndex edgeEquiv record e).map fun index =>
    (record.table.edge index).sourceInteraction.val

/-- The occurrence projection recovers the independent occurrence index exactly. -/
theorem recordOccurrence_toSourceBound (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    recordOccurrence edgeEquiv (data.toSourceBound enumeration edgeEquiv) e =
      some (data.interactionOccurrence e) := by
  unfold recordOccurrence
  rw [recordEdgeIndex_toSourceBound data enumeration edgeEquiv e]
  change some (((data.toSourceBound enumeration edgeEquiv).table.edge
    (edgeEquiv e)).sourceInteraction.val) = some (data.interactionOccurrence e)
  rw [toSourceBound_sourceInteraction_val]

/-- The physical source atom label recorded by the table edge of an independent edge. -/
noncomputable def recordSource? (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (record : SourceBoundEmbeddedBondPaths) (e : E) : Option V :=
  (recordEdgeIndex edgeEquiv record e).bind fun index =>
    indexToAtom? enumeration (record.table.edge index).source

/-- The source projection recovers the independent source atom label exactly. -/
theorem recordSource?_toSourceBound (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    recordSource? enumeration edgeEquiv (data.toSourceBound enumeration edgeEquiv) e =
      some (data.source e) := by
  unfold recordSource?
  rw [recordEdgeIndex_toSourceBound data enumeration edgeEquiv e]
  change indexToAtom? enumeration
      ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).source =
    some (data.source e)
  rw [toSourceBound_edge, sourceBondPath_source]
  exact indexToAtom?_sourceAtomEquiv data enumeration (data.source e)

/-- The physical target atom label recorded by the table edge of an independent edge. -/
noncomputable def recordTarget? (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (record : SourceBoundEmbeddedBondPaths) (e : E) : Option V :=
  (recordEdgeIndex edgeEquiv record e).bind fun index =>
    indexToAtom? enumeration (record.table.edge index).target

/-- The target projection recovers the independent target atom label exactly. -/
theorem recordTarget?_toSourceBound (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    recordTarget? enumeration edgeEquiv (data.toSourceBound enumeration edgeEquiv) e =
      some (data.target e) := by
  unfold recordTarget?
  rw [recordEdgeIndex_toSourceBound data enumeration edgeEquiv e]
  change indexToAtom? enumeration
      ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).target =
    some (data.target e)
  rw [toSourceBound_edge, sourceBondPath_target]
  exact indexToAtom?_sourceAtomEquiv data enumeration (data.target e)

/-- The continuous arc recorded by the table edge of an independent edge. -/
noncomputable def recordArc (edgeEquiv : E ≃ Fin (Fintype.card E))
    (record : SourceBoundEmbeddedBondPaths) (e : E) : Option (C(I, EmbeddedReal3)) :=
  (recordEdgeIndex edgeEquiv record e).map fun index => (record.table.edge index).arc

/-- The arc projection recovers the independent arc exactly. -/
theorem recordArc_toSourceBound (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) (e : E) :
    recordArc edgeEquiv (data.toSourceBound enumeration edgeEquiv) e =
      some (data.arc e) := by
  unfold recordArc
  rw [recordEdgeIndex_toSourceBound data enumeration edgeEquiv e]
  change some ((data.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv e)).arc =
    some (data.arc e)
  rw [toSourceBound_edge, sourceBondPath_arc]

/-- The physical real conformation read back from the encoded atom indices of a source-bound
record.  The bound check again makes the projection total and non-dependent. -/
noncomputable def recordConformation (enumeration : V ≃ Fin (Fintype.card V))
    (record : SourceBoundEmbeddedBondPaths) : MolecularConformation V :=
  if h : record.source.molecule.atomCount = Fintype.card V then
    MolecularConformation.reindex
      (enumeration.trans (finCongr h.symm)).symm record.conformation
  else
    fun _ => 0

/-- The conformation projection recovers the independent conformation exactly. -/
theorem recordConformation_toSourceBound (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    recordConformation enumeration (data.toSourceBound enumeration edgeEquiv) =
      data.conformation := by
  unfold recordConformation
  by_cases h : (data.toSourceBound enumeration edgeEquiv).source.molecule.atomCount =
      Fintype.card V
  · rw [dif_pos h]
    exact encodedConformation_reindex data enumeration
  · rw [dif_neg h]
    exact absurd
      (FiniteAtomInteractionHypergraph.encode_atomCount data.graph enumeration) h

/-! ### The encoding determines the whole independent data -/

/-- **Full-data injectivity of the construction.**  If two independent physical data records have
the same source-bound encoding under the same atom enumeration and the same edge equivalence, then
they are the same record.  This recovers the graph (atom data and ordered interaction list), the
real conformation, every occurrence index, every endpoint atom label, every arc, and (by proof
irrelevance) all physical validity proofs.

This is an injectivity statement, not a constructed total decoder.  The auxiliary non-dependent
observers used in the proof are total on source-bound records, but they recover the independent
data only on the image of `toSourceBound`. -/
theorem toSourceBound_injective (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E)) :
    Function.Injective (fun data : IndependentBondPathData V E =>
      data.toSourceBound enumeration edgeEquiv) := by
  intro data₁ data₂ h
  dsimp only at h
  -- The molecule of the encoded source is recovered from the source-bound record.
  have molecule : data₁.graph.encode enumeration = data₂.graph.encode enumeration := by
    have observed := congrArg
      (fun record : SourceBoundEmbeddedBondPaths => record.source.molecule) h
    simpa [toSourceBound] using observed
  have atoms : (data₁.graph.encode enumeration).atoms =
      (data₂.graph.encode enumeration).atoms :=
    congrArg SemanticMolecule.atoms molecule
  -- The ordered interaction list is recovered by the existing decoder.
  have interactions : data₁.graph.interactions = data₂.graph.interactions := by
    have decoded := congrArg
      (FiniteAtomInteractionHypergraph.decodeInteractions? enumeration) molecule
    rw [data₁.graph.decodeInteractions?_encode enumeration,
      data₂.graph.decodeInteractions?_encode enumeration] at decoded
    exact Option.some.inj decoded
  -- The atom data is recovered at every independent atom label.
  have atomData : data₁.graph.atomData = data₂.graph.atomData := by
    funext atom
    have first := data₁.graph.encode_atomAt enumeration (enumeration atom)
    have second := data₂.graph.encode_atomAt enumeration (enumeration atom)
    rw [← atoms] at second
    have equal := first.symm.trans second
    simpa using Option.some.inj equal
  have graphEq : data₁.graph = data₂.graph :=
    FiniteAtomInteractionHypergraph.ext_of_atomData_interactions atomData interactions
  -- The conformation is recovered through the non-dependent physical read-back.
  have conformationEq : data₁.conformation = data₂.conformation := by
    have observed := congrArg (recordConformation enumeration) h
    rw [recordConformation_toSourceBound data₁ enumeration edgeEquiv,
      recordConformation_toSourceBound data₂ enumeration edgeEquiv] at observed
    exact observed
  -- The occurrence index, both atom labels and the arc of every edge are recovered the same way.
  have occurrenceEq : data₁.interactionOccurrence = data₂.interactionOccurrence := by
    funext e
    have observed := congrArg (fun record => recordOccurrence edgeEquiv record e) h
    dsimp only at observed
    rw [recordOccurrence_toSourceBound data₁ enumeration edgeEquiv e,
      recordOccurrence_toSourceBound data₂ enumeration edgeEquiv e] at observed
    exact Option.some.inj observed
  have sourceEq : data₁.source = data₂.source := by
    funext e
    have observed := congrArg
      (fun record => recordSource? enumeration edgeEquiv record e) h
    dsimp only at observed
    rw [recordSource?_toSourceBound data₁ enumeration edgeEquiv e,
      recordSource?_toSourceBound data₂ enumeration edgeEquiv e] at observed
    exact Option.some.inj observed
  have targetEq : data₁.target = data₂.target := by
    funext e
    have observed := congrArg
      (fun record => recordTarget? enumeration edgeEquiv record e) h
    dsimp only at observed
    rw [recordTarget?_toSourceBound data₁ enumeration edgeEquiv e,
      recordTarget?_toSourceBound data₂ enumeration edgeEquiv e] at observed
    exact Option.some.inj observed
  have arcEq : data₁.arc = data₂.arc := by
    funext e
    have observed := congrArg (fun record => recordArc edgeEquiv record e) h
    dsimp only at observed
    rw [recordArc_toSourceBound data₁ enumeration edgeEquiv e,
      recordArc_toSourceBound data₂ enumeration edgeEquiv e] at observed
    exact Option.some.inj observed
  -- Recover the record field by field.
  obtain ⟨graph₁, conformation₁, occurrence₁, bound₁, injective₁, source₁, target₁,
    distinct₁, arc₁, participants₁, kind₁, sourceEndpoint₁, targetEndpoint₁, atomsInjective₁,
    arcsInjective₁, interiors₁, intersections₁⟩ := data₁
  obtain ⟨graph₂, conformation₂, occurrence₂, bound₂, injective₂, source₂, target₂,
    distinct₂, arc₂, participants₂, kind₂, sourceEndpoint₂, targetEndpoint₂, atomsInjective₂,
    arcsInjective₂, interiors₂, intersections₂⟩ := data₂
  dsimp only at graphEq conformationEq occurrenceEq sourceEq targetEq arcEq
  subst graphEq
  subst conformationEq
  subst occurrenceEq
  subst sourceEq
  subst targetEq
  subst arcEq
  rfl

/-- The encoded source-bound record determines the independent molecule exactly. -/
theorem toSourceBound_injective_molecule
    {data₁ data₂ : IndependentBondPathData V E}
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (equal : data₁.toSourceBound enumeration edgeEquiv =
      data₂.toSourceBound enumeration edgeEquiv) :
    data₁.graph.encode enumeration = data₂.graph.encode enumeration := by
  have observed := congrArg
    (fun record : SourceBoundEmbeddedBondPaths => record.source.molecule) equal
  simpa [toSourceBound] using observed

/-- The encoding agrees with the canonical `Fintype.equivFin` edge encoding of the existing
independent input form. -/
theorem toSourceBound_canonical (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    data.toSourceBound enumeration (Fintype.equivFin E) =
      (data.toEdgeIndexed enumeration).encode := by
  unfold toSourceBound EdgeIndexedSourceBoundInput.encode toEdgeIndexed
  rfl

/-! ### Independence of the atom enumeration -/

/-- Changing the enumeration only relabels encoded atom indices by the common permutation; the
physical conformation is unchanged. -/
theorem encodedConformation_relabel (data : IndependentBondPathData V E)
    (first second : V ≃ Fin (Fintype.card V)) :
    MolecularConformation.reindex (encodedIndexEquiv data.graph first second)
        (data.encodedConformation first) = data.encodedConformation second := by
  unfold encodedConformation
  rw [← MolecularConformation.reindex_trans
    (sourceAtomEquiv data.graph first) (encodedIndexEquiv data.graph first second)
    data.conformation]
  rw [sourceAtomEquiv_trans]

/-- The source-bound conformation under a change of enumeration is the common-permutation image of
the conformation under the first enumeration. -/
theorem toSourceBound_conformation_relabel (data : IndependentBondPathData V E)
    (first second : V ≃ Fin (Fintype.card V))
    (firstEdge secondEdge : E ≃ Fin (Fintype.card E)) :
    MolecularConformation.reindex (encodedIndexEquiv data.graph first second)
        (data.toSourceBound first firstEdge).conformation =
      (data.toSourceBound second secondEdge).conformation := by
  simpa [toSourceBound] using data.encodedConformation_relabel first second

/-- The arc of a physical edge is exactly the same under any two atom enumerations and any two
edge enumerations. -/
theorem toSourceBound_arc_independent (data : IndependentBondPathData V E)
    (first second : V ≃ Fin (Fintype.card V))
    (firstEdge secondEdge : E ≃ Fin (Fintype.card E)) (e : E) (t : I) :
    ((data.toSourceBound first firstEdge).table.edge (firstEdge e)).arc t =
      ((data.toSourceBound second secondEdge).table.edge (secondEdge e)).arc t := by
  rw [toSourceBound_arc, toSourceBound_arc]

/-- The source occurrence index of a physical edge is exactly the same under any two atom
enumerations and any two edge enumerations. -/
theorem toSourceBound_occurrence_independent (data : IndependentBondPathData V E)
    (first second : V ≃ Fin (Fintype.card V))
    (firstEdge secondEdge : E ≃ Fin (Fintype.card E)) (e : E) :
    ((data.toSourceBound first firstEdge).table.edge (firstEdge e)).sourceInteraction.val =
      ((data.toSourceBound second secondEdge).table.edge (secondEdge e)).sourceInteraction.val := by
  rw [toSourceBound_sourceInteraction_val, toSourceBound_sourceInteraction_val]

/-- The physical atom label recovered through the respective inverse enumerations is the same
under any atom enumeration. -/
theorem toSourceBound_recovered_source_independent (data : IndependentBondPathData V E)
    (first second : V ≃ Fin (Fintype.card V))
    (firstEdge secondEdge : E ≃ Fin (Fintype.card E)) (e : E) :
    (sourceAtomEquiv data.graph first).symm
        ((data.toSourceBound first firstEdge).table.edge (firstEdge e)).source =
      (sourceAtomEquiv data.graph second).symm
        ((data.toSourceBound second secondEdge).table.edge (secondEdge e)).source := by
  rw [toSourceBound_recovered_source, toSourceBound_recovered_source]

/-- The recovered target atom label is likewise enumeration-independent. -/
theorem toSourceBound_recovered_target_independent (data : IndependentBondPathData V E)
    (first second : V ≃ Fin (Fintype.card V))
    (firstEdge secondEdge : E ≃ Fin (Fintype.card E)) (e : E) :
    (sourceAtomEquiv data.graph first).symm
        ((data.toSourceBound first firstEdge).table.edge (firstEdge e)).target =
      (sourceAtomEquiv data.graph second).symm
        ((data.toSourceBound second secondEdge).table.edge (secondEdge e)).target := by
  rw [toSourceBound_recovered_target, toSourceBound_recovered_target]

/-- The source atom data of the encoded molecule is enumeration-independent as a function of the
independent atom label: under a change of enumeration it moves by the common permutation. -/
theorem toSourceBound_atomAt_relabel (data : IndependentBondPathData V E)
    (first second : V ≃ Fin (Fintype.card V))
    (firstEdge secondEdge : E ≃ Fin (Fintype.card E))
    (index : Fin (Fintype.card V)) :
    listGet? (data.toSourceBound second secondEdge).source.molecule.atoms index.val =
      listGet? (data.toSourceBound first firstEdge).source.molecule.atoms
        ((second.symm.trans first) index).val := by
  simpa [toSourceBound] using data.graph.encode_atomAt_relabel first second index

/-! ### Optional completeness of the documented subset -/

/-- Completeness of the documented subset for the default pair-bond specification.  This is an
explicit *optional* hypothesis, never derived from the construction: every encoded source
interaction that is a genuine selected binary pair bond is documented.  Interactions outside the
selected specification are not claimed to be realized and stay in the source untouched. -/
def CompleteForSourcePairBonds (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) : Prop :=
  ∀ index : Fin (data.graph.encode enumeration).interactions.length,
    IsGenuinePairBondAt (data.graph.encode enumeration) index →
      index ∈ data.documented enumeration

/-- Bundle the constructed table with an explicitly supplied completeness proof. -/
noncomputable def toCompleteBondPathTable (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (complete : data.CompleteForSourcePairBonds enumeration) :
    CompleteBondPathTable E (data.graph.encode enumeration)
      (data.encodedConformation enumeration) where
  table := data.toBondPathTable enumeration
  complete := complete

/-- Under the explicit completeness hypothesis, every selected binary source pair bond is
realized by exactly one physical edge. -/
theorem exact_coverage_of_genuine_pair_bond (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (complete : data.CompleteForSourcePairBonds enumeration)
    {index : Fin (data.graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (data.graph.encode enumeration) index) :
    ∃! e : E,
      ((data.toCompleteBondPathTable enumeration complete).table.edge e).sourceInteraction =
        index :=
  CompleteBondPathTable.exact_coverage_of_selected
    (data.toCompleteBondPathTable enumeration complete) genuine

/-- The number of documented occurrences equals the number of physical edges.  This is a
cardinality consequence of exact coverage, not an extra assumption. -/
theorem card_documented_eq_card_edges (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (data.toBondPathTable enumeration).documented.card = Fintype.card E :=
  BondPathTable.card_documented_eq_card_edges (data.toBondPathTable enumeration)

/-- Exact coverage in terms of the independent occurrence index: an occurrence is documented
exactly when some edge names it, and that edge is unique. -/
theorem documented_iff_exists_unique_occurrence (data : IndependentBondPathData V E)
    (enumeration : V ≃ Fin (Fintype.card V))
    (sourceIndex : Fin data.graph.interactions.length) :
    encodedIndex data.graph enumeration sourceIndex ∈ data.documented enumeration ↔
      ∃! e : E, data.interactionIndex e = sourceIndex := by
  constructor
  · intro member
    obtain ⟨e, he⟩ := (data.mem_documented_iff enumeration _).mp member
    have indexEqual : data.interactionIndex e = sourceIndex := by
      apply Fin.cast_injective
        (FiniteAtomInteractionHypergraph.encode_interactions_length data.graph enumeration).symm
      exact he
    refine ⟨e, indexEqual, ?_⟩
    intro f hf
    exact data.interactionOccurrence_injective
      (by simpa [interactionIndex] using hf.trans indexEqual.symm)
  · rintro ⟨e, he, -⟩
    exact (data.mem_documented_iff enumeration _).mpr ⟨e, by rw [he]⟩

end IndependentBondPathData

end TetraStereo.OneCenter
