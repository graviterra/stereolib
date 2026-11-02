import TetraStereo.OneCenter.OrganicStereoIndependentPathEncoding
import TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
import TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

namespace OrganicStereoEmbeddedMolecularGraphCoverage

open scoped unitInterval

open JointCoreEncoding
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoEmbeddedGraphRealization

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# Noncircular structural coverage from one global embedded graph realization

The existing independent path encoding (`OrganicStereoIndependentPathEncoding`) starts from an
`IndependentBondPathData` record that already carries a finite edge type, one occurrence per edge,
oriented endpoints, an arc per edge, and the geometric laws.  `OrganicStereoEmbeddedBondPaths`
makes the same assumptions at the level of the source-bound table.

This module removes those assumptions.  Its geometrical input is a single global continuous
injective map on the canonical realization of the selected-bond graph of an arbitrary finite
atom-labelled interaction hypergraph `graph`.  The finite edge type is *constructed* as the
subtype of selected binary interaction occurrences

`{index : Fin graph.interactions.length //
    (graph.interactions.get index).1.length = 2 ∧
      SemanticInteractionKind.isSelectedPairKind (graph.interactions.get index).2 = true}`.

Every selected binary occurrence is one edge, so parallel bonds between the same two atoms remain
distinct edges.  All other hyperedges (multicenter, ionic, metallic, hydrogen-bond, `.other`,
and selected-kind interactions with more than two participants) remain in the source graph
untouched; they are never realized as paths.

From the global embedding the module *derives* the geometric laws (atom injectivity, arc
injectivity, endpoint equations, interior avoidance and the common-endpoint intersection
condition), constructs the actual `IndependentBondPathData`, and proves completeness of the
selected path family for **every** atom enumeration by decoding each encoded selected pair bond
back to the source occurrence that gave rise to it.  Completeness is therefore a theorem here,
not an optional hypothesis as in the upstream independent encoding.

The result is composed with the actual `OrganicMolecularEvidence` assembly and its canonical
finite transport, so the generated evidence (with the generated path family), the assembled
source graph and conformation, and every parametrized arc are recovered exactly.

Scope boundaries: this is a representation and coverage layer.  It asserts no chemical
admissibility, no electron wavefunction, no knot/link classification and no spatial realization
of unselected hyperedges.
-/

/-! ## The canonical selected binary occurrence type -/

/-- One selected binary interaction occurrence of the source graph.

The subtype is over the *occurrence index*, not over an unordered pair of atoms: two documented
binary interactions with the same two participants are two distinct elements.  The two fields are
exactly the structural conditions used by the accepted pair-bond specification: length two and a
selected kind.  Distinctness of the two endpoints is *derived* below from the graph's
`participants_nodup` field and is not part of the subtype. -/
def SelectedBondIndex (graph : FiniteAtomInteractionHypergraph V) : Type :=
  { index : Fin graph.interactions.length //
    (graph.interactions.get index).1.length = 2 ∧
      SemanticInteractionKind.isSelectedPairKind (graph.interactions.get index).2 = true }

/-- The selected occurrence subtype of a finite index type is finite. -/
instance selectedBondIndexFintype (graph : FiniteAtomInteractionHypergraph V) :
    Fintype (SelectedBondIndex graph) := by
  classical
  unfold SelectedBondIndex
  infer_instance

/-- The underlying source interaction occurrence index. -/
def selectedInteractionIndex (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) : Fin graph.interactions.length :=
  edge.1

/-- The natural-number occurrence index used by `IndependentBondPathData`. -/
def selectedOccurrence (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) : ℕ :=
  edge.1.val

@[simp] theorem selectedOccurrence_lt (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    selectedOccurrence graph edge < graph.interactions.length :=
  edge.1.isLt

/-- Different selected occurrences remain different edges even when they share both endpoints. -/
theorem selectedOccurrence_injective (graph : FiniteAtomInteractionHypergraph V) :
    Function.Injective (selectedOccurrence graph) := by
  intro first second equal
  apply Subtype.ext
  exact Fin.ext equal

/-- The first participant, read from position `0` of the occurrence participant list. -/
def selectedSource (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) : V :=
  (graph.interactions.get edge.1).1.get ⟨0, by rw [edge.2.1]; decide⟩

/-- The second participant, read from position `1` of the occurrence participant list. -/
def selectedTarget (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) : V :=
  (graph.interactions.get edge.1).1.get ⟨1, by rw [edge.2.1]; decide⟩

/-- The participant list of a selected occurrence is exactly the ordered pair of its two
positional endpoints.  This is derived from the length-two condition, not assumed. -/
theorem selectedParticipants (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    (graph.interactions.get edge.1).1 = [selectedSource graph edge, selectedTarget graph edge] := by
  have h := List.eq_getElem_of_length_eq_two (graph.interactions.get edge.1).1 edge.2.1
  simpa [selectedSource, selectedTarget] using h

/-- The two endpoints of a selected occurrence are distinct.  This follows from the source
graph's independent `participants_nodup` field together with the positional description. -/
theorem selectedSource_ne_target (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    selectedSource graph edge ≠ selectedTarget graph edge := by
  intro equal
  have nodup : (graph.interactions.get edge.1).1.Nodup :=
    graph.participants_nodup _ (List.get_mem _ _)
  rw [selectedParticipants graph edge, equal] at nodup
  simpa using nodup

/-- The selected kind condition, read structurally from the subtype. -/
theorem selectedKind (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    SemanticInteractionKind.isSelectedPairKind (graph.interactions.get edge.1).2 = true :=
  edge.2.2

/-- The length-two condition, read structurally from the subtype. -/
theorem selectedLength (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    (graph.interactions.get edge.1).1.length = 2 :=
  edge.2.1

/-! ## Decoding an encoded selected pair bond to its source occurrence

The completeness proof below is noncircular: no target path table and no geometric law is used.
It takes an encoded interaction index that the accepted specification certifies as a genuine
selected binary pair bond, decodes it through the shared atom enumeration back to the source
occurrence list, and shows that this occurrence is one of the selected subtype elements. -/

/-- Inverse of `JointCoreEncoding.encodedIndex` on interaction indices. -/
def sourceIndexOf (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.encode enumeration).interactions.length) :
    Fin graph.interactions.length :=
  Fin.cast (FiniteAtomInteractionHypergraph.encode_interactions_length graph enumeration) index

/-- The inverse index really maps back to the given encoded index. -/
theorem encodedIndex_sourceIndexOf (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.encode enumeration).interactions.length) :
    encodedIndex graph enumeration (sourceIndexOf graph enumeration index) = index := by
  apply Fin.ext
  rfl

/-- Participant lists are decoded exactly: the bound-checked inverse enumeration applied to the
two encoded participants returns the two source atom labels. -/
theorem decodeParticipants?_pair (enumeration : V ≃ Fin (Fintype.card V))
    {source target : ℕ} (sourceBound : source < Fintype.card V)
    (targetBound : target < Fintype.card V) (kind : SemanticInteractionKind) :
    FiniteAtomInteractionHypergraph.decodeParticipants? enumeration
        { participants := [source, target], kind := kind } =
      some [enumeration.symm ⟨source, sourceBound⟩,
        enumeration.symm ⟨target, targetBound⟩] := by
  unfold FiniteAtomInteractionHypergraph.decodeParticipants?
  simp [FiniteAtomInteractionHypergraph.decodeIndex?, sourceBound, targetBound]

/-- **Structural completeness of the selected occurrence subtype.**

Every interaction of the encoded molecule that the accepted specification certifies as a genuine
selected binary pair bond is the `encodedIndex` image of a selected occurrence of the actual
source graph.  The proof decodes the encoded participant pair back to source atom labels and uses
the source graph's own `participants_nodup` to certify the length-two occurrence. -/
theorem exists_selected_of_genuine (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {index : Fin (graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (graph.encode enumeration) index) :
    ∃ edge : SelectedBondIndex graph,
      encodedIndex graph enumeration edge.1 = index := by
  let occurrence := sourceIndexOf graph enumeration index
  have hoccurrence : encodedIndex graph enumeration occurrence = index :=
    encodedIndex_sourceIndexOf graph enumeration index
  have lookup : (graph.encode enumeration).interactions.get index =
      FiniteAtomInteractionHypergraph.encodeInteraction enumeration
        (graph.interactions.get occurrence) := by
    rw [← hoccurrence]
    exact FiniteAtomInteractionHypergraph.encode_get graph enumeration occurrence
  have kindSelected :
      SemanticInteractionKind.isSelectedPairKind (graph.interactions.get occurrence).2 = true := by
    have selected := genuine.1
    rw [lookup] at selected
    simpa [FiniteAtomInteractionHypergraph.encodeInteraction] using selected
  obtain ⟨sourceIndex, targetIndex, sourceBound, targetBound, distinct, participants⟩ :=
    genuine.2
  have sourceBound' : sourceIndex < Fintype.card V := by
    simpa [FiniteAtomInteractionHypergraph.encode_atomCount] using sourceBound
  have targetBound' : targetIndex < Fintype.card V := by
    simpa [FiniteAtomInteractionHypergraph.encode_atomCount] using targetBound
  let sourceAtom : V := enumeration.symm ⟨sourceIndex, sourceBound'⟩
  let targetAtom : V := enumeration.symm ⟨targetIndex, targetBound'⟩
  have decodedPair :
      FiniteAtomInteractionHypergraph.decodeParticipants? enumeration
          ((graph.encode enumeration).interactions.get index) = some [sourceAtom, targetAtom] := by
    unfold FiniteAtomInteractionHypergraph.decodeParticipants?
    rw [participants]
    exact decodeParticipants?_pair enumeration sourceBound' targetBound'
      (graph.encode enumeration).interactions[index].kind
  have decodedSource :
      FiniteAtomInteractionHypergraph.decodeParticipants? enumeration
          ((graph.encode enumeration).interactions.get index) =
        some (graph.interactions.get occurrence).1 := by
    rw [lookup]
    exact FiniteAtomInteractionHypergraph.decodeParticipants?_encodeInteraction enumeration
      (graph.interactions.get occurrence)
  have participantsExact : (graph.interactions.get occurrence).1 = [sourceAtom, targetAtom] :=
    Option.some.inj (decodedSource.symm.trans decodedPair)
  have lengthTwo : (graph.interactions.get occurrence).1.length = 2 := by
    rw [participantsExact]
    rfl
  refine ⟨⟨occurrence, lengthTwo, kindSelected⟩, ?_⟩
  exact hoccurrence

/-! ## Geometric data derived from a global embedding (internal bridge)

The next structure is an *internal* intermediate used only to organize the construction.  It is
never an input of a public theorem: the public theorem below obtains all of its fields from one
global continuous injective map on the canonical selected-bond realization.  It records exactly
the obligations that the realization quotient and the injectivity of the global map discharge. -/

/-- The geometric laws on the canonical selected-bond graph.  This is internal: the public
construction derives an element of this structure from the global embedding. -/
structure SelectedGeometry (graph : FiniteAtomInteractionHypergraph V) where
  /-- Real position of every atom. -/
  conformation : MolecularConformation V
  /-- The parametric arc of every selected occurrence. -/
  arc : SelectedBondIndex graph → C(I, EmbeddedReal3)
  /-- Arc start points coincide with the oriented source atom positions. -/
  source_endpoint : ∀ edge, arc edge 0 = conformation (selectedSource graph edge)
  /-- Arc end points coincide with the oriented target atom positions. -/
  target_endpoint : ∀ edge, arc edge 1 = conformation (selectedTarget graph edge)
  /-- Distinct atoms occupy distinct points. -/
  atom_injective : Function.Injective conformation
  /-- Every arc is injective on the unit interval. -/
  arc_injective : ∀ edge, Function.Injective (arc edge)
  /-- Arc interiors avoid every atom position. -/
  interior_avoids_atoms :
    ∀ edge (t : I), t ≠ 0 → t ≠ 1 → ∀ atom, arc edge t ≠ conformation atom
  /-- Distinct arcs meet only at a common endpoint atom. -/
  intersects_only_at_common_endpoints :
    ∀ edge other (t s : I), edge ≠ other → arc edge t = arc other s →
      ∃ atom : V,
        sourceEndpointAt? (selectedSource graph) (selectedTarget graph) edge t = some atom ∧
          sourceEndpointAt? (selectedSource graph) (selectedTarget graph) other s = some atom

namespace SelectedGeometry

variable {graph : FiniteAtomInteractionHypergraph V}

/-- Construct the actual independent bond-path data from the derived geometric laws.  The graph,
the occurrence index, the oriented endpoints and the participant/kind compatibility are all
structural; the geometric laws are supplied only by the derived bridge fields. -/
def toIndependentBondPathData (geometry : SelectedGeometry graph) :
    IndependentBondPathData V (SelectedBondIndex graph) where
  graph := graph
  conformation := geometry.conformation
  interactionOccurrence := selectedOccurrence graph
  interactionOccurrence_lt := selectedOccurrence_lt graph
  interactionOccurrence_injective := selectedOccurrence_injective graph
  source := selectedSource graph
  target := selectedTarget graph
  source_ne_target := selectedSource_ne_target graph
  arc := geometry.arc
  participants_exact := selectedParticipants graph
  kind_selected := selectedKind graph
  source_endpoint := geometry.source_endpoint
  target_endpoint := geometry.target_endpoint
  atom_injective := geometry.atom_injective
  arc_injective := geometry.arc_injective
  interior_avoids_atoms := geometry.interior_avoids_atoms
  intersects_only_at_common_endpoints := geometry.intersects_only_at_common_endpoints

@[simp] theorem toIndependentBondPathData_graph (geometry : SelectedGeometry graph) :
    geometry.toIndependentBondPathData.graph = graph := rfl

@[simp] theorem toIndependentBondPathData_conformation (geometry : SelectedGeometry graph) :
    geometry.toIndependentBondPathData.conformation = geometry.conformation := rfl

@[simp] theorem toIndependentBondPathData_occurrence (geometry : SelectedGeometry graph)
    (edge : SelectedBondIndex graph) :
    geometry.toIndependentBondPathData.interactionOccurrence edge =
      selectedOccurrence graph edge := rfl

@[simp] theorem toIndependentBondPathData_source (geometry : SelectedGeometry graph)
    (edge : SelectedBondIndex graph) :
    geometry.toIndependentBondPathData.source edge = selectedSource graph edge := rfl

@[simp] theorem toIndependentBondPathData_target (geometry : SelectedGeometry graph)
    (edge : SelectedBondIndex graph) :
    geometry.toIndependentBondPathData.target edge = selectedTarget graph edge := rfl

@[simp] theorem toIndependentBondPathData_arc (geometry : SelectedGeometry graph)
    (edge : SelectedBondIndex graph) :
    geometry.toIndependentBondPathData.arc edge = geometry.arc edge := rfl

/-- **Derived completeness.**  For *every* atom enumeration, every selected binary pair bond of
the encoded source graph is documented by the constructed path data.  This removes the optional
completeness hypothesis of the upstream independent encoding. -/
theorem completeForSourcePairBonds (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    geometry.toIndependentBondPathData.CompleteForSourcePairBonds enumeration := by
  unfold IndependentBondPathData.CompleteForSourcePairBonds
  intro index genuine
  obtain ⟨edge, image⟩ := exists_selected_of_genuine graph enumeration genuine
  unfold IndependentBondPathData.documented
  refine Finset.mem_image.mpr ⟨edge, Finset.mem_univ _, ?_⟩
  change encodedIndex graph enumeration
      (IndependentBondPathData.interactionIndex geometry.toIndependentBondPathData edge) = index
  have indexEq : IndependentBondPathData.interactionIndex geometry.toIndependentBondPathData edge =
      edge.1 := rfl
  rw [indexEq]
  exact image

/-- The documented encoded occurrences are exactly the `encodedIndex` images of the selected
source occurrences.  This is definitional for the constructed data and exhibits the coverage
family without any target table. -/
theorem documented_eq_selected_image (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    geometry.toIndependentBondPathData.documented enumeration =
      Finset.univ.image (fun edge : SelectedBondIndex graph =>
        encodedIndex graph enumeration edge.1) := rfl

/-- An encoded source occurrence is documented exactly when it is a selected occurrence.  This is
the occurrence-level form of the derived completeness theorem. -/
theorem mem_documented_iff_selected (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin graph.interactions.length) :
    encodedIndex graph enumeration index ∈
        geometry.toIndependentBondPathData.documented enumeration ↔
      ∃ edge : SelectedBondIndex graph, edge.1 = index := by
  rw [documented_eq_selected_image]
  constructor
  · intro member
    obtain ⟨edge, -, image⟩ := Finset.mem_image.mp member
    refine ⟨edge, ?_⟩
    apply Fin.ext
    simpa [encodedIndex] using congrArg Fin.val image
  · rintro ⟨edge, rfl⟩
    exact Finset.mem_image.mpr ⟨edge, Finset.mem_univ _, rfl⟩

/-- Every selected source occurrence is documented by the constructed data. -/
theorem selected_mem_documented (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V)) (edge : SelectedBondIndex graph) :
    encodedIndex graph enumeration edge.1 ∈
      geometry.toIndependentBondPathData.documented enumeration :=
  Finset.mem_image.mpr ⟨edge, Finset.mem_univ _, rfl⟩

/-- The encoded occurrence of a selected edge is realized by exactly one selected occurrence:
the occurrence subtype itself.  This is distinctness of occurrences, including parallel bonds
between the same two atoms. -/
theorem selected_occurrence_unique (_geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V)) (edge : SelectedBondIndex graph) :
    ∀ other : SelectedBondIndex graph,
      encodedIndex graph enumeration other.1 = encodedIndex graph enumeration edge.1 →
        other = edge := by
  intro other image
  apply Subtype.ext
  apply Fin.ext
  simpa [encodedIndex] using congrArg Fin.val image

/-- The complete bond-path table constructed from the derived data, with completeness proved
rather than assumed. -/
def toCompleteBondPathTable (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    CompleteBondPathTable (SelectedBondIndex graph) (graph.encode enumeration)
      (geometry.toIndependentBondPathData.encodedConformation enumeration) :=
  geometry.toIndependentBondPathData.toCompleteBondPathTable enumeration
    (geometry.completeForSourcePairBonds enumeration)

/-- Exact unique coverage of every genuine selected source pair bond, by the constructed complete
table. -/
theorem exact_coverage (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    {index : Fin (graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (graph.encode enumeration) index) :
    ∃! edge : SelectedBondIndex graph,
      (((geometry.toCompleteBondPathTable enumeration).table.edge edge).sourceInteraction) =
        index :=
  CompleteBondPathTable.exact_coverage_of_selected
    (geometry.toCompleteBondPathTable enumeration) genuine

/-- The number of selected occurrences equals the number of documented encoded occurrences; this
is a cardinality consequence of unique coverage, not a separate assumption. -/
theorem card_documented_eq_card_selected (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (geometry.toIndependentBondPathData.toBondPathTable enumeration).documented.card =
      Fintype.card (SelectedBondIndex graph) :=
  IndependentBondPathData.card_documented_eq_card_edges
    geometry.toIndependentBondPathData enumeration

/-! ### The accepted source-bound encoding of the generated data -/

/-- The accepted `SourceBoundEmbeddedBondPaths` record of the generated independent data, at an
explicit edge equivalence.  This is the actual table form used by the rest of the repository. -/
def toSourceBound (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    SourceBoundEmbeddedBondPaths :=
  geometry.toIndependentBondPathData.toSourceBound enumeration edgeEquiv

@[simp] theorem toSourceBound_source (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    (geometry.toSourceBound enumeration edgeEquiv).source =
      graph.encodeAuthoritative enumeration := rfl

/-- The accepted source-bound record retains exactly the encoded source molecule. -/
@[simp] theorem toSourceBound_molecule (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    (geometry.toSourceBound enumeration edgeEquiv).source.molecule =
      graph.encode enumeration := rfl

/-- The accepted source-bound record retains the whole interaction list, in order, with the
shared atom enumeration applied and the kind copied verbatim.  Unselected hyperedges are never
dropped. -/
@[simp] theorem toSourceBound_interactions (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    (geometry.toSourceBound enumeration edgeEquiv).source.molecule.interactions =
      graph.interactions.map
        (FiniteAtomInteractionHypergraph.encodeInteraction enumeration) := rfl

/-- Exact recovery of the oriented source occurrence index. -/
@[simp] theorem toSourceBound_occurrence (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    ((geometry.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv edge)).sourceInteraction.val =
      selectedOccurrence graph edge := by
  simpa only [SelectedGeometry.toSourceBound] using
    IndependentBondPathData.toSourceBound_sourceInteraction_val
      geometry.toIndependentBondPathData enumeration edgeEquiv edge

/-- Exact recovery of the encoded oriented source atom index. -/
@[simp] theorem toSourceBound_source_val (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    ((geometry.toSourceBound enumeration edgeEquiv).table.edge
      (edgeEquiv edge)).source.val = (enumeration (selectedSource graph edge)).val := by
  simpa only [SelectedGeometry.toSourceBound] using
    IndependentBondPathData.toSourceBound_source_val
      geometry.toIndependentBondPathData enumeration edgeEquiv edge

/-- Exact recovery of the encoded oriented target atom index. -/
@[simp] theorem toSourceBound_target_val (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    ((geometry.toSourceBound enumeration edgeEquiv).table.edge
      (edgeEquiv edge)).target.val = (enumeration (selectedTarget graph edge)).val := by
  simpa only [SelectedGeometry.toSourceBound] using
    IndependentBondPathData.toSourceBound_target_val
      geometry.toIndependentBondPathData enumeration edgeEquiv edge

/-- Recovery of the physical source atom label: applying the inverse common atom equivalence to
the encoded endpoint returns exactly the positional source participant. -/
theorem toSourceBound_recovered_source (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    (sourceAtomEquiv graph enumeration).symm
        ((geometry.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv edge)).source =
      selectedSource graph edge := by
  simpa only [SelectedGeometry.toSourceBound] using
    IndependentBondPathData.toSourceBound_recovered_source
      geometry.toIndependentBondPathData enumeration edgeEquiv edge

/-- Recovery of the physical target atom label. -/
theorem toSourceBound_recovered_target (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    (sourceAtomEquiv graph enumeration).symm
        ((geometry.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv edge)).target =
      selectedTarget graph edge := by
  simpa only [SelectedGeometry.toSourceBound] using
    IndependentBondPathData.toSourceBound_recovered_target
      geometry.toIndependentBondPathData enumeration edgeEquiv edge

/-- Exact recovery of every parametrized arc value. -/
@[simp] theorem toSourceBound_arc (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) (t : I) :
    ((geometry.toSourceBound enumeration edgeEquiv).table.edge (edgeEquiv edge)).arc t =
      geometry.arc edge t := by
  simpa only [SelectedGeometry.toSourceBound] using
    IndependentBondPathData.toSourceBound_arc
      geometry.toIndependentBondPathData enumeration edgeEquiv edge t

end SelectedGeometry

/-! ## Exact coverage in the accepted source-bound form -/

/-- Exact unique coverage of every genuine selected source pair bond in the accepted
`SourceBoundEmbeddedBondPaths` record: the realizing edge is unique. -/
theorem sourceBound_exact_coverage {graph : FiniteAtomInteractionHypergraph V}
    (geometry : SelectedGeometry graph)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    {index : Fin (graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (graph.encode enumeration) index) :
    ∃! edge : SelectedBondIndex graph,
      ((geometry.toSourceBound enumeration edgeEquiv).table.edge
        (edgeEquiv edge)).sourceInteraction = index := by
  obtain ⟨edge, covered, unique⟩ := geometry.exact_coverage enumeration genuine
  refine ⟨edge, ?_, ?_⟩
  · simpa only [SelectedGeometry.toSourceBound, IndependentBondPathData.toSourceBound_edge]
      using covered
  · intro other hother
    have hother' :
        ((geometry.toCompleteBondPathTable enumeration).table.edge other).sourceInteraction =
          index := by
      simpa only [SelectedGeometry.toSourceBound, IndependentBondPathData.toSourceBound_edge]
        using hother
    exact unique other hother'

/-! ## From one global continuous injective realization map

The geometry input of this section is exactly one global map on the canonical realization of the
selected-bond graph of the source hypergraph.  No arc family, endpoint law, injectivity law,
coverage table or target path table is an input: the adapter below derives every `SelectedGeometry`
field from the realization module's global embedding theorem, and `selectedDataOfEmbedding` turns
those derived laws into the actual `IndependentBondPathData`. -/

/-- Package a raw global continuous injective realization map as the realization module's
`EmbeddedGraph`.  This is the literal input shape of the decisive theorem: one map and one proof
of injectivity. -/
def embeddedGraphOfMap (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map) :
    EmbeddedGraph (selectedSource graph) (selectedTarget graph) where
  map := map
  injective := injective

@[simp] theorem embeddedGraphOfMap_map (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map) :
    (embeddedGraphOfMap graph map injective).map = map := rfl

@[simp] theorem embeddedGraphOfMap_conformation (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map) :
    (embeddedGraphOfMap graph map injective).conformation =
      fun atom => map (Realization.vertex atom) := rfl

@[simp] theorem embeddedGraphOfMap_arc (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map) (edge : SelectedBondIndex graph) :
    (embeddedGraphOfMap graph map injective).arc edge =
      map.comp (edgeMap (selectedSource graph) (selectedTarget graph) edge) := rfl

/-- **Geometry adapter.**  Every geometric obligation of `SelectedGeometry` is discharged by the
global embedding theorem of the realization module, not assumed.  Arc injectivity uses the
structurally derived distinctness of the two endpoints; the intersection law is used verbatim
because both formulations share `sourceEndpointAt?` at the same endpoint maps. -/
def selectedGeometryOfEmbedding (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    SelectedGeometry graph where
  conformation := G.conformation
  arc := G.arc
  source_endpoint := fun edge => G.arc_zero edge
  target_endpoint := fun edge => G.arc_one edge
  atom_injective := G.atom_injective
  arc_injective := fun edge =>
    G.arc_injective edge (selectedSource_ne_target graph edge)
  interior_avoids_atoms := fun edge t ht0 ht1 atom =>
    G.interior_avoids_atoms edge t ht0 ht1 atom
  intersects_only_at_common_endpoints := fun edge other t s hne h =>
    G.intersects_only_at_common_endpoints edge other t s hne h

@[simp] theorem selectedGeometryOfEmbedding_conformation
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    (selectedGeometryOfEmbedding graph G).conformation = G.conformation := rfl

@[simp] theorem selectedGeometryOfEmbedding_arc
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedGeometryOfEmbedding graph G).arc edge = G.arc edge := rfl

/-- Geometry of a raw global map, with no structure wrapper at the call site. -/
def selectedGeometryOfMap (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map) :
    SelectedGeometry graph :=
  selectedGeometryOfEmbedding graph (embeddedGraphOfMap graph map injective)

/-- The actual independent bond-path data constructed from one global embedding.  The edge type,
occurrence index, oriented endpoints, participants and kind are structural; the geometry is the
embedding's own. -/
def selectedDataOfEmbedding (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    IndependentBondPathData V (SelectedBondIndex graph) :=
  (selectedGeometryOfEmbedding graph G).toIndependentBondPathData

/-- The same constructed data from a raw global map. -/
def selectedDataOfMap (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map) :
    IndependentBondPathData V (SelectedBondIndex graph) :=
  (selectedGeometryOfMap graph map injective).toIndependentBondPathData

@[simp] theorem selectedDataOfEmbedding_graph (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    (selectedDataOfEmbedding graph G).graph = graph := rfl

@[simp] theorem selectedDataOfEmbedding_conformation
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    (selectedDataOfEmbedding graph G).conformation = G.conformation := rfl

@[simp] theorem selectedDataOfEmbedding_arc (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedDataOfEmbedding graph G).arc edge = G.arc edge := rfl

@[simp] theorem selectedDataOfEmbedding_source (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedDataOfEmbedding graph G).source edge = selectedSource graph edge := rfl

@[simp] theorem selectedDataOfEmbedding_target (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedDataOfEmbedding graph G).target edge = selectedTarget graph edge := rfl

@[simp] theorem selectedDataOfEmbedding_occurrence (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedDataOfEmbedding graph G).interactionOccurrence edge =
      selectedOccurrence graph edge := rfl

@[simp] theorem selectedDataOfEmbedding_source_endpoint
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedDataOfEmbedding graph G).arc edge 0 =
      (selectedDataOfEmbedding graph G).conformation
        ((selectedDataOfEmbedding graph G).source edge) :=
  (selectedDataOfEmbedding graph G).source_endpoint edge

@[simp] theorem selectedDataOfEmbedding_target_endpoint
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedDataOfEmbedding graph G).arc edge 1 =
      (selectedDataOfEmbedding graph G).conformation
        ((selectedDataOfEmbedding graph G).target edge) :=
  (selectedDataOfEmbedding graph G).target_endpoint edge

/-- Structural index bound of every generated occurrence, read from the constructed data. -/
@[simp] theorem selectedDataOfEmbedding_occurrence_lt
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedDataOfEmbedding graph G).interactionOccurrence edge <
      (selectedDataOfEmbedding graph G).graph.interactions.length :=
  (selectedDataOfEmbedding graph G).interactionOccurrence_lt edge

/-- Structural injectivity of occurrences: parallel bonds between the same atoms remain distinct. -/
theorem selectedDataOfEmbedding_occurrence_injective
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    Function.Injective (selectedDataOfEmbedding graph G).interactionOccurrence :=
  (selectedDataOfEmbedding graph G).interactionOccurrence_injective

/-- Structural endpoint distinctness, read from the constructed data. -/
theorem selectedDataOfEmbedding_source_ne_target
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    (selectedDataOfEmbedding graph G).source edge ≠
      (selectedDataOfEmbedding graph G).target edge :=
  (selectedDataOfEmbedding graph G).source_ne_target edge

/-- Structural participant compatibility at the data's own occurrence index. -/
theorem selectedDataOfEmbedding_participants_exact
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    ((selectedDataOfEmbedding graph G).graph.interactions.get
        ((selectedDataOfEmbedding graph G).interactionIndex edge)).1 =
      [(selectedDataOfEmbedding graph G).source edge,
        (selectedDataOfEmbedding graph G).target edge] :=
  (selectedDataOfEmbedding graph G).participants_exact edge

/-- Structural kind compatibility at the data's own occurrence index. -/
theorem selectedDataOfEmbedding_kind_selected
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (edge : SelectedBondIndex graph) :
    SemanticInteractionKind.isSelectedPairKind
      ((selectedDataOfEmbedding graph G).graph.interactions.get
        ((selectedDataOfEmbedding graph G).interactionIndex edge)).2 = true :=
  (selectedDataOfEmbedding graph G).kind_selected edge

/-- **Derived completeness from one global embedding.**  For every atom enumeration, the
constructed data documents every selected binary pair bond of the encoded source graph.  The
proof is the structural occurrence-decoding argument; no table or geometry is reused. -/
theorem selectedDataOfEmbedding_completeForSourcePairBonds
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (selectedDataOfEmbedding graph G).CompleteForSourcePairBonds enumeration :=
  (selectedGeometryOfEmbedding graph G).completeForSourcePairBonds enumeration

/-- The raw-map form of derived completeness. -/
theorem selectedDataOfMap_completeForSourcePairBonds
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (selectedDataOfMap graph map injective).CompleteForSourcePairBonds enumeration :=
  selectedDataOfEmbedding_completeForSourcePairBonds graph
    (embeddedGraphOfMap graph map injective) enumeration

/-- **Decisive input-domain theorem.**  From an arbitrary finite atom interaction hypergraph and
ONE global continuous injective map on the canonical realization of its selected-bond graph, there
exists the actual independent bond-path data, with exactly the structurally constructed graph,
occurrence and endpoints, exactly the embedding's vertex positions and parametrized arcs, and
derived completeness for the given atom enumeration.  No target path table, local geometric law,
coverage hypothesis, ring-length bound or component count restriction is an input. -/
theorem exists_complete_selected_path_data_of_global_embedding
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    ∃ data : IndependentBondPathData V (SelectedBondIndex graph),
      data.graph = graph ∧
      data.conformation = (embeddedGraphOfMap graph map injective).conformation ∧
      (∀ edge, data.arc edge = (embeddedGraphOfMap graph map injective).arc edge) ∧
      (∀ edge, data.source edge = selectedSource graph edge) ∧
      (∀ edge, data.target edge = selectedTarget graph edge) ∧
      (∀ edge, data.interactionOccurrence edge = selectedOccurrence graph edge) ∧
      data.CompleteForSourcePairBonds enumeration := by
  refine ⟨selectedDataOfMap graph map injective, rfl, rfl, ?_, ?_, ?_, ?_,
    selectedDataOfMap_completeForSourcePairBonds graph map injective enumeration⟩
  · intro edge
    rfl
  · intro edge
    rfl
  · intro edge
    rfl
  · intro edge
    rfl

/-- Exact unique coverage of every genuine selected source pair bond by the complete table
constructed from one global embedding. -/
theorem selectedDataOfEmbedding_exact_coverage
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    {index : Fin (graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (graph.encode enumeration) index) :
    ∃! edge : SelectedBondIndex graph,
      (((selectedGeometryOfEmbedding graph G).toCompleteBondPathTable enumeration).table.edge
        edge).sourceInteraction = index :=
  (selectedGeometryOfEmbedding graph G).exact_coverage enumeration genuine

/-- The raw-map form of exact unique coverage. -/
theorem selectedDataOfMap_exact_coverage
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map)
    (enumeration : V ≃ Fin (Fintype.card V))
    {index : Fin (graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (graph.encode enumeration) index) :
    ∃! edge : SelectedBondIndex graph,
      (((selectedGeometryOfMap graph map injective).toCompleteBondPathTable enumeration).table.edge
        edge).sourceInteraction = index :=
  (selectedGeometryOfMap graph map injective).exact_coverage enumeration genuine

/-! ### The accepted source-bound encoding of the embedding-constructed data -/

/-- The accepted `SourceBoundEmbeddedBondPaths` record built directly from one global embedding. -/
def selectedSourceBoundOfEmbedding (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    SourceBoundEmbeddedBondPaths :=
  (selectedGeometryOfEmbedding graph G).toSourceBound enumeration edgeEquiv

/-- The source-bound record retains the whole encoded authoritative source. -/
@[simp] theorem selectedSourceBoundOfEmbedding_source
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    (selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).source =
      graph.encodeAuthoritative enumeration := rfl

/-- The source-bound record retains the exact encoded source molecule. -/
@[simp] theorem selectedSourceBoundOfEmbedding_molecule
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    (selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).source.molecule =
      graph.encode enumeration := rfl

/-- The source-bound record retains every source interaction in order; unselected hyperedges are
not dropped. -/
@[simp] theorem selectedSourceBoundOfEmbedding_interactions
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    (selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).source.molecule.interactions =
      graph.interactions.map
        (FiniteAtomInteractionHypergraph.encodeInteraction enumeration) := rfl

/-- Exact recovery of the oriented source occurrence index from the source-bound table. -/
@[simp] theorem selectedSourceBoundOfEmbedding_occurrence
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
      (edgeEquiv edge)).sourceInteraction.val = selectedOccurrence graph edge :=
  SelectedGeometry.toSourceBound_occurrence (selectedGeometryOfEmbedding graph G)
    enumeration edgeEquiv edge

/-- Exact recovery of the encoded oriented source atom index. -/
@[simp] theorem selectedSourceBoundOfEmbedding_source_val
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
      (edgeEquiv edge)).source.val = (enumeration (selectedSource graph edge)).val :=
  SelectedGeometry.toSourceBound_source_val (selectedGeometryOfEmbedding graph G)
    enumeration edgeEquiv edge

/-- Exact recovery of the encoded oriented target atom index. -/
@[simp] theorem selectedSourceBoundOfEmbedding_target_val
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
      (edgeEquiv edge)).target.val = (enumeration (selectedTarget graph edge)).val :=
  SelectedGeometry.toSourceBound_target_val (selectedGeometryOfEmbedding graph G)
    enumeration edgeEquiv edge

/-- Recovery of the physical source atom label from the source-bound table. -/
theorem selectedSourceBoundOfEmbedding_recovered_source
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    (sourceAtomEquiv graph enumeration).symm
        ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
          (edgeEquiv edge)).source = selectedSource graph edge :=
  SelectedGeometry.toSourceBound_recovered_source (selectedGeometryOfEmbedding graph G)
    enumeration edgeEquiv edge

/-- Recovery of the physical target atom label from the source-bound table. -/
theorem selectedSourceBoundOfEmbedding_recovered_target
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) :
    (sourceAtomEquiv graph enumeration).symm
        ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
          (edgeEquiv edge)).target = selectedTarget graph edge :=
  SelectedGeometry.toSourceBound_recovered_target (selectedGeometryOfEmbedding graph G)
    enumeration edgeEquiv edge

/-- **Exact recovery of every parametrized arc** from the accepted source-bound table, and it is
exactly the global embedding's arc. -/
@[simp] theorem selectedSourceBoundOfEmbedding_arc
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) (t : I) :
    ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
      (edgeEquiv edge)).arc t = G.arc edge t :=
  SelectedGeometry.toSourceBound_arc (selectedGeometryOfEmbedding graph G)
    enumeration edgeEquiv edge t

/-- **Exact unique coverage in the accepted source-bound record**, from one global embedding. -/
theorem selectedSourceBoundOfEmbedding_exact_coverage
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    {index : Fin (graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (graph.encode enumeration) index) :
    ∃! edge : SelectedBondIndex graph,
      ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
        (edgeEquiv edge)).sourceInteraction = index :=
  sourceBound_exact_coverage (selectedGeometryOfEmbedding graph G) enumeration edgeEquiv genuine

/-! ## Concrete inhabited fixture

The construction is not vacuous: a one-atom graph with no interactions has a unique selected
occurrence type (empty), a genuine real conformation, and a complete bond-path table whose
documented subset is empty.  This is an actual source graph witness, independent of any
embedding-existence assumption. -/

/-- A semantic atom record used by the fixture. -/
def fixtureAtom : SemanticAtom where
  element := { atomicNumber := 1, positive := by decide, atMost118 := by decide }
  isotopeMassNumber? := none
  formalCharge := 0
  unpairedElectrons := 0
  aromaticInput := false

/-- The one-atom, interaction-free source graph. -/
def fixtureGraph : FiniteAtomInteractionHypergraph (Fin 1) where
  atomData := fun _ => fixtureAtom
  interactions := []
  arity_ge_two := by
    intro edge member
    simp at member
  participants_nodup := by
    intro edge member
    simp at member

/-- The selected occurrence type of the interaction-free graph is empty. -/
instance fixtureSelectedIsEmpty : IsEmpty (SelectedBondIndex fixtureGraph) where
  false edge := by
    have bound := edge.1.isLt
    simpa [fixtureGraph] using bound

/-- The canonical geometry of the fixture: one atom at the origin and no arcs. -/
def fixtureGeometry : SelectedGeometry fixtureGraph where
  conformation := fun _ => 0
  arc := fun edge => isEmptyElim edge
  source_endpoint := fun edge => isEmptyElim edge
  target_endpoint := fun edge => isEmptyElim edge
  atom_injective := by
    intro first second _
    exact Subsingleton.elim first second
  arc_injective := fun edge => isEmptyElim edge
  interior_avoids_atoms := fun edge => isEmptyElim edge
  intersects_only_at_common_endpoints := fun edge => isEmptyElim edge

/-- The constructed independent bond-path data of the fixture. -/
def fixtureData : IndependentBondPathData (Fin 1) (SelectedBondIndex fixtureGraph) :=
  fixtureGeometry.toIndependentBondPathData

/-- The fixture's completeness proof, for the canonical enumeration. -/
theorem fixture_complete :
    fixtureData.CompleteForSourcePairBonds (Equiv.refl (Fin 1)) :=
  fixtureGeometry.completeForSourcePairBonds (Equiv.refl (Fin 1))

/-- The fixture has no documented selected occurrences. -/
theorem fixture_documented_card :
    (fixtureData.toBondPathTable (Equiv.refl (Fin 1))).documented.card = 0 := by
  rw [IndependentBondPathData.card_documented_eq_card_edges]
  simp

/-! ## Molecular evidence of the generated path family

The assembled evidence request stores exactly the source graph, the shared real conformation and
the generated path family.  No preconstructed request, target table or geometric hypothesis is
an input: the request is *constructed* from the independent bond-path data, whose data fields are
themselves constructed above. -/

variable {E : Type} [Fintype E]

/-- The generated finite path family. -/
def independentPathFamily (data : IndependentBondPathData V E) : IndependentPathFamily V :=
  letI : Fintype E := ‹Fintype E›
  ⟨E, ‹Fintype E›, data⟩

@[simp] theorem independentPathFamily_graph (data : IndependentBondPathData V E) :
    (independentPathFamily data).graph = data.graph := rfl

@[simp] theorem independentPathFamily_conformation (data : IndependentBondPathData V E) :
    (independentPathFamily data).conformation = data.conformation := rfl

@[simp] theorem independentPathFamily_data (data : IndependentBondPathData V E) :
    (independentPathFamily data).data = data := rfl

/-- The actual molecular-evidence request generated from independent bond-path data.  The graph
and conformation are the data's own; the path channel is present with exactly the generated
family; every optional electronic, band, rational-coordinate, drawing, fragment, convention, cage,
residue and frame channel is genuinely absent/empty. -/
def toMolecularEvidence (data : IndependentBondPathData V E) : OrganicMolecularEvidence V where
  graph := data.graph
  conformation := data.conformation
  rationalPositions? := none
  rationalPositions_valid := by
    intro positions present
    cases present
  electronic? := none
  electronic_unpaired := by
    intro evidence present
    cases present
  paths? := some (independentPathFamily data)
  paths_graph_eq := by
    intro family present
    have familyEq : family = independentPathFamily data := (Option.some.inj present).symm
    subst familyEq
    rfl
  paths_conformation_eq := by
    intro family present
    have familyEq : family = independentPathFamily data := (Option.some.inj present).symm
    subst familyEq
    rfl
  bands? := none
  bands_graph_eq := by
    intro bands present
    cases present
  bands_conformation_eq := by
    intro bands present
    cases present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  diagram? := none
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by
    intro row member
    simp at member
  fragments := []
  conventions := []
  cages := []
  residueLedger? := none
  frames := []

@[simp] theorem toMolecularEvidence_graph (data : IndependentBondPathData V E) :
    (toMolecularEvidence data).graph = data.graph := rfl

@[simp] theorem toMolecularEvidence_conformation (data : IndependentBondPathData V E) :
    (toMolecularEvidence data).conformation = data.conformation := rfl

@[simp] theorem toMolecularEvidence_paths (data : IndependentBondPathData V E) :
    (toMolecularEvidence data).paths? = some (independentPathFamily data) := rfl

@[simp] theorem toMolecularEvidence_bands (data : IndependentBondPathData V E) :
    (toMolecularEvidence data).bands? = none := rfl

@[simp] theorem toMolecularEvidence_electronic (data : IndependentBondPathData V E) :
    (toMolecularEvidence data).electronic? = none := rfl

/-! ## Exact recovery through the actual assembly -/

/-- The upstream assembly decodes the constructed request exactly. -/
theorem decode_assemble_toMolecularEvidence (data : IndependentBondPathData V E) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularEvidenceAssembly.assemble (toMolecularEvidence data)) =
      toMolecularEvidence data :=
  OrganicStereoMolecularEvidenceAssembly.decode_assemble _

/-- The assembled source graph is exactly the generated graph. -/
theorem assemble_stateGraph_toMolecularEvidence (data : IndependentBondPathData V E) :
    (OrganicStereoMolecularEvidenceAssembly.assemble (toMolecularEvidence data)).stateGraph =
      data.graph := by
  rw [OrganicStereoMolecularEvidenceAssembly.assemble_graph_of_no_bands _ rfl,
    toMolecularEvidence_graph]

/-- The assembled conformation is exactly the generated conformation. -/
theorem assemble_stateConformation_toMolecularEvidence
    (data : IndependentBondPathData V E) :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (toMolecularEvidence data)).stateConformation = data.conformation := by
  rw [OrganicStereoMolecularEvidenceAssembly.assemble_conformation_of_no_bands _ rfl,
    toMolecularEvidence_conformation]

/-- The decoded path option is exactly the generated family. -/
theorem decodedPaths?_assemble_toMolecularEvidence (data : IndependentBondPathData V E) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularEvidenceAssembly.assemble (toMolecularEvidence data)) =
      some (independentPathFamily data) := by
  rw [OrganicStereoMolecularEvidenceAssembly.assemble_paths?, toMolecularEvidence_paths]

/-- The decoded path option is exactly the generated family after canonical finite transport as
well. -/
theorem decodedPaths?_canonicalAssemble_toMolecularEvidence
    (enumeration : V ≃ Fin (Fintype.card V)) (data : IndependentBondPathData V E) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (toMolecularEvidence data))) =
      some (independentPathFamily data) := by
  rw [OrganicStereoMolecularCanonicalTransport.canonicalDecode_canonicalAssemble,
    decodedPaths?_assemble_toMolecularEvidence]

/-- The actual canonical assembly, decoded by the upstream request decoder, recovers the
constructed request exactly. -/
theorem decode_canonicalAssemble_toMolecularEvidence
    (enumeration : V ≃ Fin (Fintype.card V)) (data : IndependentBondPathData V E) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (toMolecularEvidence data))) =
      toMolecularEvidence data :=
  OrganicStereoMolecularCanonicalTransport.decode_canonicalAssemble enumeration _

/-- Set-image recovery for the generated request family: decoding the assembled generated
requests recovers exactly the generated requests, for any set of independent bond-path data.  No
injectivity of the generator is needed, because the pointwise decode is the identity on the
image. -/
theorem decode_assemble_image_toMolecularEvidence
    (dataSet : Set (IndependentBondPathData V E)) :
    (fun data => OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularEvidenceAssembly.assemble (toMolecularEvidence data))) ''
        dataSet =
      toMolecularEvidence '' dataSet := by
  have pointwise :
      (fun data : IndependentBondPathData V E =>
        OrganicStereoMolecularEvidenceAssembly.decode
          (OrganicStereoMolecularEvidenceAssembly.assemble
            (toMolecularEvidence (E := E) data))) =
        (fun data : IndependentBondPathData V E => toMolecularEvidence (E := E) data) :=
    funext (fun data => decode_assemble_toMolecularEvidence (E := E) data)
  rw [pointwise]

/-- The same set-image recovery through the canonical finite transport and both decoders. -/
theorem decode_canonicalAssemble_image_toMolecularEvidence
    (enumeration : V ≃ Fin (Fintype.card V))
    (dataSet : Set (IndependentBondPathData V E)) :
    (fun data => OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (toMolecularEvidence data)))) '' dataSet =
      toMolecularEvidence '' dataSet := by
  have pointwise :
      (fun data : IndependentBondPathData V E =>
        OrganicStereoMolecularEvidenceAssembly.decode
          (OrganicStereoMolecularCanonicalTransport.canonicalDecode
            (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
              (toMolecularEvidence (E := E) data)))) =
        (fun data : IndependentBondPathData V E => toMolecularEvidence (E := E) data) :=
    funext (fun data => decode_canonicalAssemble_toMolecularEvidence enumeration (E := E) data)
  rw [pointwise]

/-! ### Composition with the actual molecular assembly, from one global embedding -/

/-- The actual `OrganicMolecularEvidence` request generated by one global embedding.  Its graph and
conformation are the constructed data's own and its path channel holds exactly the generated
family. -/
def selectedEvidenceOfEmbedding (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    OrganicMolecularEvidence V :=
  toMolecularEvidence (selectedDataOfEmbedding graph G)

/-- The raw-map form of the generated molecular evidence. -/
def selectedEvidenceOfMap (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map) :
    OrganicMolecularEvidence V :=
  selectedEvidenceOfEmbedding graph (embeddedGraphOfMap graph map injective)

@[simp] theorem selectedEvidenceOfEmbedding_graph
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    (selectedEvidenceOfEmbedding graph G).graph = graph := rfl

@[simp] theorem selectedEvidenceOfEmbedding_conformation
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    (selectedEvidenceOfEmbedding graph G).conformation = G.conformation := rfl

@[simp] theorem selectedEvidenceOfEmbedding_paths
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    (selectedEvidenceOfEmbedding graph G).paths? =
      some (independentPathFamily (selectedDataOfEmbedding graph G)) := rfl

/-- The actual assembly recovers exactly the source graph. -/
theorem assemble_stateGraph_selectedEvidenceOfEmbedding
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (selectedEvidenceOfEmbedding graph G)).stateGraph = graph := by
  simpa only [selectedEvidenceOfEmbedding, selectedDataOfEmbedding_graph] using
    assemble_stateGraph_toMolecularEvidence (selectedDataOfEmbedding graph G)

/-- The actual assembly recovers exactly the global embedding's vertex coordinates. -/
theorem assemble_stateConformation_selectedEvidenceOfEmbedding
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (selectedEvidenceOfEmbedding graph G)).stateConformation = G.conformation := by
  simpa only [selectedEvidenceOfEmbedding, selectedDataOfEmbedding_conformation] using
    assemble_stateConformation_toMolecularEvidence (selectedDataOfEmbedding graph G)

/-- The actual assembly recovers exactly the generated parametrized path family. -/
theorem decodedPaths?_assemble_selectedEvidenceOfEmbedding
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularEvidenceAssembly.assemble
          (selectedEvidenceOfEmbedding graph G)) =
      some (independentPathFamily (selectedDataOfEmbedding graph G)) := by
  simpa only [selectedEvidenceOfEmbedding] using
    decodedPaths?_assemble_toMolecularEvidence (selectedDataOfEmbedding graph G)

/-- Canonical finite transport also recovers exactly the generated path family. -/
theorem decodedPaths?_canonicalAssemble_selectedEvidenceOfEmbedding
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (selectedEvidenceOfEmbedding graph G))) =
      some (independentPathFamily (selectedDataOfEmbedding graph G)) := by
  simpa only [selectedEvidenceOfEmbedding] using
    decodedPaths?_canonicalAssemble_toMolecularEvidence enumeration
      (selectedDataOfEmbedding graph G)

/-- The actual canonical molecular assembly, decoded by the upstream request decoder, recovers
exactly the generated request. -/
theorem decode_canonicalAssemble_selectedEvidenceOfEmbedding
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (selectedEvidenceOfEmbedding graph G))) =
      selectedEvidenceOfEmbedding graph G := by
  simpa only [selectedEvidenceOfEmbedding] using
    decode_canonicalAssemble_toMolecularEvidence enumeration
      (selectedDataOfEmbedding graph G)

/-- Non-canonical exact request recovery. -/
theorem decode_assemble_selectedEvidenceOfEmbedding
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph)) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularEvidenceAssembly.assemble
          (selectedEvidenceOfEmbedding graph G)) =
      selectedEvidenceOfEmbedding graph G := by
  simpa only [selectedEvidenceOfEmbedding] using
    decode_assemble_toMolecularEvidence (selectedDataOfEmbedding graph G)

/-- **Canonical image-set recovery for the embedding-constructed requests.**  Decoding the
assembled requests generated by any set of global embeddings recovers exactly the generated
requests. -/
theorem decode_canonicalAssemble_selectedEvidenceOfEmbedding_image
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (embeddingSet : Set (EmbeddedGraph (selectedSource graph) (selectedTarget graph))) :
    (fun G => OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (selectedEvidenceOfEmbedding graph G)))) '' embeddingSet =
      selectedEvidenceOfEmbedding graph '' embeddingSet := by
  have pointwise :
      (fun G : EmbeddedGraph (selectedSource graph) (selectedTarget graph) =>
        OrganicStereoMolecularEvidenceAssembly.decode
          (OrganicStereoMolecularCanonicalTransport.canonicalDecode
            (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
              (selectedEvidenceOfEmbedding graph G)))) =
        (fun G : EmbeddedGraph (selectedSource graph) (selectedTarget graph) =>
          selectedEvidenceOfEmbedding graph G) :=
    funext (fun G => decode_canonicalAssemble_selectedEvidenceOfEmbedding graph G enumeration)
  rw [pointwise]

/-- **Molecular-assembly endpoint from one global embedding.**  A single global continuous
injective realization map yields actual `OrganicMolecularEvidence` whose graph is the exact source
graph, whose vertex coordinates are the embedding's vertex positions, whose path channel is the
generated family, whose assembly recovers the graph and coordinates exactly, and whose canonical
assembly decodes back to the same generated request. -/
theorem exists_molecular_evidence_of_global_embedding
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    ∃ evidence : OrganicMolecularEvidence V,
      evidence.graph = graph ∧
      evidence.conformation = (embeddedGraphOfMap graph map injective).conformation ∧
      evidence.paths? = some (independentPathFamily
        (selectedDataOfMap graph map injective)) ∧
      (OrganicStereoMolecularEvidenceAssembly.assemble evidence).stateGraph = graph ∧
      (OrganicStereoMolecularEvidenceAssembly.assemble evidence).stateConformation =
        (embeddedGraphOfMap graph map injective).conformation ∧
      OrganicStereoMolecularEvidenceAssembly.decodedPaths?
          (OrganicStereoMolecularEvidenceAssembly.assemble evidence) =
        some (independentPathFamily (selectedDataOfMap graph map injective)) ∧
      OrganicStereoMolecularEvidenceAssembly.decode
          (OrganicStereoMolecularCanonicalTransport.canonicalDecode
            (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
              evidence)) = evidence := by
  refine ⟨selectedEvidenceOfMap graph map injective, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [selectedEvidenceOfMap] using
      assemble_stateGraph_selectedEvidenceOfEmbedding graph
        (embeddedGraphOfMap graph map injective)
  · simpa only [selectedEvidenceOfMap] using
      assemble_stateConformation_selectedEvidenceOfEmbedding graph
        (embeddedGraphOfMap graph map injective)
  · simpa only [selectedEvidenceOfMap] using
      decodedPaths?_assemble_selectedEvidenceOfEmbedding graph
        (embeddedGraphOfMap graph map injective)
  · simpa only [selectedEvidenceOfMap] using
      decode_canonicalAssemble_selectedEvidenceOfEmbedding graph
        (embeddedGraphOfMap graph map injective) enumeration

/-! ## A concrete source graph with an actual selected bond

The one-atom fixture above is a genuine but empty witness.  This section adds a two-atom source
graph with one selected binary bond and a concrete global embedding of its canonical realization
(in the sense of `OrganicStereoEmbeddedGraphRealization`), so the decisive theorem is instantiated
with a nonempty selected occurrence type and a real parametrized arc.

The embedding is the selected-graph analogue of the realization module's single-edge toy example:
vertices `false` and `true` are sent to `0` and a chosen nonzero point `p`, and interior points of
the unique edge are sent to `t • p`.  Continuity is obtained from the coinduced universal property
of the realization, as in that example. -/

/-- Two atoms, one selected binary (unspecified covalent) bond. -/
def toySourceGraph : FiniteAtomInteractionHypergraph Bool where
  atomData := fun _ => fixtureAtom
  interactions := [([false, true], SemanticInteractionKind.unspecifiedCovalent)]
  arity_ge_two := by
    intro interaction member
    rw [List.mem_singleton] at member
    subst interaction
    decide
  participants_nodup := by
    intro interaction member
    rw [List.mem_singleton] at member
    subst interaction
    decide

/-- The unique selected occurrence of the toy source graph. -/
def toyEdge : SelectedBondIndex toySourceGraph :=
  ⟨⟨0, by decide⟩, by decide, by decide⟩

/-- The underlying index value of every toy selected occurrence is `0` (the occurrence type is a
subtype of `Fin 1`). -/
theorem toySelected_fin_val_eq_zero (edge : SelectedBondIndex toySourceGraph) :
    edge.1.val = 0 := by
  apply Nat.lt_one_iff.mp
  simpa [toySourceGraph] using edge.1.isLt

/-- The occurrence index of every toy selected edge is the unique index `0`. -/
theorem toySelected_index_eq_zero (edge : SelectedBondIndex toySourceGraph) :
    edge.1 = ⟨0, by simpa [toySourceGraph] using Nat.zero_lt_one⟩ := by
  apply Fin.ext
  exact toySelected_fin_val_eq_zero edge

/-- The selected occurrence type of the toy source graph is a subsingleton (it is a subtype of
`Fin 1`). -/
instance toySelectedSubsingleton : Subsingleton (SelectedBondIndex toySourceGraph) :=
  ⟨fun first second => by
    apply Subtype.ext
    rw [toySelected_index_eq_zero first, toySelected_index_eq_zero second]⟩

/-- Every selected occurrence of the toy graph is the unique one. -/
theorem toySelected_card : Fintype.card (SelectedBondIndex toySourceGraph) = 1 :=
  Fintype.card_eq_one_of_forall_eq (fun edge => Subsingleton.elim edge toyEdge)

/-- The oriented source endpoint of the toy bond is `false`. -/
theorem toySelected_source (edge : SelectedBondIndex toySourceGraph) :
    selectedSource toySourceGraph edge = false := by
  have pair : [false, true] =
      [selectedSource toySourceGraph edge, selectedTarget toySourceGraph edge] := by
    have h := selectedParticipants toySourceGraph edge
    rw [toySelected_index_eq_zero edge] at h
    simpa [toySourceGraph] using h
  exact ((List.cons.inj pair).1).symm

/-- The oriented target endpoint of the toy bond is `true`. -/
theorem toySelected_target (edge : SelectedBondIndex toySourceGraph) :
    selectedTarget toySourceGraph edge = true := by
  have pair : [false, true] =
      [selectedSource toySourceGraph edge, selectedTarget toySourceGraph edge] := by
    have h := selectedParticipants toySourceGraph edge
    rw [toySelected_index_eq_zero edge] at h
    simpa [toySourceGraph] using h
  exact ((List.cons.inj (List.cons.inj pair).2).1).symm

/-- The concrete global map on the toy selected-graph realization. -/
def toySourceMap :
    Realization (selectedSource toySourceGraph) (selectedTarget toySourceGraph) → EmbeddedReal3
  | Realization.vertex atom => toyVertexPoint atom
  | Realization.interior _ t => (t.1 : ℝ) • toyNonzeroPoint

/-- The raw-domain map whose continuity implies continuity by the coinduced universal property. -/
def toySourceRawMap :
    RawDomain Bool (SelectedBondIndex toySourceGraph) → EmbeddedReal3 :=
  Sum.elim (fun vertex : RawVertex Bool => toyVertexPoint vertex.1)
    (fun interval : RawInterval (SelectedBondIndex toySourceGraph) =>
      (interval.2 : ℝ) • toyNonzeroPoint)

/-- The composite of the concrete map with the gluing map is the explicit raw map. -/
theorem toySourceMap_comp_glue :
    toySourceMap ∘ glue (selectedSource toySourceGraph) (selectedTarget toySourceGraph) =
      toySourceRawMap := by
  funext point
  cases point with
  | inl vertex =>
      obtain ⟨atom, fiber⟩ := vertex
      cases atom <;> rfl
  | inr interval =>
      obtain ⟨edge, t⟩ := interval
      by_cases h0 : t = 0
      · rw [h0, Function.comp_apply, glue_inr, glueInterval_zero]
        simp [toySourceMap, toySourceRawMap, toySelected_source edge]
      · by_cases h1 : t = 1
        · rw [h1, Function.comp_apply, glue_inr, glueInterval_one]
          simp [toySourceMap, toySourceRawMap, toySelected_target edge]
        · rw [Function.comp_apply, glue_inr,
            glueInterval_interior _ _ edge t h0 h1]
          rfl

/-- The raw map is continuous, by the same argument as in the realization module's toy example. -/
theorem toySourceRawMap_continuous : Continuous toySourceRawMap := by
  unfold toySourceRawMap
  apply Continuous.sumElim
  · apply continuous_sigma
    intro atom
    exact (continuous_const : Continuous (fun _ : Unit => toyVertexPoint atom))
  · apply continuous_sigma
    intro edge
    exact continuous_subtype_val.smul
      (continuous_const : Continuous (fun _ : I => toyNonzeroPoint))

/-- Continuity of the concrete map, obtained from the coinduced universal property. -/
theorem toySourceMap_continuous : Continuous toySourceMap :=
  (continuous_coinduced_dom
    (f := glue (selectedSource toySourceGraph) (selectedTarget toySourceGraph))
    (g := toySourceMap)).2 (by
    rw [toySourceMap_comp_glue]
    exact toySourceRawMap_continuous)

/-- Injectivity of the concrete map: the vertex points are distinct and the interior of the edge
never meets a vertex or another interior parameter. -/
theorem toySourceMap_injective : Function.Injective toySourceMap := by
  intro x y h
  cases x with
  | vertex a =>
      cases y with
      | vertex b =>
          have hab : a = b := toyVertexPoint_injective h
          subst b
          rfl
      | interior e t =>
          cases a
          · exact absurd
              (toySmul_eq_zero (t := t.1)
                (show (t.1 : ℝ) • toyNonzeroPoint = 0 from h.symm)) t.2.1
          · exact absurd
              (toySmul_eq_point (t := t.1)
                (show (t.1 : ℝ) • toyNonzeroPoint = toyNonzeroPoint from h.symm)) t.2.2
  | interior e t =>
      cases y with
      | vertex a =>
          cases a
          · exact absurd
              (toySmul_eq_zero (t := t.1)
                (show (t.1 : ℝ) • toyNonzeroPoint = 0 from h)) t.2.1
          · exact absurd
              (toySmul_eq_point (t := t.1)
                (show (t.1 : ℝ) • toyNonzeroPoint = toyNonzeroPoint from h)) t.2.2
      | interior f s =>
          have same : (t.1 : ℝ) • toyNonzeroPoint = (s.1 : ℝ) • toyNonzeroPoint := h
          have parameters : t.1 = s.1 := toySmul_injective same
          have edges : e = f := Subsingleton.elim e f
          rw [edges]
          exact congrArg
            (Realization.interior (src := selectedSource toySourceGraph)
              (dst := selectedTarget toySourceGraph) f) (Subtype.ext parameters)

/-- The concrete global embedding of the toy selected-bond graph. -/
def toySourceEmbeddedGraph :
    EmbeddedGraph (selectedSource toySourceGraph) (selectedTarget toySourceGraph) where
  map := ⟨toySourceMap, toySourceMap_continuous⟩
  injective := toySourceMap_injective

/-- The actual independent bond-path data produced for the nonempty toy graph. -/
def toyConstructedData :
    IndependentBondPathData Bool (SelectedBondIndex toySourceGraph) :=
  selectedDataOfEmbedding toySourceGraph toySourceEmbeddedGraph

/-- The generated data is complete for the canonical finite enumeration of `Bool`. -/
theorem toyConstructedData_complete :
    toyConstructedData.CompleteForSourcePairBonds (Fintype.equivFin Bool) :=
  selectedDataOfEmbedding_completeForSourcePairBonds toySourceGraph toySourceEmbeddedGraph
    (Fintype.equivFin Bool)

/-- The generated data's graph is the exact toy source graph. -/
theorem toyConstructedData_graph : toyConstructedData.graph = toySourceGraph := rfl

/-- The documented table has exactly one entry: the unique selected bond. -/
theorem toyConstructedData_documented_card :
    (toyConstructedData.toBondPathTable (Fintype.equivFin Bool)).documented.card = 1 := by
  rw [IndependentBondPathData.card_documented_eq_card_edges, toySelected_card]

/-- At the left endpoint the concrete arc is the position of `false`. -/
theorem toyConstructedData_arc_zero (edge : SelectedBondIndex toySourceGraph) :
    toyConstructedData.arc edge 0 = 0 := by
  change (selectedDataOfEmbedding toySourceGraph toySourceEmbeddedGraph).arc edge 0 = 0
  rw [selectedDataOfEmbedding_arc]
  show toySourceEmbeddedGraph.map
      (edgePoint (selectedSource toySourceGraph) (selectedTarget toySourceGraph) edge 0) = 0
  rw [edgePoint_zero, toySelected_source edge]
  change toySourceMap (Realization.vertex false) = 0
  rfl

/-- At the right endpoint the concrete arc is the chosen nonzero point. -/
theorem toyConstructedData_arc_one (edge : SelectedBondIndex toySourceGraph) :
    toyConstructedData.arc edge 1 = toyNonzeroPoint := by
  change (selectedDataOfEmbedding toySourceGraph toySourceEmbeddedGraph).arc edge 1 =
    toyNonzeroPoint
  rw [selectedDataOfEmbedding_arc]
  show toySourceEmbeddedGraph.map
      (edgePoint (selectedSource toySourceGraph) (selectedTarget toySourceGraph) edge 1) =
        toyNonzeroPoint
  rw [edgePoint_one, toySelected_target edge]
  change toySourceMap (Realization.vertex true) = toyNonzeroPoint
  rfl

/-- Every interior arc value is exactly `t • p`. -/
theorem toyConstructedData_arc_interior (edge : SelectedBondIndex toySourceGraph) (t : I)
    (h0 : t ≠ 0) (h1 : t ≠ 1) :
    toyConstructedData.arc edge t = (t : ℝ) • toyNonzeroPoint := by
  change (selectedDataOfEmbedding toySourceGraph toySourceEmbeddedGraph).arc edge t =
    (t : ℝ) • toyNonzeroPoint
  rw [selectedDataOfEmbedding_arc]
  show toySourceEmbeddedGraph.map
      (edgePoint (selectedSource toySourceGraph) (selectedTarget toySourceGraph) edge t) =
        (t : ℝ) • toyNonzeroPoint
  rw [edgePoint_interior _ _ edge t h0 h1]
  rfl

end

end OrganicStereoEmbeddedMolecularGraphCoverage

end TetraStereo.OneCenter
