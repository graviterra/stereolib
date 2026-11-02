import TetraStereo.OneCenter.OrganicStereoIndependentPathEncoding
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription

set_option autoImplicit false

namespace TetraStereo.OneCenter

open scoped unitInterval

/-!
# Ingress from independent physical bond-path data into the whole-state description

`OrganicStereoIndependentPathEncoding.IndependentBondPathData` is a genuinely independent physical
source: an atom-labelled interaction hypergraph over an arbitrary finite atom type `V`, one real
point per atom, an oriented occurrence/endpoint/arc record for every edge of an arbitrary finite
edge type `E`, and the physical geometric axioms.  `OrganicStereoFiniteClassicalDescription`
provides the actual domain record `WholeState` and its path channel (`PathAnnotation`,
`path_valid`, arc endpoint agreement), together with the adapter
`toIndependentBondPathData : WholeState → PathGeometryValid → IndependentBondPathData`.

This module supplies the missing direction, for *every* independent record and with no extra
hypothesis:

* `toWholeState : IndependentBondPathData V E → WholeState V E (Fin 0)`.  The graph and the real
  conformation are the supplied ones; the path channel is built from the supplied occurrence
  indices, oriented atom labels and continuous arcs; every path validity bound, participant
  equation, kind equation and endpoint equation is discharged from the corresponding independent
  field.  The optional electronic, rational, drawing and ordered annotation channels are absent
  (`none` / `[]`); in particular no rational position is fabricated.  The band index type is
  `Fin 0`, so the band family is the genuine empty family.
* `pathGeometryValid` proves the existing `PathGeometryValid` predicate for that state directly
  from the independent geometry axioms.  It is not assumed and not restated: it is the domain's
  own predicate.
* `toIndependentBondPathData_toWholeState` proves that the existing domain adapter, applied to the
  constructed state, returns the original independent record *in full*, including all
  proposition-valued fields (proof irrelevance).  Hence the graph, conformation, every occurrence
  index, every oriented endpoint, every arc, and the geometric obligations are recovered exactly.
* `toEncodedDescription` and `decodeDescription_toEncodedDescription` lift the construction through
  the existing `encodeDescription` / `decodeDescription` pair at the canonical `Fin` schema, and
  the decoded state still carries the original graph and conformation (source preservation).

No chemical embedding existence, no rational realizability and no global chemistry-exhaustiveness
claim is made here.  This is a coverage adapter into the existing domain, not a new encoder.
-/

namespace IndependentBondPathData

variable {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]

/-! ## The path channel of one independent edge -/

/-- The domain path annotation of an independent edge.  The occurrence index, the two oriented
atom labels and the continuous arc are copied literally from the independent record; the endpoint
distinctness proof is the independent one. -/
def toPathAnnotation (data : IndependentBondPathData V E) (edge : E) :
    PathAnnotation V where
  interactionIndex := data.interactionOccurrence edge
  source := data.source edge
  target := data.target edge
  source_ne_target := data.source_ne_target edge
  arc := data.arc edge

@[simp] theorem toPathAnnotation_interactionIndex (data : IndependentBondPathData V E)
    (edge : E) :
    (data.toPathAnnotation edge).interactionIndex = data.interactionOccurrence edge := rfl

@[simp] theorem toPathAnnotation_source (data : IndependentBondPathData V E) (edge : E) :
    (data.toPathAnnotation edge).source = data.source edge := rfl

@[simp] theorem toPathAnnotation_target (data : IndependentBondPathData V E) (edge : E) :
    (data.toPathAnnotation edge).target = data.target edge := rfl

@[simp] theorem toPathAnnotation_arc (data : IndependentBondPathData V E) (edge : E) :
    (data.toPathAnnotation edge).arc = data.arc edge := rfl

@[simp] theorem toPathAnnotation_source_ne_target (data : IndependentBondPathData V E)
    (edge : E) :
    (data.toPathAnnotation edge).source ≠ (data.toPathAnnotation edge).target :=
  data.source_ne_target edge

/-! ## The constructed whole state -/

/-- The whole-state ingress of independent physical bond-path data.

The graph and the shared real conformation are the input's own; the path family is the dependent
copy of the input occurrence, endpoint and arc data; the path-validity bounds and the participant,
kind and endpoint equations are the input's actual proofs.  Every optional annotation channel is
absent (`none` or the empty list), so no electronic, drawing, rational, role, fragment, convention
or cage data is invented.  The band index type is `Fin 0`, so the band family is empty and the
band agreement field is vacuous. -/
def toWholeState (data : IndependentBondPathData V E) : WholeState V E (Fin 0) where
  graph := data.graph
  electronic? := none
  electronic_unpaired := by
    intro channel present
    simp at present
  conformation := data.conformation
  rationalPositions? := none
  rationalPositions_valid := by
    intro positions present
    simp at present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  paths := data.toPathAnnotation
  path_valid := by
    intro edge
    refine ⟨data.interactionOccurrence_lt edge, ?_, ?_⟩
    · exact data.participants_exact edge
    · exact data.kind_selected edge
  path_source_endpoint := by
    intro edge
    exact data.source_endpoint edge
  path_target_endpoint := by
    intro edge
    exact data.target_endpoint edge
  bandFamily := Fin.elim0
  band_agreement := fun band => Fin.elim0 band
  diagram? := none
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by
    intro row member
    simp at member
  fragments := []
  conventions := []
  cages := []

/-! ### Projections of the constructed state -/

@[simp] theorem toWholeState_graph (data : IndependentBondPathData V E) :
    data.toWholeState.graph = data.graph := rfl

@[simp] theorem toWholeState_conformation (data : IndependentBondPathData V E) :
    data.toWholeState.conformation = data.conformation := rfl

@[simp] theorem toWholeState_electronic? (data : IndependentBondPathData V E) :
    data.toWholeState.electronic? = none := rfl

@[simp] theorem toWholeState_rationalPositions? (data : IndependentBondPathData V E) :
    data.toWholeState.rationalPositions? = none := rfl

@[simp] theorem toWholeState_roles (data : IndependentBondPathData V E) :
    data.toWholeState.roles = [] := rfl

@[simp] theorem toWholeState_paths (data : IndependentBondPathData V E) (edge : E) :
    data.toWholeState.paths edge = data.toPathAnnotation edge := rfl

@[simp] theorem toWholeState_paths_interactionIndex (data : IndependentBondPathData V E)
    (edge : E) :
    (data.toWholeState.paths edge).interactionIndex = data.interactionOccurrence edge := rfl

@[simp] theorem toWholeState_paths_source (data : IndependentBondPathData V E) (edge : E) :
    (data.toWholeState.paths edge).source = data.source edge := rfl

@[simp] theorem toWholeState_paths_target (data : IndependentBondPathData V E) (edge : E) :
    (data.toWholeState.paths edge).target = data.target edge := rfl

@[simp] theorem toWholeState_paths_arc (data : IndependentBondPathData V E) (edge : E) :
    (data.toWholeState.paths edge).arc = data.arc edge := rfl

@[simp] theorem toWholeState_diagram? (data : IndependentBondPathData V E) :
    data.toWholeState.diagram? = none := rfl

@[simp] theorem toWholeState_diagramPartial? (data : IndependentBondPathData V E) :
    data.toWholeState.diagramPartial? = none := rfl

@[simp] theorem toWholeState_diagramIncidence (data : IndependentBondPathData V E) :
    data.toWholeState.diagramIncidence = [] := rfl

@[simp] theorem toWholeState_fragments (data : IndependentBondPathData V E) :
    data.toWholeState.fragments = [] := rfl

@[simp] theorem toWholeState_conventions (data : IndependentBondPathData V E) :
    data.toWholeState.conventions = [] := rfl

@[simp] theorem toWholeState_cages (data : IndependentBondPathData V E) :
    data.toWholeState.cages = [] := rfl

/-- The physical path fields of the constructed state are exactly the independent input fields,
including both endpoint equations against the shared conformation. -/
theorem toWholeState_path_fields (data : IndependentBondPathData V E) (edge : E) :
    (data.toWholeState.paths edge).interactionIndex = data.interactionOccurrence edge ∧
      (data.toWholeState.paths edge).source = data.source edge ∧
      (data.toWholeState.paths edge).target = data.target edge ∧
      (data.toWholeState.paths edge).arc = data.arc edge ∧
      (data.toWholeState.paths edge).arc 0 =
        data.toWholeState.conformation (data.toWholeState.paths edge).source ∧
      (data.toWholeState.paths edge).arc 1 =
        data.toWholeState.conformation (data.toWholeState.paths edge).target :=
  ⟨rfl, rfl, rfl, rfl, data.source_endpoint edge, data.target_endpoint edge⟩

/-- Every independent occurrence index is realized by the constructed path channel, with the
bound supplied by the independent range proof. -/
theorem toWholeState_path_valid_index (data : IndependentBondPathData V E) (edge : E) :
    (data.toWholeState.paths edge).interactionIndex = data.interactionOccurrence edge ∧
      (data.toWholeState.paths edge).interactionIndex <
        data.toWholeState.graph.interactions.length :=
  ⟨rfl, data.interactionOccurrence_lt edge⟩

/-- The constructed path occurrence map is injective exactly because the independent occurrence
map is. -/
theorem toWholeState_occurrence_injective (data : IndependentBondPathData V E) :
    Function.Injective fun edge => (data.toWholeState.paths edge).interactionIndex :=
  data.interactionOccurrence_injective

/-! ### The existing geometry predicate -/

/-- The independent geometric axioms prove the domain's `PathGeometryValid` for the constructed
state.  This is the existing predicate of `OrganicStereoFiniteClassicalDescription`; it is not
redefined or weakened. -/
theorem pathGeometryValid (data : IndependentBondPathData V E) :
    PathGeometryValid data.toWholeState where
  occurrence_injective := data.interactionOccurrence_injective
  atom_injective := data.atom_injective
  arc_injective := data.arc_injective
  interior_avoids_atoms := data.interior_avoids_atoms
  intersects_only_at_common_endpoints := by
    intro edge other t s different meet
    exact data.intersects_only_at_common_endpoints edge other t s different meet

end IndependentBondPathData

/-! ## Full recovery through the existing domain adapter -/

/-- Extensionality for `IndependentBondPathData`: equality of the six data fields determines the
whole record.  The eleven remaining fields are propositions, hence identified by proof
irrelevance.  This lemma is stated here because the ingress must recover the *whole* independent
record; it does not modify or duplicate any domain definition. -/
theorem independentBondPathData_extEq {V : Type*} [DecidableEq V] [Fintype V]
    {E : Type*} [Fintype E] {first second : IndependentBondPathData V E}
    (graph : first.graph = second.graph)
    (conformation : first.conformation = second.conformation)
    (occurrence : first.interactionOccurrence = second.interactionOccurrence)
    (source : first.source = second.source)
    (target : first.target = second.target)
    (arc : first.arc = second.arc) : first = second := by
  obtain ⟨firstGraph, firstConformation, firstOccurrence, firstOccurrenceLt,
    firstOccurrenceInjective, firstSource, firstTarget, firstDistinct, firstArc,
    firstParticipants, firstKind, firstSourceEndpoint, firstTargetEndpoint, firstAtomInjective,
    firstArcInjective, firstInterior, firstIntersections⟩ := first
  obtain ⟨secondGraph, secondConformation, secondOccurrence, secondOccurrenceLt,
    secondOccurrenceInjective, secondSource, secondTarget, secondDistinct, secondArc,
    secondParticipants, secondKind, secondSourceEndpoint, secondTargetEndpoint,
    secondAtomInjective, secondArcInjective, secondInterior, secondIntersections⟩ := second
  dsimp only at graph conformation occurrence source target arc
  cases graph
  cases conformation
  cases occurrence
  cases source
  cases target
  cases arc
  have occurrenceLt : firstOccurrenceLt = secondOccurrenceLt := Subsingleton.elim _ _
  have occurrenceInjective : firstOccurrenceInjective = secondOccurrenceInjective :=
    Subsingleton.elim _ _
  have distinct : firstDistinct = secondDistinct := Subsingleton.elim _ _
  have participants : firstParticipants = secondParticipants := Subsingleton.elim _ _
  have kind : firstKind = secondKind := Subsingleton.elim _ _
  have sourceEndpoint : firstSourceEndpoint = secondSourceEndpoint := Subsingleton.elim _ _
  have targetEndpoint : firstTargetEndpoint = secondTargetEndpoint := Subsingleton.elim _ _
  have atomInjective : firstAtomInjective = secondAtomInjective := Subsingleton.elim _ _
  have arcInjective : firstArcInjective = secondArcInjective := Subsingleton.elim _ _
  have interior : firstInterior = secondInterior := Subsingleton.elim _ _
  have intersections : firstIntersections = secondIntersections := Subsingleton.elim _ _
  cases occurrenceLt
  cases occurrenceInjective
  cases distinct
  cases participants
  cases kind
  cases sourceEndpoint
  cases targetEndpoint
  cases atomInjective
  cases arcInjective
  cases interior
  cases intersections
  rfl

/-- **Full recovery.**  Applying the existing domain adapter `toIndependentBondPathData` to the
constructed whole state returns the original independent record, including every proof field.
The chosen `PathGeometryValid` proof is irrelevant to the result, as expected. -/
theorem toIndependentBondPathData_toWholeState {V : Type*} [DecidableEq V] [Fintype V]
    {E : Type*} [Fintype E] (data : IndependentBondPathData V E)
    (valid : PathGeometryValid data.toWholeState) :
    toIndependentBondPathData data.toWholeState valid = data := by
  apply independentBondPathData_extEq <;> rfl

/-- Recovery of the graph. -/
@[simp] theorem toIndependentBondPathData_toWholeState_graph
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E) (valid : PathGeometryValid data.toWholeState) :
    (toIndependentBondPathData data.toWholeState valid).graph = data.graph := by
  rw [toIndependentBondPathData_toWholeState]

/-- Recovery of the real conformation. -/
@[simp] theorem toIndependentBondPathData_toWholeState_conformation
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E) (valid : PathGeometryValid data.toWholeState) :
    (toIndependentBondPathData data.toWholeState valid).conformation = data.conformation := by
  rw [toIndependentBondPathData_toWholeState]

/-- Recovery of the occurrence map. -/
@[simp] theorem toIndependentBondPathData_toWholeState_interactionOccurrence
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E) (valid : PathGeometryValid data.toWholeState) :
    (toIndependentBondPathData data.toWholeState valid).interactionOccurrence =
      data.interactionOccurrence := by
  rw [toIndependentBondPathData_toWholeState]

/-- Recovery of every bounded occurrence index. -/
@[simp] theorem toIndependentBondPathData_toWholeState_interactionIndex
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E) (valid : PathGeometryValid data.toWholeState)
    (edge : E) :
    (toIndependentBondPathData data.toWholeState valid).interactionIndex edge =
      data.interactionIndex edge := by
  apply Fin.ext
  rfl

/-- Recovery of every oriented source endpoint. -/
@[simp] theorem toIndependentBondPathData_toWholeState_source
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E) (valid : PathGeometryValid data.toWholeState) :
    (toIndependentBondPathData data.toWholeState valid).source = data.source := by
  rw [toIndependentBondPathData_toWholeState]

/-- Recovery of every oriented target endpoint. -/
@[simp] theorem toIndependentBondPathData_toWholeState_target
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E) (valid : PathGeometryValid data.toWholeState) :
    (toIndependentBondPathData data.toWholeState valid).target = data.target := by
  rw [toIndependentBondPathData_toWholeState]

/-- Recovery of every continuous arc. -/
@[simp] theorem toIndependentBondPathData_toWholeState_arc
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E) (valid : PathGeometryValid data.toWholeState) :
    (toIndependentBondPathData data.toWholeState valid).arc = data.arc := by
  rw [toIndependentBondPathData_toWholeState]

/-- Pointwise recovery of every arc value. -/
@[simp] theorem toIndependentBondPathData_toWholeState_arc_apply
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E) (valid : PathGeometryValid data.toWholeState)
    (edge : E) (t : I) :
    (toIndependentBondPathData data.toWholeState valid).arc edge t = data.arc edge t := by
  rw [toIndependentBondPathData_toWholeState]

/-! ## Transport of the domain adapter along an equality of states -/

/-- The domain adapter `toIndependentBondPathData` does not depend on which proof of
`PathGeometryValid` is supplied: its six data fields mention only the state. -/
theorem toIndependentBondPathData_valid_irrelevant
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (state : WholeState V E (Fin 0)) (first second : PathGeometryValid state) :
    toIndependentBondPathData state first = toIndependentBondPathData state second := by
  apply independentBondPathData_extEq <;> rfl

/-- Transport of the domain adapter along an equality of whole states, with independently supplied
validity proofs on both sides. -/
theorem toIndependentBondPathData_eq_of_state_eq
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    {state other : WholeState V E (Fin 0)}
    (equal : state = other) (valid : PathGeometryValid state)
    (otherValid : PathGeometryValid other) :
    toIndependentBondPathData state valid = toIndependentBondPathData other otherValid := by
  cases equal
  exact toIndependentBondPathData_valid_irrelevant state valid otherValid

/-! ## Lifting through the existing description encoder and decoder -/

namespace IndependentBondPathData

variable {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]

/-- Encode the constructed state through the actual domain encoder at the canonical `Fin`
schema.  The band index type is the encoded empty type. -/
noncomputable def toEncodedDescription (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E)) :
    EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card (Fin 0)) :=
  encodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
    data.toWholeState

/-- Decoding the encoded ingress recovers the constructed whole state exactly. -/
theorem decodeDescription_toEncodedDescription (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E)) :
    decodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
        (data.toEncodedDescription atomEnumeration edgeEnumeration) = data.toWholeState :=
  decodeDescription_encodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
    data.toWholeState

/-- The encoded graph is the common relabelling of the independent graph: the source is retained,
not replaced. -/
@[simp] theorem toEncodedDescription_graph (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E)) :
    (data.toEncodedDescription atomEnumeration edgeEnumeration).graph =
      relabelGraph atomEnumeration data.graph := rfl

/-- The encoded conformation is the common relabelling of the independent real conformation. -/
@[simp] theorem toEncodedDescription_conformation (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E)) :
    (data.toEncodedDescription atomEnumeration edgeEnumeration).conformation =
      MolecularConformation.reindex atomEnumeration data.conformation := rfl

/-- Every encoded path is the common relabelling of the independent path annotation; the arc is
retained literally. -/
@[simp] theorem toEncodedDescription_paths (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E)) (edge : E) :
    (data.toEncodedDescription atomEnumeration edgeEnumeration).paths (edgeEnumeration edge) =
      relabelPathAnnotation atomEnumeration (data.toPathAnnotation edge) := by
  unfold toEncodedDescription
  simp only [encodeDescription, relabelDescription, reindexBands, reindexEdges,
    relabelWholeState, Equiv.symm_apply_apply, toWholeState_paths]

end IndependentBondPathData

/-- Source preservation through the decode of the encoded ingress: the graph is the original
independent graph. -/
@[simp] theorem decodeDescription_toEncodedDescription_graph
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E)) :
    (decodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
        (data.toEncodedDescription atomEnumeration edgeEnumeration)).graph = data.graph := by
  rw [IndependentBondPathData.decodeDescription_toEncodedDescription]
  rfl

/-- Source preservation through the decode of the encoded ingress: the conformation is the
original independent real conformation. -/
@[simp] theorem decodeDescription_toEncodedDescription_conformation
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E)) :
    (decodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
        (data.toEncodedDescription atomEnumeration edgeEnumeration)).conformation =
      data.conformation := by
  rw [IndependentBondPathData.decodeDescription_toEncodedDescription]
  rfl

/-- Source preservation for the path channel: every decoded path is the original independent path
annotation at the corresponding physical edge. -/
@[simp] theorem decodeDescription_toEncodedDescription_paths
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E)) (edge : E) :
    (decodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
        (data.toEncodedDescription atomEnumeration edgeEnumeration)).paths edge =
      data.toPathAnnotation edge := by
  rw [IndependentBondPathData.decodeDescription_toEncodedDescription]
  rfl

/-- The domain adapter recovers the independent record even after the encode/decode lift: the
decoded state's validity proof is transported along the round-trip equality. -/
theorem toIndependentBondPathData_decodeDescription
    {V : Type*} [DecidableEq V] [Fintype V] {E : Type*} [Fintype E]
    (data : IndependentBondPathData V E)
    (atomEnumeration : V ≃ Fin (Fintype.card V))
    (edgeEnumeration : E ≃ Fin (Fintype.card E))
    (valid : PathGeometryValid
      (decodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
        (data.toEncodedDescription atomEnumeration edgeEnumeration))) :
    toIndependentBondPathData
        (decodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
          (data.toEncodedDescription atomEnumeration edgeEnumeration)) valid = data := by
  let decoded := decodeDescription atomEnumeration edgeEnumeration (Fintype.equivFin (Fin 0))
    (data.toEncodedDescription atomEnumeration edgeEnumeration)
  have roundtrip : decoded = data.toWholeState :=
    IndependentBondPathData.decodeDescription_toEncodedDescription data atomEnumeration
      edgeEnumeration
  let transported : PathGeometryValid data.toWholeState := roundtrip ▸ valid
  change toIndependentBondPathData decoded valid = data
  calc
    toIndependentBondPathData decoded valid
        = toIndependentBondPathData data.toWholeState transported :=
          toIndependentBondPathData_eq_of_state_eq roundtrip valid transported
    _ = data := toIndependentBondPathData_toWholeState data transported

end TetraStereo.OneCenter
