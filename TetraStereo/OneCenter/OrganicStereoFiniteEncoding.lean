import Mathlib.Data.Fintype.EquivFin
import TetraStereo.OneCenter.AuthoritativeChemicalInput

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Serialization of finite atom-labelled interaction hypergraphs

This module is the representation layer between an independently specified finite chemical graph
and the existing format-neutral `SemanticMolecule` / `AuthoritativeChemicalInput` types.  It does
not add a chemistry domain and it does not decide chemical admissibility: every ingredient below is
either a source field or a purely combinatorial mapping into the existing structures.

The source is an arbitrary finite atom type `V` together with

* `atomData : V → SemanticAtom` (element, isotope label, formal charge, unpaired electrons,
  aromatic input flag),
* an ordered list of hyperedges `List (List V × SemanticInteractionKind)`,
* the independent well-formedness assumptions `2 ≤ arity` and `Nodup` participants.

An explicit enumeration `V ≃ Fin (Fintype.card V)` chooses atom identities.  The encoding keeps
atom data literally, keeps interaction order and kind literally (including `.other` authority
codes), and maps each participant to its enumeration index.  The main results are exact lookup,
exact round-trip decoding, structural well-formedness of the resulting molecule and of the
certified authoritative input, and pointwise compatibility under a change of enumeration.

No bound is placed on atom, component, coordination, electron or bond-order counts, and no spatial
or diagram evidence is invented: `spatial?` and `diagram?` remain `none`.
-/

/-- An independently specified finite atom-labelled interaction hypergraph.  `atomData` supplies
the complete semantic atom record for each atom label; the interaction list is ordered and each
hyperedge carries an independent kind.  The two assumptions are deliberately separate from the
encoding so that well-formedness is a source property, not a property of serialization. -/
structure FiniteAtomInteractionHypergraph (V : Type*) [DecidableEq V] [Fintype V] where
  /-- Complete semantic data attached to each independent atom label. -/
  atomData : V → SemanticAtom
  /-- Ordered finite list of hyperedges.  Participant lists are atom labels, not indices. -/
  interactions : List (List V × SemanticInteractionKind)
  /-- Every hyperedge has at least two participants. -/
  arity_ge_two : ∀ edge ∈ interactions, 2 ≤ edge.1.length
  /-- Every hyperedge lists its participants without repetition. -/
  participants_nodup : ∀ edge ∈ interactions, edge.1.Nodup

namespace FiniteAtomInteractionHypergraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Bridge between the repository's local list lookup and core `getElem?`. -/
private theorem listGet?_eq_getElem? {α : Type*} (values : List α) (index : ℕ) :
    listGet? values index = values[index]? := by
  induction values generalizing index with
  | nil => simp [listGet?]
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => simpa [listGet?] using inductionHypothesis index

/-! ## Encoding -/

omit [DecidableEq V] in
/-- Map one source hyperedge into the index representation.  Only participant identities are
translated; the kind, including any `.other authorityCode`, is copied verbatim. -/
def encodeInteraction (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) : SemanticInteraction :=
  { participants := edge.1.map fun atom => (enumeration atom).val
    kind := edge.2 }

/-- Encode a finite atom-labelled interaction hypergraph as a `SemanticMolecule`.

The atom list is the enumeration order `0, …, card V - 1`, each entry carrying exactly the source
atom data at the corresponding label.  The interaction list is the source list with each
participant replaced by its enumeration index.  No atom, component, coordination or bond-order
bound is introduced. -/
def encode (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) : SemanticMolecule :=
  { atoms := List.ofFn fun index => source.atomData (enumeration.symm index)
    interactions := source.interactions.map (encodeInteraction enumeration) }

/-- Successful encoding preserves the atom count exactly: it is the cardinality of the source atom
type, whatever that cardinality is. -/
@[simp] theorem encode_atomCount (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encode enumeration).atomCount = Fintype.card V := by
  simp [SemanticMolecule.atomCount, encode]

/-- Exact atom lookup.  At every in-range index the encoded molecule returns precisely the source
atom data at the label named by that index.  In particular isotope label, formal charge, unpaired
electron count and aromatic input are not reinterpreted. -/
theorem encode_atomAt (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card V)) :
    listGet? (source.encode enumeration).atoms index.val =
      some (source.atomData (enumeration.symm index)) := by
  unfold encode
  rw [listGet?_eq_getElem?]
  have bound : index.val <
      (List.ofFn fun index => source.atomData (enumeration.symm index)).length := by
    rw [List.length_ofFn]
    exact index.isLt
  rw [List.getElem?_eq_getElem bound]
  simp

/-- Field-level form of `encode_atomAt`: every semantic atom component is preserved exactly. -/
theorem encode_atom_fields (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card V)) :
    ∃ atom : SemanticAtom,
      listGet? (source.encode enumeration).atoms index.val = some atom ∧
        atom.element = (source.atomData (enumeration.symm index)).element ∧
        atom.isotopeMassNumber? =
          (source.atomData (enumeration.symm index)).isotopeMassNumber? ∧
        atom.formalCharge = (source.atomData (enumeration.symm index)).formalCharge ∧
        atom.unpairedElectrons =
          (source.atomData (enumeration.symm index)).unpairedElectrons ∧
        atom.aromaticInput = (source.atomData (enumeration.symm index)).aromaticInput := by
  exact ⟨_, source.encode_atomAt enumeration index, rfl, rfl, rfl, rfl, rfl⟩

/-- Encoding preserves the interaction list length exactly. -/
@[simp] theorem encode_interactions_length (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encode enumeration).interactions.length = source.interactions.length := by
  simp [encode]

/-- Exact interaction lookup, including order and kind.  The interaction at source position `k` is
exactly the mapped source hyperedge at position `k`. -/
theorem encode_interactionAt (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (index : ℕ)
    (bound : index < source.interactions.length) :
    listGet? (source.encode enumeration).interactions index =
      some (encodeInteraction enumeration (source.interactions.get ⟨index, bound⟩)) := by
  unfold encode
  rw [listGet?_eq_getElem?]
  have mappedBound : index <
      (source.interactions.map (encodeInteraction enumeration)).length := by
    rw [List.length_map]
    exact bound
  rw [List.getElem?_eq_getElem mappedBound, List.getElem_map]
  rfl

omit [DecidableEq V] in
/-- Exact participant incidence: at each position of an encoded hyperedge one finds precisely the
enumeration index of the source participant at the same position. -/
theorem encode_participantAt (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) (position : ℕ) :
    listGet? (encodeInteraction enumeration edge).participants position =
      (listGet? edge.1 position).map fun atom => (enumeration atom).val := by
  unfold encodeInteraction
  rw [listGet?_eq_getElem?, List.getElem?_map, ← listGet?_eq_getElem?]

/-- At the list level, participant incidence is the pointwise enumeration of the source
participants; no other information is used. -/
theorem encode_participants_list (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encode enumeration).interactions.map SemanticInteraction.participants =
      source.interactions.map
        (fun edge => edge.1.map fun atom => (enumeration atom).val) := by
  rw [show (source.encode enumeration).interactions =
        source.interactions.map (encodeInteraction enumeration) from rfl,
    List.map_map]
  rfl

/-- Encoding preserves the ordered list of interaction kinds exactly.  This is why a source with no
`.other` edge cannot acquire one: `.other` codes are copied, never interpreted. -/
theorem encode_interactionKinds (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encode enumeration).interactions.map SemanticInteraction.kind =
      source.interactions.map (fun edge => edge.2) := by
  rw [show (source.encode enumeration).interactions =
        source.interactions.map (encodeInteraction enumeration) from rfl,
    List.map_map]
  rfl

/-! ## Well-formedness -/

omit [DecidableEq V] in
/-- Each source hyperedge encodes to a structurally well-formed semantic interaction: arity and
participant distinctness come from the independent source assumptions, and every index is in
range because the enumeration targets `Fin (card V)`. -/
theorem encodeInteraction_wellFormed (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind)
    (arity : 2 ≤ edge.1.length) (nodup : edge.1.Nodup) :
    (encodeInteraction enumeration edge).WellFormed (Fintype.card V) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [encodeInteraction] using arity
  · exact nodup.map (fun first second equal => enumeration.injective (Fin.ext equal))
  · rw [show (encodeInteraction enumeration edge).participants =
          edge.1.map (fun atom => (enumeration atom).val) from rfl,
      List.all_map]
    exact List.all_eq_true.mpr (fun atom _ => decide_eq_true (enumeration atom).isLt)

/-- The encoded molecule is structurally well-formed for every finite source and every explicit
enumeration.  This is a theorem, not a hypothesis of the encoding. -/
theorem encode_structurallyWellFormed (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encode enumeration).StructurallyWellFormed := by
  unfold SemanticMolecule.StructurallyWellFormed
  unfold encode
  simp only [SemanticMolecule.atomCount, List.length_ofFn]
  rw [List.all_map]
  exact List.all_eq_true.mpr fun edge membership =>
    (SemanticInteraction.wellFormed?_eq_true_iff _ _).mpr
      (encodeInteraction_wellFormed enumeration edge
        (source.arity_ge_two edge membership)
        (source.participants_nodup edge membership))

/-! ## Certified authoritative input

The encoding uses only the molecule channel.  Spatial and diagram evidence are deliberately left
absent; this module does not invent geometry and does not depend on any geometry- or
localized-CIP-readiness predicate. -/

/-- Encode the source as a full `AuthoritativeChemicalInput` with no spatial or diagram channel. -/
def encodeAuthoritative (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) : AuthoritativeChemicalInput :=
  { molecule := source.encode enumeration }

@[simp] theorem encodeAuthoritative_molecule (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encodeAuthoritative enumeration).molecule = source.encode enumeration := rfl

@[simp] theorem encodeAuthoritative_spatial? (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encodeAuthoritative enumeration).spatial? = none := rfl

@[simp] theorem encodeAuthoritative_diagram? (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encodeAuthoritative enumeration).diagram? = none := rfl

/-- The encoded authoritative input satisfies the existing structural certificate. -/
theorem encodeAuthoritative_structurallyWellFormed
    (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.encodeAuthoritative enumeration).StructurallyWellFormed :=
  ⟨source.encode_structurallyWellFormed enumeration, trivial, trivial⟩

/-- The constructive certificate for the encoded input. -/
def certifiedEncoding (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) : CertifiedAuthoritativeChemicalInput :=
  { input := source.encodeAuthoritative enumeration
    structurallyWellFormed := source.encodeAuthoritative_structurallyWellFormed enumeration }

@[simp] theorem certifiedEncoding_input (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (source.certifiedEncoding enumeration).input = source.encodeAuthoritative enumeration := rfl

/-- Exact atom lookup survives the certified wrapper. -/
theorem certifiedEncoding_atomAt (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card V)) :
    listGet? (source.certifiedEncoding enumeration).input.molecule.atoms index.val =
      some (source.atomData (enumeration.symm index)) :=
  source.encode_atomAt enumeration index

/-- Exact interaction lookup survives the certified wrapper. -/
theorem certifiedEncoding_interactionAt (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (index : ℕ)
    (bound : index < source.interactions.length) :
    listGet? (source.certifiedEncoding enumeration).input.molecule.interactions index =
      some (encodeInteraction enumeration (source.interactions.get ⟨index, bound⟩)) :=
  source.encode_interactionAt enumeration index bound

/-! ## Decoding and round trip -/

omit [DecidableEq V] in
/-- Decode one enumeration index back to an independent atom label.  Indices outside the finite
range have no label. -/
def decodeIndex? (enumeration : V ≃ Fin (Fintype.card V)) (index : ℕ) : Option V :=
  if bound : index < Fintype.card V then some (enumeration.symm ⟨index, bound⟩) else none

omit [DecidableEq V] in
/-- Decoding the index of a source label recovers that label exactly. -/
theorem decodeIndex?_encode (enumeration : V ≃ Fin (Fintype.card V)) (atom : V) :
    decodeIndex? enumeration (enumeration atom).val = some atom := by
  unfold decodeIndex?
  rw [dif_pos (enumeration atom).isLt]
  simp

omit [DecidableEq V] in
/-- Decode a semantic participant list back to independent atom labels. -/
def decodeParticipants? (enumeration : V ≃ Fin (Fintype.card V))
    (interaction : SemanticInteraction) : Option (List V) :=
  interaction.participants.mapM (decodeIndex? enumeration)

omit [DecidableEq V] in
/-- Decoding is a left inverse of the enumeration map on any source participant list. -/
theorem mapM_decodeIndex?_map_enumeration (enumeration : V ≃ Fin (Fintype.card V))
    (values : List V) :
    (values.map fun atom => (enumeration atom).val).mapM (decodeIndex? enumeration) =
      some values := by
  induction values with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      simp [decodeIndex?_encode, inductionHypothesis]

omit [DecidableEq V] in
/-- Participant round trip: decoding the encoded participants recovers the source participant list
exactly, including order and multiplicity. -/
theorem decodeParticipants?_encodeInteraction (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) :
    decodeParticipants? enumeration (encodeInteraction enumeration edge) = some edge.1 := by
  obtain ⟨participants, kind⟩ := edge
  exact mapM_decodeIndex?_map_enumeration enumeration participants

omit [DecidableEq V] in
/-- Decode a whole semantic interaction to an independent source hyperedge. -/
def decodeInteraction? (enumeration : V ≃ Fin (Fintype.card V))
    (interaction : SemanticInteraction) : Option (List V × SemanticInteractionKind) :=
  (decodeParticipants? enumeration interaction).map fun participants =>
    (participants, interaction.kind)

omit [DecidableEq V] in
/-- Interaction round trip: decoding an encoded interaction recovers the source hyperedge,
participants and kind alike. -/
theorem decodeInteraction?_encodeInteraction (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) :
    decodeInteraction? enumeration (encodeInteraction enumeration edge) = some edge := by
  obtain ⟨participants, kind⟩ := edge
  unfold decodeInteraction?
  rw [decodeParticipants?_encodeInteraction]
  simp [encodeInteraction]

omit [DecidableEq V] in
/-- Decode an ordered list of semantic interactions. -/
def decodeInteractions? (enumeration : V ≃ Fin (Fintype.card V))
    (molecule : SemanticMolecule) : Option (List (List V × SemanticInteractionKind)) :=
  molecule.interactions.mapM (decodeInteraction? enumeration)

/-- Whole-list round trip: decoding the encoded interaction list recovers the source list exactly,
so order, arity and kind are all retained. -/
theorem decodeInteractions?_encode (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    decodeInteractions? enumeration (source.encode enumeration) = some source.interactions := by
  unfold decodeInteractions?
  rw [show (source.encode enumeration).interactions =
        source.interactions.map (encodeInteraction enumeration) from rfl]
  induction source.interactions with
  | nil => rfl
  | cons edge edges inductionHypothesis =>
      simp [decodeInteraction?_encodeInteraction, inductionHypothesis]

omit [DecidableEq V] in
/-- Decode one atom position back to its independent source label.  The semantic atom data stored
there is then the source `atomData` at that label, by `encode_atomAt`. -/
def decodeAtomLabel? (enumeration : V ≃ Fin (Fintype.card V))
    (molecule : SemanticMolecule) (index : ℕ) : Option V :=
  (listGet? molecule.atoms index).bind fun _ => decodeIndex? enumeration index

/-- Atom-label round trip at every encoded position. -/
theorem decodeAtomLabel?_encode (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card V)) :
    decodeAtomLabel? enumeration (source.encode enumeration) index.val =
      some (enumeration.symm index) := by
  unfold decodeAtomLabel?
  rw [source.encode_atomAt enumeration index]
  rw [Option.bind_some]
  unfold decodeIndex?
  rw [dif_pos index.isLt]

omit [DecidableEq V] in
/-- Decode the full ordered atom-label list.  The length guard is exactly the source cardinality,
so malformed atom lists are rejected rather than reinterpreted. -/
def decodeAtomLabels? (enumeration : V ≃ Fin (Fintype.card V))
    (molecule : SemanticMolecule) : Option (List V) :=
  if molecule.atomCount = Fintype.card V then
    some (List.ofFn fun index => enumeration.symm index)
  else none

/-- Whole-list atom-label round trip: the decoded label list is exactly the enumeration of the
source atom type. -/
theorem decodeAtomLabels?_encode (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    decodeAtomLabels? enumeration (source.encode enumeration) =
      some (List.ofFn fun index => enumeration.symm index) := by
  unfold decodeAtomLabels?
  rw [if_pos (source.encode_atomCount enumeration)]

/-! ## Compatibility under a change of enumeration -/

/-- Changing the enumeration only permutes atom identities.  The atom found at index `i` under
one enumeration is the atom found at the corresponding permuted index under another, with the
relabelling permutation `second.symm.trans first`. -/
theorem encode_atomAt_relabel (source : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card V)) :
    listGet? (source.encode second).atoms index.val =
      listGet? (source.encode first).atoms ((second.symm.trans first) index).val := by
  rw [source.encode_atomAt second index,
    source.encode_atomAt first ((second.symm.trans first) index)]
  simp

/-- At a fixed source atom the encoded atom data is independent of the enumeration; only the index
at which it appears changes. -/
theorem encode_atomData_relabel (source : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (atom : V) :
    listGet? (source.encode second).atoms (second atom).val = some (source.atomData atom) ∧
      listGet? (source.encode first).atoms (first atom).val = some (source.atomData atom) := by
  constructor
  · rw [source.encode_atomAt second (second atom)]
    simp
  · rw [source.encode_atomAt first (first atom)]
    simp

omit [DecidableEq V] in
/-- Pointwise participant relabelling: for a source participant at a given position, the encoded
participant value is its enumeration index in either representation, and the two indices are
related by `second.symm.trans first`.  Only identities move; incidence is unchanged. -/
theorem encode_participantAt_relabel (edge : List V × SemanticInteractionKind)
    (first second : V ≃ Fin (Fintype.card V)) (position : ℕ) (atom : V)
    (lookup : listGet? edge.1 position = some atom) :
    listGet? (encodeInteraction second edge).participants position =
        some (second atom).val ∧
      listGet? (encodeInteraction first edge).participants position =
        some (first atom).val ∧
      ((second.symm.trans first) (second atom)).val = (first atom).val := by
  refine ⟨?_, ?_, ?_⟩
  · rw [encode_participantAt second edge position, lookup]
    rfl
  · rw [encode_participantAt first edge position, lookup]
    rfl
  · simp

/-! ## Absence of interpreted authority strings -/

/-- The source has no `.other` interaction kind if no authority code is ever used. -/
def HasNoOtherKind (source : FiniteAtomInteractionHypergraph V) : Prop :=
  ∀ edge ∈ source.interactions, ∀ authorityCode : String,
    edge.2 ≠ SemanticInteractionKind.other authorityCode

/-- If the source uses no `.other` kind, the encoding uses no `.other` kind either: kinds are
copied verbatim and authority strings are never interpreted as chemistry. -/
theorem encode_no_other (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (noOther : source.HasNoOtherKind) :
    ∀ interaction ∈ (source.encode enumeration).interactions,
      ∀ authorityCode : String,
        interaction.kind ≠ SemanticInteractionKind.other authorityCode := by
  intro interaction membership authorityCode
  rw [show (source.encode enumeration).interactions =
        source.interactions.map (encodeInteraction enumeration) from rfl] at membership
  obtain ⟨edge, edgeMembership, equality⟩ := List.mem_map.mp membership
  rw [← equality]
  exact noOther edge edgeMembership authorityCode

/-! ## Noncomputable convenience -/

/-- The canonical noncomputable enumeration.  Every theorem above is stated for an explicit
equivalence; this is only a convenience for callers that accept a chosen enumeration. -/
noncomputable def canonicalEnumeration (V : Type*) [Fintype V] :
    V ≃ Fin (Fintype.card V) :=
  Fintype.equivFin V

/-- Encode using the canonical noncomputable enumeration. -/
noncomputable def encodeCanonical (source : FiniteAtomInteractionHypergraph V) :
    SemanticMolecule :=
  source.encode (canonicalEnumeration V)

/-- Certified encoding using the canonical noncomputable enumeration. -/
noncomputable def certifiedEncodingCanonical
    (source : FiniteAtomInteractionHypergraph V) : CertifiedAuthoritativeChemicalInput :=
  source.certifiedEncoding (canonicalEnumeration V)

end FiniteAtomInteractionHypergraph

end TetraStereo.OneCenter
