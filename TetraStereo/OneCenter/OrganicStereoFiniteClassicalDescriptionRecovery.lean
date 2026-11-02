import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription
import TetraStereo.OneCenter.OrganicStereoCorrelatedInformation

set_option autoImplicit false

namespace TetraStereo.OneCenter

open IUPACDrawing2006.ST6

noncomputable section

/-!
# Recovery of correlated finite classical stereo information

This module instantiates the repository's correlated-information carrier
`OrganicStereoCorrelatedInformation.CorrelatedInformation` at the whole-state type
`FiniteClassicalStereoDescription V E B` (a `WholeState V E B`).  A value stores

* the retained IUPAC `ConfigurationKnowledge` tag,
* the retained configuration-scope summary,
* one joint set `possible : Set (FiniteClassicalStereoDescription V E B)` of **entire** whole
  states, never a product of per-channel marginals, and
* the retained optional `DiagramConfiguration`, exactly as in the generic carrier.

Encoding and decoding of information use only the domain's public whole-record operations
`encodeDescription`, `decodeDescription`, `relabelDescription`, `relabelWholeState`,
`encodeDescriptionSet` and their two proved inverse laws.  The encoded payload carries no
`V`-labelled original source and no original description: decoding needs only the externally
supplied equivalences and the encoded record.  Because each `WholeState` carries every data
channel -- including the drawing channel, the specialist fragment, convention and cage annotation
ledgers and the optional residue-link/naming-hierarchy ledger -- and the whole state is moved as
one unit, no channel is dropped by the information transport.

## Scope

The recovered channels are exactly the fields of the current `WholeState` record: the atom
interaction hypergraph, the optional supplied electronic inventory with its unpaired-count tie, the
single shared real conformation, optional exact rational provenance, the ordered role ledger, the
bond-path family, the band attachment family with its agreement, optional source drawing data,
optional sparse partial positions, the sparse raw incidence ledger, and the ordered specialist
annotation channels (residue/fragment annotations, drawing conventions and numbered cage/face
annotations) and the optional specialist residue-link/naming-hierarchy ledger.  Decoding recovers the original whole state exactly, field by
field (the `decodeDescription_encodeDescription_*` corollaries below), so no channel is projected
out and the encoded payload never stores the original `V`-labelled source.  The specialist
annotation payload types are owned by their own modules; this module neither redefines nor assumes
them, it only proves that whole-state transport moves them unchanged.  No claim is made that these
current fields exhaust organic chemistry, and no CIP descriptor, chemical truth or completeness
result is asserted here.

## Consistency

An empty `possible` set is representable and means inconsistent evidence.  `Consistent` is
nonemptiness of `possible`; it is never derived from the knowledge tag.  Nonemptiness, exact
membership and both whole-set recovery laws are stated for an arbitrary set of whole states.
-/

variable {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]

/-- Concrete correlated information over complete finite classical whole states.  `possible` is one
set of entire whole states. -/
abbrev FiniteClassicalInformation (V E B : Type*) [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] :=
  CorrelatedInformation (FiniteClassicalStereoDescription V E B)

namespace FiniteClassicalInformation

/-! ## Constructors and the adapter to `CorrelatedInformation` -/

/-- Information specified by a knowledge tag and one joint set of whole states.  The scope summary is
empty and no separate `DiagramConfiguration` is attached; the whole states may still carry their own
source drawing data. -/
def ofStates (knowledge : ConfigurationKnowledge)
    (possible : Set (FiniteClassicalStereoDescription V E B)) :
    FiniteClassicalInformation V E B :=
  { knowledge := knowledge
    scopes := []
    possible := possible
    diagram? := none }

@[simp] theorem ofStates_knowledge (knowledge : ConfigurationKnowledge)
    (possible : Set (FiniteClassicalStereoDescription V E B)) :
    (ofStates knowledge possible).knowledge = knowledge := rfl

@[simp] theorem ofStates_scopes (knowledge : ConfigurationKnowledge)
    (possible : Set (FiniteClassicalStereoDescription V E B)) :
    (ofStates knowledge possible).scopes = [] := rfl

@[simp] theorem ofStates_possible (knowledge : ConfigurationKnowledge)
    (possible : Set (FiniteClassicalStereoDescription V E B)) :
    (ofStates knowledge possible).possible = possible := rfl

@[simp] theorem ofStates_diagram? (knowledge : ConfigurationKnowledge)
    (possible : Set (FiniteClassicalStereoDescription V E B)) :
    (ofStates knowledge possible).diagram? = none := rfl

/-- The concrete information carrier is literally the repository's correlated-information carrier
at the whole-state type.  This identity adapter retains the knowledge tag, the scope summary, the
joint possible set and the optional attached diagram. -/
def toCorrelatedInformation (info : FiniteClassicalInformation V E B) :
    CorrelatedInformation (FiniteClassicalStereoDescription V E B) :=
  info

/-- Inverse of the identity adapter. -/
def ofCorrelatedInformation
    (info : CorrelatedInformation (FiniteClassicalStereoDescription V E B)) :
    FiniteClassicalInformation V E B :=
  info

@[simp] theorem ofCorrelatedInformation_toCorrelatedInformation
    (info : FiniteClassicalInformation V E B) :
    ofCorrelatedInformation (toCorrelatedInformation info) = info := rfl

@[simp] theorem toCorrelatedInformation_ofCorrelatedInformation
    (info : CorrelatedInformation (FiniteClassicalStereoDescription V E B)) :
    toCorrelatedInformation (ofCorrelatedInformation info) = info := rfl

/-! ## Consistency is explicit -/

/-- Consistency is exactly nonemptiness of the joint possible set. -/
theorem consistent_iff_possible_nonempty (info : FiniteClassicalInformation V E B) :
    info.Consistent ↔ info.possible.Nonempty :=
  CorrelatedInformation.consistent_iff info

/-- Inconsistency is exactly an empty joint possible set. -/
theorem not_consistent_iff_possible_empty (info : FiniteClassicalInformation V E B) :
    ¬ info.Consistent ↔ info.possible = ∅ := by
  rw [consistent_iff_possible_nonempty, Set.not_nonempty_iff_eq_empty]

/-- A recorded whole state certifies consistency. -/
theorem consistent_of_mem (info : FiniteClassicalInformation V E B)
    {state : FiniteClassicalStereoDescription V E B} (member : state ∈ info.possible) :
    info.Consistent := by
  rw [consistent_iff_possible_nonempty]
  exact ⟨state, member⟩

/-- Inconsistent information: the joint possible set is empty.  This is a genuine value, distinct
from missing information, and no physical fact is certified from it. -/
def inconsistentInformation (knowledge : ConfigurationKnowledge) :
    FiniteClassicalInformation V E B :=
  ofStates knowledge ∅

@[simp] theorem inconsistentInformation_knowledge (knowledge : ConfigurationKnowledge) :
    (inconsistentInformation (V := V) (E := E) (B := B) knowledge).knowledge = knowledge := rfl

@[simp] theorem inconsistentInformation_possible (knowledge : ConfigurationKnowledge) :
    (inconsistentInformation (V := V) (E := E) (B := B) knowledge).possible = ∅ := rfl

theorem inconsistentInformation_not_consistent (knowledge : ConfigurationKnowledge) :
    ¬ (inconsistentInformation (V := V) (E := E) (B := B) knowledge).Consistent :=
  CorrelatedInformation.not_consistent_of_possible_eq_empty
    (inconsistentInformation (V := V) (E := E) (B := B) knowledge) rfl

theorem inconsistentInformation_consistent_iff_false (knowledge : ConfigurationKnowledge) :
    (inconsistentInformation (V := V) (E := E) (B := B) knowledge).Consistent ↔ False := by
  rw [consistent_iff_possible_nonempty, inconsistentInformation_possible]
  simp

/-- Every retained knowledge tag is one of the eight declared tags. -/
theorem knowledge_mem_allKnowledgeStates (info : FiniteClassicalInformation V E B) :
    info.knowledge ∈ allKnowledgeStates :=
  CorrelatedInformation.knowledge_mem_allKnowledgeStates info.knowledge

/-! ## Encoding and decoding whole-state information

The forward map is the domain's `encodeDescription` and the inverse is the domain's
`decodeDescription`; both inverse laws are the domain's proved theorems, not assumptions. -/

/-- The whole-state equivalence induced by the three externally supplied enumerations. -/
def descriptionEquiv (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B)) :
    FiniteClassicalStereoDescription V E B ≃
      EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B) where
  toFun := encodeDescription eV eE eB
  invFun := decodeDescription eV eE eB
  left_inv := decodeDescription_encodeDescription eV eE eB
  right_inv := encodeDescription_decodeDescription eV eE eB

@[simp] theorem descriptionEquiv_apply (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    descriptionEquiv eV eE eB description = encodeDescription eV eE eB description := rfl

@[simp] theorem descriptionEquiv_symm_apply (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    (descriptionEquiv eV eE eB).symm encoded = decodeDescription eV eE eB encoded := rfl

/-- Encode correlated information along the whole-state encoding.  Knowledge, scopes and the
attached diagram are unchanged; the joint possible set is moved to its exact whole-state image. -/
def encodeInformation (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B)) :=
  info.transport (descriptionEquiv eV eE eB)

/-- Decode correlated information using only the three equivalences and the encoded payload.  No
original description and no `V`-labelled source is required or available. -/
def decodeInformation (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    FiniteClassicalInformation V E B :=
  info.transport (descriptionEquiv eV eE eB).symm

/-! ## Knowledge and metadata preservation -/

@[simp] theorem encodeInformation_knowledge (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (encodeInformation eV eE eB info).knowledge = info.knowledge := by
  rfl

@[simp] theorem encodeInformation_scopes (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (encodeInformation eV eE eB info).scopes = info.scopes := by
  rfl

@[simp] theorem encodeInformation_diagram? (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (encodeInformation eV eE eB info).diagram? = info.diagram? := by
  rfl

/-- Encoding preserves knowledge tag, scope summary and attached diagram together. -/
theorem encodeInformation_metadata (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (encodeInformation eV eE eB info).knowledge = info.knowledge ∧
      (encodeInformation eV eE eB info).scopes = info.scopes ∧
      (encodeInformation eV eE eB info).diagram? = info.diagram? :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem decodeInformation_knowledge (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeInformation eV eE eB info).knowledge = info.knowledge := by
  rfl

@[simp] theorem decodeInformation_scopes (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeInformation eV eE eB info).scopes = info.scopes := by
  rfl

@[simp] theorem decodeInformation_diagram? (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeInformation eV eE eB info).diagram? = info.diagram? := by
  rfl

/-- Decoding preserves knowledge tag, scope summary and attached diagram together. -/
theorem decodeInformation_metadata (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeInformation eV eE eB info).knowledge = info.knowledge ∧
      (decodeInformation eV eE eB info).scopes = info.scopes ∧
      (decodeInformation eV eE eB info).diagram? = info.diagram? :=
  ⟨rfl, rfl, rfl⟩

/-! ## Exact joint possible sets

`possible` is always one set of entire whole states.  The encoded set is exactly its image under
the domain's whole-state encoding, and the decoded set is exactly its image under the inverse. -/

/-- The encoded joint possible set is exactly the image of the original set under the whole-state
encoding.  It is one set of entire states, not a product of per-channel marginals. -/
theorem encodeInformation_possible (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (encodeInformation eV eE eB info).possible =
      descriptionEquiv eV eE eB '' info.possible := by
  rfl

/-- The encoded joint possible set is exactly the domain's `encodeDescriptionSet`. -/
theorem encodeInformation_possible_eq_encodeDescriptionSet
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (info : FiniteClassicalInformation V E B) :
    (encodeInformation eV eE eB info).possible =
      encodeDescriptionSet eV eE eB info.possible := by
  rw [encodeInformation_possible]
  rfl

/-- The decoded joint possible set is exactly the image of the encoded set under decoding. -/
theorem decodeInformation_possible (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeInformation eV eE eB info).possible =
      (descriptionEquiv eV eE eB).symm '' info.possible := by
  rfl

/-- Whole-set recovery law for the encoded information, stated at the level of the domain's
decoder: decoding the encoded joint possible set gives back exactly the original set.  This holds
for an arbitrary set of whole states. -/
theorem decodeDescription_image_encodeInformation_possible
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (info : FiniteClassicalInformation V E B) :
    decodeDescription eV eE eB '' (encodeInformation eV eE eB info).possible =
      info.possible := by
  rw [encodeInformation_possible_eq_encodeDescriptionSet,
    decodeDescription_image_encodeDescriptionSet]

/-- Whole-set recovery law for the decoded information: encoding the decoded joint possible set
gives back exactly the encoded original set.  This holds for an arbitrary set of encoded states. -/
theorem encodeDescription_image_decodeInformation_possible
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    encodeDescription eV eE eB '' (decodeInformation eV eE eB info).possible =
      info.possible := by
  rw [decodeInformation_possible, Set.image_image]
  have h : (encodeDescription eV eE eB ∘ (descriptionEquiv eV eE eB).symm) = id := by
    funext encoded
    exact encodeDescription_decodeDescription eV eE eB encoded
  change (encodeDescription eV eE eB ∘ (descriptionEquiv eV eE eB).symm) '' info.possible =
    info.possible
  rw [h, Set.image_id]

/-- Exact whole-set membership equivalence: an encoded state is jointly possible exactly when the
whole state obtained from it by the domain's decoder is jointly possible. -/
theorem mem_encodeInformation_possible_iff (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B)
    (state : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    state ∈ (encodeInformation eV eE eB info).possible ↔
      decodeDescription eV eE eB state ∈ info.possible := by
  rw [encodeInformation_possible, Set.mem_image]
  constructor
  · rintro ⟨original, member, mapped⟩
    have mapped' : encodeDescription eV eE eB original = state := mapped
    rw [← mapped', decodeDescription_encodeDescription]
    exact member
  · intro member
    exact ⟨decodeDescription eV eE eB state, member,
      encodeDescription_decodeDescription eV eE eB state⟩

/-- Exact whole-set membership equivalence in the decoding direction. -/
theorem mem_decodeInformation_possible_iff (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B)))
    (state : FiniteClassicalStereoDescription V E B) :
    state ∈ (decodeInformation eV eE eB info).possible ↔
      encodeDescription eV eE eB state ∈ info.possible := by
  rw [decodeInformation_possible, Set.mem_image]
  constructor
  · rintro ⟨original, member, mapped⟩
    have mapped' : decodeDescription eV eE eB original = state := mapped
    rw [← mapped', encodeDescription_decodeDescription]
    exact member
  · intro member
    exact ⟨encodeDescription eV eE eB state, member,
      decodeDescription_encodeDescription eV eE eB state⟩

/-- Membership of the image of an original whole state in the encoded joint possible set is
exactly original membership. -/
theorem mem_encodeInformation_possible_source_iff (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B)
    (state : FiniteClassicalStereoDescription V E B) :
    encodeDescription eV eE eB state ∈ (encodeInformation eV eE eB info).possible ↔
      state ∈ info.possible := by
  rw [mem_encodeInformation_possible_iff, decodeDescription_encodeDescription]

/-- Membership of a decoded encoded state in the decoded joint possible set is exactly membership
of the encoded state in the encoded set. -/
theorem mem_decodeInformation_possible_encoded_iff (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B)))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    (descriptionEquiv eV eE eB).symm encoded ∈
        (decodeInformation eV eE eB info).possible ↔
      encoded ∈ info.possible := by
  rw [decodeInformation_possible, Set.mem_image]
  constructor
  · rintro ⟨original, member, mapped⟩
    have : original = encoded := by
      have injective := congrArg (descriptionEquiv eV eE eB) mapped
      simpa [descriptionEquiv_apply, descriptionEquiv_symm_apply,
        encodeDescription_decodeDescription] using injective
    rw [← this]
    exact member
  · intro member
    exact ⟨encoded, member, rfl⟩

/-- Nonemptiness of the joint possible set is preserved exactly by encoding. -/
theorem encodeInformation_possible_nonempty_iff (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (encodeInformation eV eE eB info).possible.Nonempty ↔ info.possible.Nonempty := by
  rw [encodeInformation_possible]
  constructor
  · rintro ⟨state, member⟩
    rw [Set.mem_image] at member
    obtain ⟨original, originalMember, _⟩ := member
    exact ⟨original, originalMember⟩
  · rintro ⟨original, member⟩
    exact ⟨descriptionEquiv eV eE eB original, by
      rw [Set.mem_image]
      exact ⟨original, member, rfl⟩⟩

/-- Nonemptiness of the joint possible set is preserved exactly by decoding. -/
theorem decodeInformation_possible_nonempty_iff (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeInformation eV eE eB info).possible.Nonempty ↔ info.possible.Nonempty := by
  rw [decodeInformation_possible]
  constructor
  · rintro ⟨state, member⟩
    rw [Set.mem_image] at member
    obtain ⟨original, originalMember, _⟩ := member
    exact ⟨original, originalMember⟩
  · rintro ⟨original, member⟩
    exact ⟨(descriptionEquiv eV eE eB).symm original, by
      rw [Set.mem_image]
      exact ⟨original, member, rfl⟩⟩

/-! ## Both round trips -/

/-- Decoding an encoded information recovers it exactly, including the joint possible set. -/
theorem decodeInformation_encodeInformation (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    decodeInformation eV eE eB (encodeInformation eV eE eB info) = info := by
  unfold decodeInformation encodeInformation
  exact CorrelatedInformation.transport_symm_transport (descriptionEquiv eV eE eB) info

/-- Encoding a decoded information recovers it exactly, including the joint possible set. -/
theorem encodeInformation_decodeInformation (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    encodeInformation eV eE eB (decodeInformation eV eE eB info) = info := by
  unfold decodeInformation encodeInformation
  exact CorrelatedInformation.transport_transport_symm (descriptionEquiv eV eE eB) info

/-- The possible set is recovered exactly by the decode-after-encode pipeline. -/
theorem decodeInformation_encodeInformation_possible
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (info : FiniteClassicalInformation V E B) :
    (decodeInformation eV eE eB (encodeInformation eV eE eB info)).possible =
      info.possible := by
  rw [decodeInformation_encodeInformation]

/-- The possible set is recovered exactly by the encode-after-decode pipeline. -/
theorem encodeInformation_decodeInformation_possible
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (encodeInformation eV eE eB (decodeInformation eV eE eB info)).possible =
      info.possible := by
  rw [encodeInformation_decodeInformation]

/-! ## Consistency is preserved in both directions -/

/-- Encoding preserves consistency exactly: the encoded evidence is nonempty iff the original is. -/
theorem encodeInformation_consistent_iff (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (encodeInformation eV eE eB info).Consistent ↔ info.Consistent := by
  rw [consistent_iff_possible_nonempty, encodeInformation_possible_nonempty_iff,
    consistent_iff_possible_nonempty]

/-- Decoding preserves consistency exactly. -/
theorem decodeInformation_consistent_iff (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeInformation eV eE eB info).Consistent ↔ info.Consistent := by
  rw [consistent_iff_possible_nonempty, decodeInformation_possible_nonempty_iff,
    consistent_iff_possible_nonempty]

/-- Inconsistent evidence remains exactly inconsistent after encoding: the empty set is preserved. -/
theorem encodeInformation_possible_empty (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) (empty : info.possible = ∅) :
    (encodeInformation eV eE eB info).possible = ∅ := by
  rw [encodeInformation_possible, empty, Set.image_empty]

/-- Inconsistent evidence remains exactly inconsistent after decoding: the empty set is preserved. -/
theorem decodeInformation_possible_empty (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B)))
    (empty : info.possible = ∅) :
    (decodeInformation eV eE eB info).possible = ∅ := by
  rw [decodeInformation_possible, empty, Set.image_empty]

/-! ## Enumeration independence

The encoding type is the same `Fin`-schema for every choice of enumerations.  The recovered
information (knowledge, scopes, attached diagram and the entire joint possible set) is literally
the original information for every enumeration.  This is the sense in which the recovered
description does not depend on the enumeration chosen. -/

/-- The information recovered by the encode-then-decode pipeline is independent of the choice of
atom, edge and band enumerations. -/
theorem decode_encode_independent_of_enumerations
    (eV₁ eV₂ : V ≃ Fin (Fintype.card V))
    (eE₁ eE₂ : E ≃ Fin (Fintype.card E))
    (eB₁ eB₂ : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    decodeInformation eV₁ eE₁ eB₁ (encodeInformation eV₁ eE₁ eB₁ info) =
      decodeInformation eV₂ eE₂ eB₂ (encodeInformation eV₂ eE₂ eB₂ info) := by
  rw [decodeInformation_encodeInformation, decodeInformation_encodeInformation]

/-- The recovered joint possible set is independent of the choice of enumerations. -/
theorem recovered_possible_independent_of_enumerations
    (eV₁ eV₂ : V ≃ Fin (Fintype.card V))
    (eE₁ eE₂ : E ≃ Fin (Fintype.card E))
    (eB₁ eB₂ : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (decodeInformation eV₁ eE₁ eB₁ (encodeInformation eV₁ eE₁ eB₁ info)).possible =
      (decodeInformation eV₂ eE₂ eB₂ (encodeInformation eV₂ eE₂ eB₂ info)).possible := by
  rw [decodeInformation_encodeInformation, decodeInformation_encodeInformation]

/-- The recovered knowledge tag, scope summary and attached diagram are independent of the choice
of enumerations. -/
theorem recovered_metadata_independent_of_enumerations
    (eV₁ eV₂ : V ≃ Fin (Fintype.card V))
    (eE₁ eE₂ : E ≃ Fin (Fintype.card E))
    (eB₁ eB₂ : B ≃ Fin (Fintype.card B))
    (info : FiniteClassicalInformation V E B) :
    (decodeInformation eV₁ eE₁ eB₁ (encodeInformation eV₁ eE₁ eB₁ info)).knowledge =
        (decodeInformation eV₂ eE₂ eB₂ (encodeInformation eV₂ eE₂ eB₂ info)).knowledge ∧
      (decodeInformation eV₁ eE₁ eB₁ (encodeInformation eV₁ eE₁ eB₁ info)).scopes =
        (decodeInformation eV₂ eE₂ eB₂ (encodeInformation eV₂ eE₂ eB₂ info)).scopes ∧
      (decodeInformation eV₁ eE₁ eB₁ (encodeInformation eV₁ eE₁ eB₁ info)).diagram? =
        (decodeInformation eV₂ eE₂ eB₂ (encodeInformation eV₂ eE₂ eB₂ info)).diagram? := by
  rw [decodeInformation_encodeInformation, decodeInformation_encodeInformation]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The drawing channel retained by each whole state -/

/-- Encoding a whole description relabels its optional source drawing data through the same atom
enumeration, leaving absence absent. -/
@[simp] theorem encodeDescription_diagram? (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (encodeDescription eV eE eB description).diagram? =
      description.diagram?.map (relabelDiagramSource eV) := by
  unfold encodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- Decoding a whole description relabels its optional source drawing data through the inverse
enumeration. -/
@[simp] theorem decodeDescription_diagram? (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    (decodeDescription eV eE eB encoded).diagram? =
      encoded.diagram?.map (relabelDiagramSource eV.symm) := by
  unfold decodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- The encoded drawing data is exactly the relabelled drawing data of the decoded whole state.
Thus the diagram channel is retained by the whole-state information transport. -/
theorem encodeDescription_decodeDescription_diagram?
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    encoded.diagram? =
      (decodeDescription eV eE eB encoded).diagram?.map (relabelDiagramSource eV) := by
  rw [decodeDescription_diagram?, Option.map_map]
  have h : (relabelDiagramSource eV ∘ relabelDiagramSource eV.symm) = id := by
    funext source
    simpa using relabelDiagramSource_symm (e := eV.symm) source
  rw [h, Option.map_id]
  rfl

/-- Every possible encoded state is the image of a possible original whole state, and its drawing
channel is the relabelled drawing channel of that original state. -/
theorem encodeInformation_mem_possible_diagram
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (info : FiniteClassicalInformation V E B)
    (state : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B))
    (member : state ∈ (encodeInformation eV eE eB info).possible) :
    ∃ original ∈ info.possible,
      encodeDescription eV eE eB original = state ∧
        state.diagram? = original.diagram?.map (relabelDiagramSource eV) := by
  rw [encodeInformation_possible, Set.mem_image] at member
  obtain ⟨original, originalMember, mapped⟩ := member
  have mapped' : encodeDescription eV eE eB original = state := mapped
  exact ⟨original, originalMember, mapped', by rw [← mapped', encodeDescription_diagram?]⟩

/-! ## Exact recovery of every data channel

The domain's `decodeDescription_encodeDescription` already states that decoding recovers the
original whole state.  The following corollaries expose that fact separately for every data field,
so that no channel (including the optional channels, the sparse drawing ledger and the specialist
annotation channels) is projected away by the recovery pipeline. -/

/-- Decoding an encoded description recovers the original interaction hypergraph. -/
theorem decodeDescription_encodeDescription_graph
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).graph =
      description.graph := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the optional supplied electronic inventory exactly. -/
theorem decodeDescription_encodeDescription_electronic
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).electronic? =
      description.electronic? := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the shared real conformation exactly. -/
theorem decodeDescription_encodeDescription_conformation
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).conformation =
      description.conformation := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers optional rational provenance, including genuine absence. -/
theorem decodeDescription_encodeDescription_rationalPositions
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).rationalPositions? =
      description.rationalPositions? := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the ordered role ledger exactly. -/
theorem decodeDescription_encodeDescription_roles
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).roles =
      description.roles := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the bond-path family exactly at every edge. -/
theorem decodeDescription_encodeDescription_paths
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).paths =
      description.paths := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the band attachment family exactly at every band. -/
theorem decodeDescription_encodeDescription_bandFamily
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).bandFamily =
      description.bandFamily := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the optional source drawing data exactly. -/
theorem decodeDescription_encodeDescription_diagram
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).diagram? =
      description.diagram? := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the optional sparse partial positions exactly. -/
theorem decodeDescription_encodeDescription_diagramPartial
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).diagramPartial? =
      description.diagramPartial? := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the sparse raw incidence ledger exactly, including multiplicity. -/
theorem decodeDescription_encodeDescription_diagramIncidence
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).diagramIncidence =
      description.diagramIncidence := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the ordered residue/fragment annotation ledger exactly.  The payload type is
owned by the specialist-annotation module; it is moved unchanged as part of the whole state. -/
theorem decodeDescription_encodeDescription_fragments
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).fragments =
      description.fragments := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the optional specialist residue-link and naming-hierarchy ledger exactly,
including genuine absence.  The payload type is owned by the specialist-annotation module; it is
moved unchanged as a field of the whole state. -/
theorem decodeDescription_encodeDescription_residueLedger
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).residueLedger? =
      description.residueLedger? := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the ordered drawing-convention channel exactly. -/
theorem decodeDescription_encodeDescription_conventions
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).conventions =
      description.conventions := by
  rw [decodeDescription_encodeDescription]

/-- Decoding recovers the ordered numbered cage/face annotation channel exactly. -/
theorem decodeDescription_encodeDescription_cages
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).cages =
      description.cages := by
  rw [decodeDescription_encodeDescription]

/-- All fourteen data channels of the whole state are recovered together: the interaction
hypergraph, the optional electronic inventory, the shared conformation, optional rational
provenance, the role ledger, the path family, the band family, the optional drawing data, the
optional partial positions, the raw incidence ledger, the fragment, convention and cage
annotation channels, and the optional specialist residue ledger.  No field is projected out. -/
theorem decodeDescription_encodeDescription_allData
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).graph =
        description.graph ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).electronic? =
        description.electronic? ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).conformation =
        description.conformation ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).rationalPositions? =
        description.rationalPositions? ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).roles =
        description.roles ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).paths =
        description.paths ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).bandFamily =
        description.bandFamily ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).diagram? =
        description.diagram? ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).diagramPartial? =
        description.diagramPartial? ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).diagramIncidence =
        description.diagramIncidence ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).fragments =
        description.fragments ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).conventions =
        description.conventions ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).cages =
        description.cages ∧
      (decodeDescription eV eE eB (encodeDescription eV eE eB description)).residueLedger? =
        description.residueLedger? := by
  rw [decodeDescription_encodeDescription]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FiniteClassicalInformation

/-! ## Concrete fixtures -/

namespace FiniteClassicalInformationExample

open FiniteClassicalStereoDescriptionExample

/-- A retained knowledge tag for the fixture. -/
def knowledge : ConfigurationKnowledge := ConfigurationKnowledge.knownAbsolute

/-- The joint possible set of the fixture: exactly one entire whole description. -/
def possible : Set (FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0)) :=
  {description}

/-- A non-vacuous consistent information value over the repository's concrete description. -/
def information : FiniteClassicalInformation (Fin 2) (Fin 1) (Fin 0) :=
  FiniteClassicalInformation.ofStates knowledge possible

@[simp] theorem information_possible :
    information.possible = possible := rfl

/-- The fixture is consistent: one whole state is jointly possible. -/
theorem information_consistent : information.Consistent := by
  rw [FiniteClassicalInformation.consistent_iff_possible_nonempty, information_possible]
  exact ⟨description, by simp [possible]⟩

/-- Identity-enumeration encoding and decoding recovers the concrete information exactly. -/
theorem information_roundtrip :
    FiniteClassicalInformation.decodeInformation (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1))
        (Equiv.refl (Fin 0))
        (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2))
          (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0)) information) = information :=
  FiniteClassicalInformation.decodeInformation_encodeInformation _ _ _ information

/-- The recovered possible set is exactly the singleton of the original whole description: the
entire state, not a product of projections. -/
theorem information_recovered_possible :
    (FiniteClassicalInformation.decodeInformation (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1))
        (Equiv.refl (Fin 0))
        (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2))
          (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0)) information)).possible =
      {description} := by
  rw [FiniteClassicalInformation.decodeInformation_encodeInformation, information_possible]
  rfl

/-- The encoded information is consistent too. -/
theorem encoded_information_consistent :
    (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1))
      (Equiv.refl (Fin 0)) information).Consistent :=
  (FiniteClassicalInformation.encodeInformation_consistent_iff _ _ _ _).mpr
    information_consistent

/-- The knowledge tag is retained by encoding. -/
theorem encoded_information_knowledge :
    (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1))
      (Equiv.refl (Fin 0)) information).knowledge =
      ConfigurationKnowledge.knownAbsolute := by
  simp [information, knowledge]

/-- The encoded image of the concrete description is jointly possible.  Its whole state, including
its (absent) drawing channel, is moved as one unit. -/
theorem encoded_description_mem :
    encodeDescription (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0))
        description ∈
      (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2))
        (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0)) information).possible := by
  rw [FiniteClassicalInformation.mem_encodeInformation_possible_iff,
    decodeDescription_encodeDescription]
  simp [information_possible, possible]

/-- A genuinely non-identity atom enumeration of the fixture atom type. -/
def swapAtoms : Fin 2 ≃ Fin 2 :=
  Equiv.swap 0 1

/-- The recovered information is independent of the atom enumeration at the concrete fixture,
using a genuinely non-identity enumeration of `Fin 2`. -/
theorem information_recovered_possible_independent_of_enumerations :
    (FiniteClassicalInformation.decodeInformation (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1))
        (Equiv.refl (Fin 0))
        (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2))
          (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0)) information)).possible =
      (FiniteClassicalInformation.decodeInformation swapAtoms (Equiv.refl (Fin 1))
        (Equiv.refl (Fin 0))
        (FiniteClassicalInformation.encodeInformation swapAtoms (Equiv.refl (Fin 1))
          (Equiv.refl (Fin 0)) information)).possible :=
  FiniteClassicalInformation.recovered_possible_independent_of_enumerations
    (Equiv.refl (Fin 2)) swapAtoms (Equiv.refl (Fin 1)) (Equiv.refl (Fin 1))
    (Equiv.refl (Fin 0)) (Equiv.refl (Fin 0)) information

/-! ### A non-singleton joint possible set

The singleton fixture above exercises exact membership; this fixture uses `Set.univ`, an arbitrary
whole-state set, and verifies both recovery laws, nonemptiness and membership of every state. -/

/-- A non-singleton joint possible set: every whole state is possible. -/
def universalPossible : Set (FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0)) :=
  Set.univ

/-- Information with the universal whole-state set and the wholly-unspecified tag. -/
def universalInformation : FiniteClassicalInformation (Fin 2) (Fin 1) (Fin 0) :=
  FiniteClassicalInformation.ofStates ConfigurationKnowledge.whollyUnspecified universalPossible

@[simp] theorem universalInformation_possible :
    universalInformation.possible = Set.univ := rfl

/-- The universal-set fixture is consistent. -/
theorem universalInformation_consistent : universalInformation.Consistent := by
  rw [FiniteClassicalInformation.consistent_iff_possible_nonempty, universalInformation_possible]
  exact ⟨description, Set.mem_univ description⟩

/-- The universal set is recovered exactly by decode-after-encode. -/
theorem universalInformation_recovered_possible :
    (FiniteClassicalInformation.decodeInformation (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1))
        (Equiv.refl (Fin 0))
        (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2))
          (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0)) universalInformation)).possible =
      Set.univ := by
  rw [FiniteClassicalInformation.decodeInformation_encodeInformation,
    universalInformation_possible]

/-- The universal set is recovered exactly by encode-after-decode. -/
theorem universalInformation_reencoded_possible :
    (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1))
        (Equiv.refl (Fin 0))
        (FiniteClassicalInformation.decodeInformation (Equiv.refl (Fin 2))
          (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0)) universalInformation)).possible =
      Set.univ := by
  rw [FiniteClassicalInformation.encodeInformation_decodeInformation,
    universalInformation_possible]

/-- Every whole state is a member of the recovered universal possible set. -/
theorem universalInformation_recovered_mem
    (state : FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0)) :
    state ∈
      (FiniteClassicalInformation.decodeInformation (Equiv.refl (Fin 2))
        (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0))
        (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2))
          (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0)) universalInformation)).possible := by
  rw [FiniteClassicalInformation.decodeInformation_encodeInformation,
    universalInformation_possible]
  exact Set.mem_univ state

/-- The recovered universal possible set is nonempty. -/
theorem universalInformation_recovered_nonempty :
    (FiniteClassicalInformation.decodeInformation (Equiv.refl (Fin 2))
      (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0))
      (FiniteClassicalInformation.encodeInformation (Equiv.refl (Fin 2))
        (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0)) universalInformation)).possible.Nonempty :=
  ⟨description, universalInformation_recovered_mem description⟩

/-- An explicit inconsistent fixture: empty joint possible set. -/
def emptyInformation : FiniteClassicalInformation (Fin 2) (Fin 1) (Fin 0) :=
  FiniteClassicalInformation.ofStates ConfigurationKnowledge.whollyUnspecified ∅

@[simp] theorem emptyInformation_possible : emptyInformation.possible = ∅ := rfl

/-- The empty information value is genuinely inconsistent, not merely underspecified. -/
theorem emptyInformation_not_consistent : ¬ emptyInformation.Consistent :=
  CorrelatedInformation.not_consistent_of_possible_eq_empty emptyInformation rfl

theorem emptyInformation_consistent_iff_false :
    emptyInformation.Consistent ↔ False := by
  rw [FiniteClassicalInformation.consistent_iff_possible_nonempty, emptyInformation_possible]
  simp

end FiniteClassicalInformationExample

end

end TetraStereo.OneCenter
