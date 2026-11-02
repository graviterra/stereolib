import TetraStereo.OneCenter.OrganicStereoFiniteEncoding
import TetraStereo.OneCenter.OrganicStereoRealConfiguration
import TetraStereo.OneCenter.OrganicStereoInteractionRoles
import Mathlib.Data.Fin.SuccPred

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# Joint finite physical state: one source, geometry and interaction roles together

This module is the representational core join between three independently written foundation
layers:

* `OrganicStereoFiniteEncoding` — an arbitrary finite atom type `V`, an ordered list of source
  hyperedges, and the certified encoding `FiniteAtomInteractionHypergraph.certifiedEncoding`;
* `OrganicStereoRealConfiguration` — real conformations `MolecularConformation V` and their
  transport by a bijection of atom indices;
* `OrganicStereoInteractionRoles` — typed interaction roles and their attachment to concrete
  source indices.

The new object is an **independent physical state** over the source atom type `V`: one real point
per source atom together with one explicitly supplied role for every source interaction index.  A
role is one of the five physical constructors (ordinary bond, directed coordination, haptic
ligand, multicenter, delocalized), each carrying its own physical distinctness / nonemptiness /
arity data and its own electron count or bond order.  The state also carries, for every index, the
independent agreement that its role has exactly the source participant list, in order and with
multiplicity, and exactly the source kind (including any electron count).  Nothing is inferred
from the stored participant order, from the kind, or from a stereodescriptor.

`encodeJoint` maps such a state through the *same* enumeration used by
`graph.certifiedEncoding e`: all atoms are transported by one equivalence derived from `e`, the
geometry by `MolecularConformation.reindex`, and every role to an existing
`InteractionRoles.TypedInteraction` attached as an `InteractionRoles.RoleDecoration` to the
matching encoded interaction index.  `decodeJoint` is a concrete inverse on encoded states, and
`joint_encoding_left_inverse` proves that decoding an encoded state recovers the original
independent geometry and the original roles.  A whole set of states is mapped as a set (no
replacement by a product of marginals): `decodeJoint_image_encodeJointSet` proves exact recovery.

Changing the enumeration transports *all* channels by one common index permutation
(`enumeration_transport_joint`): the geometry is reindexed and every typed role is relabelled by
the same equivalence.  There is no independent choice per channel.

Boundaries: no `LocalizedCIPGraphReady`, desired label, priority, named geometry, path/band/
steric-locking knowledge is used or claimed.  The source keeps `spatial? = none` and
`diagram? = none`; the real frame is an explicit addition, not a reinterpretation of absent
spatial evidence.  Role erasure alone is not injective (already proved in
`InteractionRoles.TypedInteraction.roleErase_not_injective`); the full joint record retains the
roles, as `joint_encoding_roleAt` shows.  This is a representation join, not an
exhaustiveness claim about the intended chemical domain.

## Strict versus broad state

`JointState` is the **strict (restricted)** variant.  It demands a `PhysicalRole` for *every* source
interaction index and keeps the literal ordered agreement `supportKind = graph.interactions.get
index`.  That theorem (`joint_encoding_left_inverse`) is sound and is retained unchanged; it is
explicitly named as a restriction at `strict_joint_encoding_left_inverse_restricted`.

The **broad** state `BroadJointState` removes both restrictions.  Its independent role data is a
finite *ordered list* of `BroadAnnotation`s, each naming one concrete source interaction occurrence
index and one role over the independent labels `V`.  An annotation records only the compatibility
that `InteractionRoles.Decorates` itself checks (kind/electron count, unordered participant support
as a `Finset`, equal participant count); the source participant order need not coincide literally
with the role's ordered support.  The ledger may be empty or partial, may contain several
annotations of the same index, and keeps list order and multiplicity.  Source interactions stay the
entire arbitrary graph, unchanged.  The broad states are encoded through the *same* atom
equivalence as the graph and geometry, producing the existing `InteractionRoles.RoleLedger`; no
encoded ledger is an input.  Decode-after-encode, injectivity, whole-set recovery and enumeration
transport are proved for the entire geometry-plus-ledger state.
-/

namespace TetraStereo.OneCenter
namespace JointCoreEncoding

open InteractionRoles
open FiniteAtomInteractionHypergraph

/-! ## Explicit role data over an arbitrary finite atom type -/

/-- The five physical interaction-role constructors over independent atom labels `V`.

Every constructor carries its own physical arity / distinctness evidence:

* `ordinaryBond` carries a bond order and two distinct atoms;
* `directed` carries an explicit donor and acceptor and their distinctness — direction is data,
  never read off a stored list order;
* `haptic` carries a metal centre and a nonempty, duplicate-free donor support disjoint from the
  centre;
* `multicenter` and `delocalized` carry a duplicate-free participant list of arity at least two
  and an explicit electron count.

No constructor stores a stereodescriptor, priority, named geometry or path/band tag. -/
inductive PhysicalRole (V : Type*) where
  | ordinaryBond (bondOrder : ℕ) (left right : V) (distinct : left ≠ right)
  | directed (donor acceptor : V) (distinct : donor ≠ acceptor)
  | haptic (centre : V) (donors : List V) (nonempty : donors ≠ [])
      (nodup : donors.Nodup) (centreNotMem : centre ∉ donors)
  | multicenter (participants : List V) (nodup : participants.Nodup)
      (arity : 2 ≤ participants.length) (electronCount : ℕ)
  | delocalized (participants : List V) (nodup : participants.Nodup)
      (arity : 2 ≤ participants.length) (electronCount : ℕ)

namespace PhysicalRole

/-- The ordered participant list and semantic kind carried by a physical role.  This is exactly
the information that must agree with the independent source hyperedge: participant order and
multiplicity, kind and every electron count are preserved. -/
def supportKind {V : Type*} : PhysicalRole V → List V × SemanticInteractionKind
  | ordinaryBond bondOrder left right _ =>
      ([left, right], SemanticInteractionKind.covalent bondOrder)
  | directed donor acceptor _ =>
      ([donor, acceptor], SemanticInteractionKind.coordinate)
  | haptic centre donors _ _ _ =>
      (centre :: donors, SemanticInteractionKind.coordinate)
  | multicenter participants _ _ electronCount =>
      (participants, SemanticInteractionKind.multicenter electronCount)
  | delocalized participants _ _ electronCount =>
      (participants, SemanticInteractionKind.delocalized electronCount)

/-- Map a physical role through a bijection onto `Fin n`, producing the existing typed
interaction representation.  Only atom identities move; constructor role, direction, electron
count and haptic support are copied. -/
def toTypedInteraction {V : Type*} {n : ℕ} (e : V ≃ Fin n) :
    PhysicalRole V → InteractionRoles.TypedInteraction n
  | ordinaryBond bondOrder left right distinct =>
      InteractionRoles.TypedInteraction.ordinaryBond
        ⟨bondOrder, e left, e right, fun equal => distinct (e.injective equal)⟩
  | directed donor acceptor distinct =>
      InteractionRoles.TypedInteraction.directedCoordination
        ⟨e donor, e acceptor, fun equal => distinct (e.injective equal)⟩
  | haptic centre donors nonempty nodup centreNotMem =>
      InteractionRoles.TypedInteraction.haptic
        ⟨e centre, donors.map e, by simpa using nonempty,
          nodup.map e.injective,
          by
            intro member
            rcases List.mem_map.mp member with ⟨donor, donorMem, equal⟩
            exact centreNotMem (by
              have hd : donor = centre := e.injective equal
              simpa [hd] using donorMem)⟩
  | multicenter participants nodup arity electronCount =>
      InteractionRoles.TypedInteraction.multicenter
        ⟨participants.map e, nodup.map e.injective, by simpa using arity, electronCount⟩
  | delocalized participants nodup arity electronCount =>
      InteractionRoles.TypedInteraction.delocalized
        ⟨participants.map e, nodup.map e.injective, by simpa using arity, electronCount⟩

/-- Recover physical role data from a typed interaction through the inverse bijection.  The
recovered role carries the physically meaningful proofs transported back from the typed data;
no role is inferred from the semantic kind. -/
def ofTypedInteraction {V : Type*} {n : ℕ} (e : V ≃ Fin n) :
    InteractionRoles.TypedInteraction n → PhysicalRole V
  | InteractionRoles.TypedInteraction.ordinaryBond data =>
      ordinaryBond data.bondOrder (e.symm data.left) (e.symm data.right)
        (fun equal => data.distinct (by simpa using congrArg e equal))
  | InteractionRoles.TypedInteraction.directedCoordination data =>
      directed (e.symm data.donor) (e.symm data.acceptor)
        (fun equal => data.distinct (by simpa using congrArg e equal))
  | InteractionRoles.TypedInteraction.haptic data =>
      haptic (e.symm data.centre) (data.donors.map e.symm)
        (by intro empty; exact data.nonempty (by simpa using empty))
        (data.nodup.map e.symm.injective)
        (by
          intro member
          rcases List.mem_map.mp member with ⟨donor, donorMem, equal⟩
          exact data.centreNotMem (by
            have hd : donor = data.centre := e.symm.injective equal
            simpa [hd] using donorMem))
  | InteractionRoles.TypedInteraction.multicenter data =>
      multicenter (data.participants.map e.symm)
        (data.nodup.map e.symm.injective) (by simpa using data.arity) data.electronCount
  | InteractionRoles.TypedInteraction.delocalized data =>
      delocalized (data.participants.map e.symm)
        (data.nodup.map e.symm.injective) (by simpa using data.arity) data.electronCount

/-! ### Elementary list transports used by the round trips -/

theorem map_symm_apply_map {V : Type*} {n : ℕ} (e : V ≃ Fin n) (values : List V) :
    (values.map e).map e.symm = values := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis => simp [inductionHypothesis]

theorem map_apply_symm_map {V : Type*} {n : ℕ} (e : V ≃ Fin n)
    (values : List (Fin n)) :
    (values.map e.symm).map e = values := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis => simp [inductionHypothesis]

/-- Decoding an encoded physical role returns exactly the original role: geometry of atoms,
constructor role, direction, haptic support and electron counts are all recovered. -/
@[simp] theorem ofTypedInteraction_toTypedInteraction {V : Type*} {n : ℕ}
    (e : V ≃ Fin n) (role : PhysicalRole V) :
    PhysicalRole.ofTypedInteraction e (role.toTypedInteraction e) = role := by
  cases role with
  | ordinaryBond bondOrder left right distinct =>
      simp [toTypedInteraction, ofTypedInteraction]
  | directed donor acceptor distinct =>
      simp [toTypedInteraction, ofTypedInteraction]
  | haptic centre donors nonempty nodup centreNotMem =>
      simp [toTypedInteraction, ofTypedInteraction, map_symm_apply_map]
  | multicenter participants nodup arity electronCount =>
      simp [toTypedInteraction, ofTypedInteraction, map_symm_apply_map]
  | delocalized participants nodup arity electronCount =>
      simp [toTypedInteraction, ofTypedInteraction, map_symm_apply_map]

/-- Encoding a typed interaction through the inverse bijection recovers that typed interaction.
This is the other round trip, needed to show that decoding an arbitrary encoded state still yields
a physical role whose re-encoding is the stored typed interaction. -/
@[simp] theorem toTypedInteraction_ofTypedInteraction {V : Type*} {n : ℕ}
    (e : V ≃ Fin n) (typed : InteractionRoles.TypedInteraction n) :
    (PhysicalRole.ofTypedInteraction e typed).toTypedInteraction e = typed := by
  cases typed with
  | ordinaryBond data =>
      simp [toTypedInteraction, ofTypedInteraction]
  | directedCoordination data =>
      simp [toTypedInteraction, ofTypedInteraction]
  | haptic data =>
      simp [toTypedInteraction, ofTypedInteraction, map_apply_symm_map]
  | multicenter data =>
      simp [toTypedInteraction, ofTypedInteraction, map_apply_symm_map]
  | delocalized data =>
      simp [toTypedInteraction, ofTypedInteraction, map_apply_symm_map]

end PhysicalRole

/-! ## The common atom equivalence induced by the source enumeration -/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The atom equivalence actually used by the certified encoding: the source enumeration `e`
composed with the size identification between the source atom type and the encoded atom list.
Both the real conformation and every interaction role are transported by this single
equivalence. -/
def sourceAtomEquiv (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) :
    V ≃ SourceAtomIndex (graph.certifiedEncoding e) :=
  e.trans (finCongr (FiniteAtomInteractionHypergraph.encode_atomCount graph e).symm)

/-- The index of a source interaction inside the encoded certified molecule.  Encoding preserves
the interaction list length, so every source index names exactly one encoded interaction index. -/
def encodedIndex (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length) :
    Fin (graph.certifiedEncoding e).input.molecule.interactions.length :=
  Fin.cast (FiniteAtomInteractionHypergraph.encode_interactions_length graph e).symm index

/-- Exact lookup at an encoded interaction index.  The encoded interaction is exactly the
source hyperedge with its participants mapped through `e`; order and kind are unchanged. -/
theorem encoded_get (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length) :
    (graph.certifiedEncoding e).input.molecule.interactions.get
        (encodedIndex graph e index) =
      FiniteAtomInteractionHypergraph.encodeInteraction e (graph.interactions.get index) := by
  show (List.map (FiniteAtomInteractionHypergraph.encodeInteraction e) graph.interactions).get
      (encodedIndex graph e index) =
    FiniteAtomInteractionHypergraph.encodeInteraction e (graph.interactions.get index)
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  rfl

/-- The atom value assigned by the common equivalence is the value assigned by the source
enumeration.  Only the type-level size proof is inserted; atom identities are unchanged. -/
@[simp] theorem sourceAtomEquiv_apply_val (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (atom : V) :
    ((sourceAtomEquiv graph e) atom).val = (e atom).val := rfl

/-- The common equivalence maps a participant list to the same natural-number list as the source
enumeration: participation order and multiplicity are unchanged. -/
@[simp] theorem map_sourceAtomEquiv_val (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (values : List V) :
    (values.map (sourceAtomEquiv graph e)).map Fin.val =
      values.map (fun atom => (e atom).val) := by
  induction values with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp [sourceAtomEquiv_apply_val graph e atom, inductionHypothesis]

/-- Erasing the typed image of a physical role is exactly the encoding of its ordered
participant list and kind.  In particular participation order and multiplicity, kind and every
electron count are preserved by the transport. -/
theorem toTypedInteraction_erase (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (role : PhysicalRole V) :
    (role.toTypedInteraction (sourceAtomEquiv graph e)).erase =
      FiniteAtomInteractionHypergraph.encodeInteraction e role.supportKind := by
  cases role with
  | ordinaryBond bondOrder left right distinct =>
      simp only [PhysicalRole.toTypedInteraction, PhysicalRole.supportKind,
        FiniteAtomInteractionHypergraph.encodeInteraction,
        InteractionRoles.TypedInteraction.erase, List.map_cons, List.map_nil,
        sourceAtomEquiv_apply_val graph e left, sourceAtomEquiv_apply_val graph e right]
  | directed donor acceptor distinct =>
      simp only [PhysicalRole.toTypedInteraction, PhysicalRole.supportKind,
        FiniteAtomInteractionHypergraph.encodeInteraction,
        InteractionRoles.TypedInteraction.erase, List.map_cons, List.map_nil,
        sourceAtomEquiv_apply_val graph e donor, sourceAtomEquiv_apply_val graph e acceptor]
  | haptic centre donors nonempty nodup centreNotMem =>
      simp only [PhysicalRole.toTypedInteraction, PhysicalRole.supportKind,
        FiniteAtomInteractionHypergraph.encodeInteraction,
        InteractionRoles.TypedInteraction.erase, List.map_cons, List.map_nil,
        sourceAtomEquiv_apply_val graph e centre,
        map_sourceAtomEquiv_val graph e donors]
  | multicenter participants nodup arity electronCount =>
      simp only [PhysicalRole.toTypedInteraction, PhysicalRole.supportKind,
        FiniteAtomInteractionHypergraph.encodeInteraction,
        InteractionRoles.TypedInteraction.erase,
        map_sourceAtomEquiv_val graph e participants]
  | delocalized participants nodup arity electronCount =>
      simp only [PhysicalRole.toTypedInteraction, PhysicalRole.supportKind,
        FiniteAtomInteractionHypergraph.encodeInteraction,
        InteractionRoles.TypedInteraction.erase,
        map_sourceAtomEquiv_val graph e participants]

/-- Encoding of a source hyperedge is injective: atom identities are mapped by a bijection and
the kind is copied verbatim.  Consequently exact list/kind agreement can be tested after
encoding. -/
theorem encodeInteraction_injective (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective (FiniteAtomInteractionHypergraph.encodeInteraction e) := by
  intro first second equal
  obtain ⟨firstParticipants, firstKind⟩ := first
  obtain ⟨secondParticipants, secondKind⟩ := second
  have participants : firstParticipants = secondParticipants := by
    have mapped := congrArg SemanticInteraction.participants equal
    simp only [FiniteAtomInteractionHypergraph.encodeInteraction] at mapped
    exact (List.map_inj_right (fun a b same => e.injective (Fin.ext same))).mp mapped
  have kind : firstKind = secondKind := by
    have mapped := congrArg SemanticInteraction.kind equal
    simpa [FiniteAtomInteractionHypergraph.encodeInteraction] using mapped
  simp [participants, kind]

/-! ## Independent joint physical states -/

/-- The **strict (restricted)** independent physical state over the source atom type: one real
geometry and one explicit physical role for every source interaction index, with the independent
agreement that each role has exactly the source edge's ordered participant list and kind.

This is deliberately narrower than `BroadJointState` below: it requires a role for *every* source
interaction (so an aromatic, ionic, metallic or otherwise unspecified source edge cannot be left
unannotated) and it requires the literal ordered equality `supportKind = graph.interactions.get
index` (so the opposite donor direction against the same source participant order is excluded).
The broad state removes both restrictions.  This strict structure and its theorem
`joint_encoding_left_inverse` remain valid and are named as the restricted case at
`strict_joint_encoding_left_inverse_restricted`.

The state is indexed by the *labels* `V` and by source indices; it is independent of any chosen
enumeration of `V`. -/
structure JointState (graph : FiniteAtomInteractionHypergraph V) where
  /-- One real point per independent source atom label. -/
  conformation : MolecularConformation V
  /-- Explicit role at every source interaction index. -/
  roleAt : (index : Fin graph.interactions.length) → PhysicalRole V
  /-- The role at an index has exactly the source participant list (order and multiplicity) and
  exactly the source kind, including electron counts. -/
  agrees : ∀ index, (roleAt index).supportKind = graph.interactions.get index

namespace JointState

/-- Extensionality for joint states.  The agreement field is proposition-valued, so two states
with the same geometry and the same role assignment are equal. -/
theorem extEq {graph : FiniteAtomInteractionHypergraph V} {first second : JointState graph}
    (conformation : first.conformation = second.conformation)
    (roleAt : first.roleAt = second.roleAt) : first = second := by
  obtain ⟨firstConformation, firstRoles, firstAgrees⟩ := first
  obtain ⟨secondConformation, secondRoles, secondAgrees⟩ := second
  cases conformation
  cases roleAt
  rfl

end JointState

/-- The certified encoded joint state.  It lives over `graph.certifiedEncoding e`: the geometry
is a source-indexed real conformation and every interaction carries an existing
`RoleDecoration` attached to the encoded interaction index. -/
structure EncodedJointState (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) where
  /-- Real geometry over the encoded certified source atom index. -/
  conformation : SourceConformation (graph.certifiedEncoding e)
  /-- Existing typed role decoration at every source interaction index. -/
  decorations : (index : Fin graph.interactions.length) →
    InteractionRoles.RoleDecoration (graph.certifiedEncoding e).input.molecule
  /-- The decoration is attached to the encoded image of exactly that source index. -/
  decoration_index : ∀ index, (decorations index).index = encodedIndex graph e index
  /-- The full erased typed interaction is literally the source edge encoded through `e`, so
  order, multiplicity, kind and electron counts all agree independently. -/
  source_exact : ∀ index, (decorations index).typed.erase =
    FiniteAtomInteractionHypergraph.encodeInteraction e (graph.interactions.get index)

/-! ## Attaching a physical role to a source index -/

/-- Build the existing role decoration for one source index from an explicit physical role and
the independent agreement with the source edge. -/
def decorationOf (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length)
    (role : PhysicalRole V)
    (agrees : role.supportKind = graph.interactions.get index) :
    InteractionRoles.RoleDecoration (graph.certifiedEncoding e).input.molecule :=
  InteractionRoles.RoleDecoration.ofDecorates (encodedIndex graph e index)
    (role.toTypedInteraction (sourceAtomEquiv graph e))
    (by
      refine ⟨?_, ?_⟩
      · change InteractionRoles.roleErasedSupport
            ((role.toTypedInteraction (sourceAtomEquiv graph e)).erase) =
          InteractionRoles.roleErasedSupport
            ((graph.certifiedEncoding e).input.molecule.interactions.get
              (encodedIndex graph e index))
        rw [toTypedInteraction_erase graph e role, agrees, encoded_get graph e index]
      · rw [toTypedInteraction_erase graph e role, agrees, encoded_get graph e index])

@[simp] theorem decorationOf_index (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length)
    (role : PhysicalRole V) (agrees : role.supportKind = graph.interactions.get index) :
    (decorationOf graph e index role agrees).index = encodedIndex graph e index := rfl

@[simp] theorem decorationOf_typed (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length)
    (role : PhysicalRole V) (agrees : role.supportKind = graph.interactions.get index) :
    (decorationOf graph e index role agrees).typed =
      role.toTypedInteraction (sourceAtomEquiv graph e) := rfl

/-- Recover a physical role from an encoded typed interaction. -/
def decodeRole {n : ℕ} (e : V ≃ Fin n) (typed : InteractionRoles.TypedInteraction n) :
    PhysicalRole V :=
  PhysicalRole.ofTypedInteraction e typed

/-- If a typed interaction erases exactly to an encoded source edge, then the physical role
recovered from it has exactly that source edge's ordered participants and kind. -/
theorem decodeRole_agrees (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length)
    (typed : InteractionRoles.TypedInteraction
      (graph.certifiedEncoding e).input.molecule.atomCount)
    (hexact : typed.erase =
      FiniteAtomInteractionHypergraph.encodeInteraction e (graph.interactions.get index)) :
    (decodeRole (sourceAtomEquiv graph e) typed).supportKind =
      graph.interactions.get index := by
  change (PhysicalRole.ofTypedInteraction (sourceAtomEquiv graph e) typed).supportKind =
    graph.interactions.get index
  have composed : FiniteAtomInteractionHypergraph.encodeInteraction e
        (PhysicalRole.ofTypedInteraction (sourceAtomEquiv graph e) typed).supportKind =
      FiniteAtomInteractionHypergraph.encodeInteraction e (graph.interactions.get index) := by
    rw [← toTypedInteraction_erase graph e
      (PhysicalRole.ofTypedInteraction (sourceAtomEquiv graph e) typed)]
    rw [PhysicalRole.toTypedInteraction_ofTypedInteraction (sourceAtomEquiv graph e) typed]
    exact hexact
  exact encodeInteraction_injective e composed

/-! ## Encode and decode the joint state -/

/-- Encode an independent joint state through the source enumeration.  The geometry is reindexed
by `sourceAtomEquiv`, and every role is transported to a typed `RoleDecoration` attached to the
encoded interaction index.  All channels use the same enumeration. -/
def encodeJoint (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : JointState graph) :
    EncodedJointState graph e where
  conformation := MolecularConformation.reindex (sourceAtomEquiv graph e) state.conformation
  decorations := fun index =>
    decorationOf graph e index (state.roleAt index) (state.agrees index)
  decoration_index := fun index => rfl
  source_exact := fun index => by
    show ((state.roleAt index).toTypedInteraction (sourceAtomEquiv graph e)).erase =
      FiniteAtomInteractionHypergraph.encodeInteraction e (graph.interactions.get index)
    rw [toTypedInteraction_erase graph e (state.roleAt index), state.agrees index]

/-- Decode an encoded joint state back to an independent state over `V`.  The geometry is
reindexed by the inverse atom equivalence and every role is recovered from its typed decoration.
Decoding is total and requires no reconstruction hypothesis. -/
def decodeJoint (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : EncodedJointState graph e) :
    JointState graph where
  conformation := MolecularConformation.reindex (sourceAtomEquiv graph e).symm state.conformation
  roleAt := fun index =>
    decodeRole (sourceAtomEquiv graph e) ((state.decorations index).typed)
  agrees := fun index =>
    decodeRole_agrees graph e index ((state.decorations index).typed)
      (state.source_exact index)

/-! ## The left-inverse theorem -/

/-- **Restricted strict join theorem.**  Decoding the encoded image of a *strict* independent
joint state recovers the original independent geometry and the original explicit roles.  The
agreement field is proposition-valued and recovered by proof irrelevance.

This is the original strict result, retained unchanged.  It is **restricted**: it applies only to
states that assign a role to every source interaction and that satisfy the literal ordered
agreement `supportKind = graph.interactions.get index`.  The unrestricted statement is
`broad_joint_encoding_left_inverse` below, and `strict_joint_encoding_left_inverse_restricted`
names this theorem as the restriction to full ordered ledgers. -/
theorem joint_encoding_left_inverse (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : JointState graph) :
    decodeJoint graph e (encodeJoint graph e state) = state := by
  obtain ⟨conformation, roleAt, agrees⟩ := state
  apply JointState.extEq
  · show MolecularConformation.reindex (sourceAtomEquiv graph e).symm
        (MolecularConformation.reindex (sourceAtomEquiv graph e) conformation) = conformation
    exact MolecularConformation.reindex_reindex (sourceAtomEquiv graph e) conformation
  · funext index
    show PhysicalRole.ofTypedInteraction (sourceAtomEquiv graph e)
        ((roleAt index).toTypedInteraction (sourceAtomEquiv graph e)) = roleAt index
    exact PhysicalRole.ofTypedInteraction_toTypedInteraction
      (sourceAtomEquiv graph e) (roleAt index)

/-- Encoding is injective, because decoding is a left inverse. -/
theorem encodeJoint_injective (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) : Function.Injective (encodeJoint graph e) := by
  intro first second equal
  have := congrArg (decodeJoint graph e) equal
  simpa [joint_encoding_left_inverse graph e first,
    joint_encoding_left_inverse graph e second] using this

/-- The joint record retains the role channel exactly.  In particular, unlike bare role
erasure (which is not injective, `InteractionRoles.TypedInteraction.roleErase_not_injective`),
the encoded joint state determines every explicit role. -/
theorem joint_encoding_roleAt (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : JointState graph) :
    (decodeJoint graph e (encodeJoint graph e state)).roleAt = state.roleAt :=
  congrArg JointState.roleAt (joint_encoding_left_inverse graph e state)

/-- The joint record retains the geometry channel exactly. -/
theorem joint_encoding_conformation (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : JointState graph) :
    (decodeJoint graph e (encodeJoint graph e state)).conformation = state.conformation :=
  congrArg JointState.conformation (joint_encoding_left_inverse graph e state)

/-! ## Whole sets of independent states -/

/-- The image of an arbitrary set of independent joint states.  The whole set is encoded as a
set; it is never replaced by a product of independently chosen marginal sets. -/
def encodeJointSet (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (states : Set (JointState graph)) :
    Set (EncodedJointState graph e) :=
  encodeJoint graph e '' states

/-- Exact membership in the encoded set: an encoded state belongs to it exactly when it is the
image of some member state. -/
theorem mem_encodeJointSet_iff (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (states : Set (JointState graph))
    (encoded : EncodedJointState graph e) :
    encoded ∈ encodeJointSet graph e states ↔
      ∃ state, state ∈ states ∧ encodeJoint graph e state = encoded :=
  Iff.rfl

/-- Exact membership recovery at the level of a single state: the encoded image of a state lies
in the encoded set exactly when the state lies in the original set.  This is an exact set
statement, not a product-of-marginals approximation. -/
theorem mem_encodeJointSet_image_iff (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (states : Set (JointState graph))
    (state : JointState graph) :
    encodeJoint graph e state ∈ encodeJointSet graph e states ↔ state ∈ states := by
  constructor
  · rintro ⟨other, otherMem, equal⟩
    have same : other = state := encodeJoint_injective graph e equal
    simpa [same] using otherMem
  · intro member
    exact ⟨state, member, rfl⟩

/-- Decoding the image of an arbitrary set of joint states recovers that set exactly.  This is the
set-level form of the left-inverse theorem. -/
theorem decodeJoint_image_encodeJointSet (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (states : Set (JointState graph)) :
    decodeJoint graph e '' encodeJointSet graph e states = states := by
  rw [encodeJointSet, Set.image_image]
  have composeIdentity :
      (fun state => decodeJoint graph e (encodeJoint graph e state)) = id := by
    funext state
    exact joint_encoding_left_inverse graph e state
  rw [composeIdentity, Set.image_id]

/-! ## Change of enumeration transports all channels together -/

/-- The common index permutation induced by changing the enumeration from `e₁` to `e₂`.  The
same permutation is used for the geometry and for every typed role. -/
def encodedIndexEquiv (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) :
    SourceAtomIndex (graph.certifiedEncoding first) ≃
      SourceAtomIndex (graph.certifiedEncoding second) :=
  (sourceAtomEquiv graph first).symm.trans (sourceAtomEquiv graph second)

/-- The two atom equivalences differ exactly by the common index permutation. -/
theorem sourceAtomEquiv_trans (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) :
    (sourceAtomEquiv graph first).trans (encodedIndexEquiv graph first second) =
      sourceAtomEquiv graph second := by
  ext atom
  simp only [Equiv.trans_apply, encodedIndexEquiv, Equiv.symm_apply_apply]

/-- Relabelling a typed interaction along a bijection of finite index types.  Constructor role,
direction, haptic support and electron counts are preserved; only atom identities move. -/
def typedRelabel {n m : ℕ} (equivalent : Fin n ≃ Fin m) :
    InteractionRoles.TypedInteraction n → InteractionRoles.TypedInteraction m
  | InteractionRoles.TypedInteraction.ordinaryBond data =>
      InteractionRoles.TypedInteraction.ordinaryBond
        ⟨data.bondOrder, equivalent data.left, equivalent data.right,
          fun equal => data.distinct (equivalent.injective equal)⟩
  | InteractionRoles.TypedInteraction.directedCoordination data =>
      InteractionRoles.TypedInteraction.directedCoordination
        ⟨equivalent data.donor, equivalent data.acceptor,
          fun equal => data.distinct (equivalent.injective equal)⟩
  | InteractionRoles.TypedInteraction.haptic data =>
      InteractionRoles.TypedInteraction.haptic
        ⟨equivalent data.centre, data.donors.map equivalent,
          by simpa using data.nonempty,
          data.nodup.map equivalent.injective,
          by
            intro member
            rcases List.mem_map.mp member with ⟨donor, donorMem, equal⟩
            exact data.centreNotMem (by
              have hd : donor = data.centre := equivalent.injective equal
              simpa [hd] using donorMem)⟩
  | InteractionRoles.TypedInteraction.multicenter data =>
      InteractionRoles.TypedInteraction.multicenter
        ⟨data.participants.map equivalent, data.nodup.map equivalent.injective,
          by simpa using data.arity, data.electronCount⟩
  | InteractionRoles.TypedInteraction.delocalized data =>
      InteractionRoles.TypedInteraction.delocalized
        ⟨data.participants.map equivalent, data.nodup.map equivalent.injective,
          by simpa using data.arity, data.electronCount⟩

/-- Relabelling commutes with encoding a physical role, provided the atom equivalences differ by
exactly that relabelling. -/
theorem typedRelabel_toTypedInteraction {n m : ℕ} (equivalent : Fin n ≃ Fin m)
    (e : V ≃ Fin n) (role : PhysicalRole V) :
    typedRelabel equivalent (role.toTypedInteraction e) =
      role.toTypedInteraction (e.trans equivalent) := by
  cases role <;>
    simp [typedRelabel, PhysicalRole.toTypedInteraction]

/-- Changing the enumeration transports the geometry channel by the common index permutation. -/
theorem enumeration_transport_conformation (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (state : JointState graph) :
    (encodeJoint graph second state).conformation =
      MolecularConformation.reindex (encodedIndexEquiv graph first second)
        (encodeJoint graph first state).conformation := by
  show MolecularConformation.reindex (sourceAtomEquiv graph second) state.conformation =
    MolecularConformation.reindex (encodedIndexEquiv graph first second)
      (MolecularConformation.reindex (sourceAtomEquiv graph first) state.conformation)
  rw [← MolecularConformation.reindex_trans]
  rw [sourceAtomEquiv_trans graph first second]

/-- Changing the enumeration transports every typed role by the same common index permutation.
No channel is relabelled by an independently chosen equivalence. -/
theorem enumeration_transport_role (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (state : JointState graph)
    (index : Fin graph.interactions.length) :
    ((encodeJoint graph second state).decorations index).typed =
      typedRelabel (encodedIndexEquiv graph first second)
        (((encodeJoint graph first state).decorations index).typed) := by
  show (state.roleAt index).toTypedInteraction (sourceAtomEquiv graph second) =
    typedRelabel (encodedIndexEquiv graph first second)
      ((state.roleAt index).toTypedInteraction (sourceAtomEquiv graph first))
  rw [typedRelabel_toTypedInteraction, sourceAtomEquiv_trans graph first second]

/-- Combined statement: under a change of enumeration, the joint geometry and every typed role
are transported by the one common index permutation. -/
theorem enumeration_transport_joint (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (state : JointState graph) :
    (encodeJoint graph second state).conformation =
        MolecularConformation.reindex (encodedIndexEquiv graph first second)
          (encodeJoint graph first state).conformation ∧
      (∀ index,
        ((encodeJoint graph second state).decorations index).typed =
          typedRelabel (encodedIndexEquiv graph first second)
            (((encodeJoint graph first state).decorations index).typed)) :=
  ⟨enumeration_transport_conformation graph first second state,
    fun index => enumeration_transport_role graph first second state index⟩

/-! ## Source channels remain absent -/

/-- The certified source built by the encoding still has no optional spatial channel.  The real
conformation in the joint state is an explicit addition, never a reinterpretation of absent
spatial evidence. -/
@[simp] theorem encodedJoint_spatial? (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) :
    (graph.certifiedEncoding e).input.spatial? = none := rfl

/-- The certified source built by the encoding still has no optional diagram channel. -/
@[simp] theorem encodedJoint_diagram? (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) :
    (graph.certifiedEncoding e).input.diagram? = none := rfl

/-! ## Broad independent joint states with a partial ordered role ledger

The strict `JointState` above requires a `PhysicalRole` for **every** source interaction and keeps
the literal ordered agreement `supportKind = graph.interactions.get index`.  That is sound but
narrow: an aromatic, ionic, metallic, hydrogen-bonded or otherwise unspecified source edge cannot
be left without a role, and the opposite donor direction against one fixed source participant order
is not representable.

The broad state removes both restrictions.  Its independent role information is a finite *ordered
list* of annotations.  Each annotation names a concrete source interaction occurrence index
together with a role over the independent labels `V`, and records only the compatibility that
`InteractionRoles.Decorates` itself checks: exact semantic kind (including electron counts),
unordered participant support as a `Finset`, and equal participant count.  The source participant
order is not required to agree literally; for duplicate-free lists those conditions are exactly
permutation compatibility (`compatible_perm`).  Consequently:

* the ledger may be empty, partial, or contain several annotations of the same source index;
* list order and multiplicity are preserved (`List.map` never merges or deduplicates);
* the source interaction graph is never modified, and no role is demanded for an unannotated edge;
* opposite donor directions against the same source participant order are both compatible
  (`compatible_directed_swap`).

Encoding uses the *same* atom equivalence `sourceAtomEquiv graph e` as the graph and the geometry,
and produces the existing `InteractionRoles.RoleLedger` over the encoded certified source.  No
encoded ledger is an input: the independent input carries only `List (BroadAnnotation graph)`.
Decoding is exact on the whole state (geometry together with the entire ordered ledger), and the
strict `JointState` result is recovered as the restriction to a full ordered ledger (`ofStrict`,
`strict_joint_encoding_left_inverse_restricted`).
-/

/-- The ordered participant list carried by a physical role. -/
def PhysicalRole.supportList {V : Type*} (role : PhysicalRole V) : List V :=
  role.supportKind.1

/-- The semantic kind, including any electron count, carried by a physical role. -/
def PhysicalRole.kind {V : Type*} (role : PhysicalRole V) : SemanticInteractionKind :=
  role.supportKind.2

/-- The unordered participant support of a physical role: the same view that role erasure keeps,
and the view against which `InteractionRoles.Decorates` checks a source interaction. -/
def PhysicalRole.supportFinset {V : Type*} [DecidableEq V] (role : PhysicalRole V) : Finset V :=
  role.supportList.toFinset

/-- The participant count carried by a physical role. -/
def PhysicalRole.supportLength {V : Type*} (role : PhysicalRole V) : ℕ :=
  role.supportList.length

/-- Every physical role has a duplicate-free ordered support; each constructor stores that
evidence. -/
theorem PhysicalRole.supportList_nodup {V : Type*} (role : PhysicalRole V) :
    role.supportList.Nodup := by
  cases role with
  | ordinaryBond bondOrder left right distinct =>
      simpa [PhysicalRole.supportList, PhysicalRole.supportKind] using
        (List.nodup_cons.mpr ⟨by simpa using distinct, List.nodup_singleton right⟩)
  | directed donor acceptor distinct =>
      simpa [PhysicalRole.supportList, PhysicalRole.supportKind] using
        (List.nodup_cons.mpr ⟨by simpa using distinct, List.nodup_singleton acceptor⟩)
  | haptic centre donors nonempty nodup centreNotMem =>
      simpa [PhysicalRole.supportList, PhysicalRole.supportKind] using
        (List.nodup_cons.mpr ⟨centreNotMem, nodup⟩)
  | multicenter participants nodup arity electronCount =>
      simpa [PhysicalRole.supportList, PhysicalRole.supportKind] using nodup
  | delocalized participants nodup arity electronCount =>
      simpa [PhysicalRole.supportList, PhysicalRole.supportKind] using nodup

/-- Reversing an explicit donor/acceptor direction leaves the unordered participant support
unchanged.  This is why the broad state can represent both directions against one fixed source
participant order. -/
theorem PhysicalRole.supportFinset_directed_swap {V : Type*} [DecidableEq V]
    {donor acceptor : V} (distinct : donor ≠ acceptor) :
    (PhysicalRole.directed donor acceptor distinct).supportFinset =
      (PhysicalRole.directed acceptor donor distinct.symm).supportFinset := by
  show ([donor, acceptor] : List V).toFinset = ([acceptor, donor] : List V).toFinset
  apply List.toFinset.ext
  intro atom
  simp [or_comm]

/-- Membership of an image value in the deduplicated image of a list, for an injective function. -/
theorem mem_map_toFinset_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (injective : Function.Injective f) (values : List α) (value : α) :
    f value ∈ (values.map f).toFinset ↔ value ∈ values := by
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨other, member, equal⟩
    simpa [injective equal] using member
  · intro member
    exact ⟨value, member, rfl⟩

/-- Deduplication commutes with mapping: equal unordered supports stay equal after applying any
function. -/
theorem toFinset_map_congr {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) {first second : List α} (equal : first.toFinset = second.toFinset) :
    (first.map f).toFinset = (second.map f).toFinset := by
  have member_iff : ∀ atom, atom ∈ first ↔ atom ∈ second := by
    intro atom
    rw [← List.mem_toFinset, ← List.mem_toFinset, equal]
  apply List.toFinset.ext
  intro value
  rw [List.mem_map, List.mem_map]
  constructor
  · rintro ⟨atom, member, equalValue⟩
    exact ⟨atom, (member_iff atom).mp member, equalValue⟩
  · rintro ⟨atom, member, equalValue⟩
    exact ⟨atom, (member_iff atom).mpr member, equalValue⟩

/-- For an injective function, equality of the deduplicated images implies equality of the
deduplicated sources. -/
theorem toFinset_map_injective_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (injective : Function.Injective f) {first second : List α}
    (equal : (first.map f).toFinset = (second.map f).toFinset) :
    first.toFinset = second.toFinset := by
  have member_iff : ∀ atom, atom ∈ first ↔ atom ∈ second := by
    intro atom
    rw [← mem_map_toFinset_iff f injective first atom,
      ← mem_map_toFinset_iff f injective second atom, equal]
  exact List.toFinset.ext member_iff

/-- The participant map used by the common encoding is injective, so unordered supports can be
compared before and after the transport in both directions. -/
theorem sourceAtomEquiv_val_injective (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) :
    Function.Injective (fun atom : V => ((sourceAtomEquiv graph e) atom).val) := by
  intro first second equal
  exact (sourceAtomEquiv graph e).injective (Fin.ext equal)

/-- Compatibility of one independent role annotation with one concrete source interaction
occurrence.  This is exactly the information checked by `InteractionRoles.Decorates` after the
common encoding: the same semantic kind (and hence electron count), the same unordered participant
support, and the same participant count.  The literal source participant order is **not** required
to coincide with the role's ordered support; for duplicate-free lists these conditions are exactly
permutation compatibility (`compatible_perm`). -/
def Compatible (graph : FiniteAtomInteractionHypergraph V)
    (index : Fin graph.interactions.length) (role : PhysicalRole V) : Prop :=
  role.supportFinset = (graph.interactions.get index).1.toFinset ∧
    role.kind = (graph.interactions.get index).2 ∧
    role.supportLength = (graph.interactions.get index).1.length

/-- One annotation of the broad ledger: a concrete source interaction occurrence index together
with an independent physical role that is compatible with that occurrence.

The index is an occurrence index into the actual ordered source interaction list, so duplicated
equal-valued source interactions remain separately addressable.  An annotation is *not* required to
exist for every source index: the ledger is an arbitrary finite list. -/
structure BroadAnnotation (graph : FiniteAtomInteractionHypergraph V) where
  index : Fin graph.interactions.length
  role : PhysicalRole V
  compatible : Compatible graph index role

/-- Extensionality for broad annotations.  The compatibility field is proposition-valued. -/
theorem BroadAnnotation.extEq {graph : FiniteAtomInteractionHypergraph V}
    {first second : BroadAnnotation graph}
    (index : first.index = second.index) (role : first.role = second.role) : first = second := by
  obtain ⟨firstIndex, firstRole, firstCompatible⟩ := first
  obtain ⟨secondIndex, secondRole, secondCompatible⟩ := second
  cases index
  cases role
  exact congrArg (BroadAnnotation.mk firstIndex firstRole)
    (Subsingleton.elim firstCompatible secondCompatible)

/-- Compatibility entails permutation compatibility with the source participant list: the role's
duplicate-free ordered support and the source's duplicate-free participant list have the same
elements as a `Finset`, hence are permutations. -/
theorem compatible_perm {graph : FiniteAtomInteractionHypergraph V}
    {index : Fin graph.interactions.length} {role : PhysicalRole V}
    (compatible : Compatible graph index role) :
    role.supportList.Perm (graph.interactions.get index).1 := by
  refine List.perm_of_nodup_nodup_toFinset_eq (PhysicalRole.supportList_nodup role)
    (graph.participants_nodup (graph.interactions.get index)
      (List.get_mem graph.interactions index)) ?_
  simpa [PhysicalRole.supportFinset] using compatible.1

/-- Reversing an explicit donor/acceptor direction preserves compatibility.  Both directions are
representable against the same fixed source participant order. -/
theorem compatible_directed_swap {graph : FiniteAtomInteractionHypergraph V}
    {index : Fin graph.interactions.length} {donor acceptor : V} (distinct : donor ≠ acceptor)
    (compatible : Compatible graph index (PhysicalRole.directed donor acceptor distinct)) :
    Compatible graph index (PhysicalRole.directed acceptor donor distinct.symm) := by
  obtain ⟨support, kind, length⟩ := compatible
  refine ⟨?_, ?_, ?_⟩
  · rw [← PhysicalRole.supportFinset_directed_swap distinct]
    exact support
  · simpa [PhysicalRole.kind, PhysicalRole.supportKind] using kind
  · simpa [PhysicalRole.supportLength, PhysicalRole.supportList, PhysicalRole.supportKind]
      using length

/-- A **broad independent joint physical state**: one real geometry over the independent atom
labels `V`, together with a finite ordered ledger of physical-role annotations.  The ledger is an
arbitrary list (empty, partial, or with repeated source indices); source interactions are not
modified and no role is demanded for an unannotated edge.  The input contains no encoded
`RoleLedger`; the annotations are independent of any enumeration of `V`. -/
structure BroadJointState (graph : FiniteAtomInteractionHypergraph V) where
  /-- One real point per independent source atom label. -/
  conformation : MolecularConformation V
  /-- Finite ordered role ledger: order and multiplicity are those of the list. -/
  ledger : List (BroadAnnotation graph)

namespace BroadJointState

/-- Extensionality for broad joint states. -/
theorem extEq {graph : FiniteAtomInteractionHypergraph V}
    {first second : BroadJointState graph}
    (conformation : first.conformation = second.conformation)
    (ledger : first.ledger = second.ledger) : first = second := by
  obtain ⟨firstConformation, firstLedger⟩ := first
  obtain ⟨secondConformation, secondLedger⟩ := second
  cases conformation
  cases ledger
  rfl

/-- The broad state with an empty ledger: a valid state in which every source interaction is left
completely untouched.  This is impossible for the strict `JointState`. -/
def empty (graph : FiniteAtomInteractionHypergraph V)
    (conformation : MolecularConformation V) : BroadJointState graph :=
  { conformation := conformation, ledger := [] }

end BroadJointState

/-- The encoded broad joint state.  It lives over `graph.certifiedEncoding e`: the geometry is a
source-indexed real conformation and the ledger is the existing `InteractionRoles.RoleLedger` over
the encoded certified source. -/
structure EncodedBroadJointState (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) where
  /-- Real geometry over the encoded certified source atom index. -/
  conformation : SourceConformation (graph.certifiedEncoding e)
  /-- Existing role ledger over the encoded source. -/
  ledger : InteractionRoles.RoleLedger (graph.certifiedEncoding e).input

/-! ### The encoded decoration of one broad annotation -/

/-- An independent annotation, encoded through the common atom equivalence, satisfies exactly the
existing `InteractionRoles.Decorates` relation at the encoded occurrence index. -/
theorem broadDecorates (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (annotation : BroadAnnotation graph) :
    InteractionRoles.Decorates (graph.certifiedEncoding e).input.molecule
      (encodedIndex graph e annotation.index)
      (annotation.role.toTypedInteraction (sourceAtomEquiv graph e)) := by
  obtain ⟨support, kind, length⟩ := annotation.compatible
  have sourceSupport : (annotation.role.supportKind.1).toFinset =
      (graph.interactions.get annotation.index).1.toFinset := support
  have sourceKind : annotation.role.supportKind.2 =
      (graph.interactions.get annotation.index).2 := kind
  have sourceLength : annotation.role.supportKind.1.length =
      (graph.interactions.get annotation.index).1.length := length
  refine ⟨?_, ?_⟩
  · refine InteractionRoles.RoleErasedInteraction.ext ?_ ?_
    · show (annotation.role.toTypedInteraction (sourceAtomEquiv graph e)).erase.participants.toFinset =
        ((graph.certifiedEncoding e).input.molecule.interactions.get
          (encodedIndex graph e annotation.index)).participants.toFinset
      rw [toTypedInteraction_erase graph e annotation.role, encoded_get graph e annotation.index]
      simpa only [FiniteAtomInteractionHypergraph.encodeInteraction] using
        (toFinset_map_congr (fun atom : V => ((sourceAtomEquiv graph e) atom).val) sourceSupport)
    · show (annotation.role.toTypedInteraction (sourceAtomEquiv graph e)).erase.kind =
        ((graph.certifiedEncoding e).input.molecule.interactions.get
          (encodedIndex graph e annotation.index)).kind
      rw [toTypedInteraction_erase graph e annotation.role, encoded_get graph e annotation.index]
      simpa only [FiniteAtomInteractionHypergraph.encodeInteraction] using sourceKind
  · show (annotation.role.toTypedInteraction (sourceAtomEquiv graph e)).erase.participants.length =
      ((graph.certifiedEncoding e).input.molecule.interactions.get
        (encodedIndex graph e annotation.index)).participants.length
    rw [toTypedInteraction_erase graph e annotation.role, encoded_get graph e annotation.index]
    simpa [FiniteAtomInteractionHypergraph.encodeInteraction, PhysicalRole.supportLength,
      PhysicalRole.supportList] using sourceLength

/-- Build the existing role decoration for one broad annotation at its encoded occurrence index. -/
def broadDecoration (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (annotation : BroadAnnotation graph) :
    InteractionRoles.RoleDecoration (graph.certifiedEncoding e).input.molecule :=
  InteractionRoles.RoleDecoration.ofDecorates (encodedIndex graph e annotation.index)
    (annotation.role.toTypedInteraction (sourceAtomEquiv graph e))
    (broadDecorates graph e annotation)

@[simp] theorem broadDecoration_index (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (annotation : BroadAnnotation graph) :
    (broadDecoration graph e annotation).index = encodedIndex graph e annotation.index := rfl

@[simp] theorem broadDecoration_typed (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (annotation : BroadAnnotation graph) :
    (broadDecoration graph e annotation).typed =
      annotation.role.toTypedInteraction (sourceAtomEquiv graph e) := rfl

/-- Encode a broad independent joint state.  The geometry is reindexed by the common atom
equivalence, and the ordered ledger is transported entry by entry to a list of existing
`RoleDecoration`s, preserving order and multiplicity.  No channel uses a different enumeration. -/
def encodeBroad (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : BroadJointState graph) :
    EncodedBroadJointState graph e where
  conformation := MolecularConformation.reindex (sourceAtomEquiv graph e) state.conformation
  ledger := { decorations := state.ledger.map (broadDecoration graph e) }

/-- The encoded ledger decorations are exactly the entrywise images of the independent ordered
ledger.  In particular the independent list order and multiplicity are preserved; equal-valued
annotations are neither merged nor reordered. -/
@[simp] theorem encodeBroad_ledger_decorations (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : BroadJointState graph) :
    (encodeBroad graph e state).ledger.decorations =
      state.ledger.map (broadDecoration graph e) := rfl

/-- Encoding the broad ledger leaves the encoded source exactly unchanged. -/
@[simp] theorem encodeBroad_ledger_eraseSource (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : BroadJointState graph) :
    (encodeBroad graph e state).ledger.eraseSource = (graph.certifiedEncoding e).input := rfl

@[simp] theorem encodeBroad_ledger_length (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : BroadJointState graph) :
    (encodeBroad graph e state).ledger.decorations.length = state.ledger.length := by
  simp [encodeBroad]

@[simp] theorem encodeBroad_empty_ledger (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (conformation : MolecularConformation V) :
    (encodeBroad graph e (BroadJointState.empty graph conformation)).ledger.decorations = [] := rfl

/-! ### Decoding a broad encoded state -/

/-- The source occurrence index corresponding to an encoded interaction index. -/
def sourceInteractionIndex (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.certifiedEncoding e).input.molecule.interactions.length) :
    Fin graph.interactions.length :=
  Fin.cast (FiniteAtomInteractionHypergraph.encode_interactions_length graph e) index

/-- The two index transports are inverse at every encoded occurrence index. -/
@[simp] theorem encodedIndex_sourceInteractionIndex (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.certifiedEncoding e).input.molecule.interactions.length) :
    encodedIndex graph e (sourceInteractionIndex graph e index) = index := by
  apply Fin.ext
  simp [encodedIndex, sourceInteractionIndex]

/-- The index transports are also inverse in the other direction. -/
@[simp] theorem sourceInteractionIndex_encodedIndex (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length) :
    sourceInteractionIndex graph e (encodedIndex graph e index) = index := by
  apply Fin.ext
  simp [encodedIndex, sourceInteractionIndex]

/-- The encoded interaction at an arbitrary encoded index is the encoding of the corresponding
source interaction. -/
theorem encoded_interaction_get (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.certifiedEncoding e).input.molecule.interactions.length) :
    (graph.certifiedEncoding e).input.molecule.interactions.get index =
      FiniteAtomInteractionHypergraph.encodeInteraction e
        (graph.interactions.get (sourceInteractionIndex graph e index)) := by
  rw [← encodedIndex_sourceInteractionIndex graph e index]
  exact encoded_get graph e (sourceInteractionIndex graph e index)

/-- Any existing `RoleDecoration` of the encoded source decodes to an independent annotation that
is compatible with the corresponding source occurrence.  This is the exact converse of
`broadDecorates`: the transported source participant order need not be reproduced literally. -/
theorem decodeCompatible (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (decoration : InteractionRoles.RoleDecoration (graph.certifiedEncoding e).input.molecule) :
    Compatible graph (sourceInteractionIndex graph e decoration.index)
      (decodeRole (sourceAtomEquiv graph e) decoration.typed) := by
  have hsource := encoded_interaction_get graph e decoration.index
  have herase : decoration.typed.erase =
      FiniteAtomInteractionHypergraph.encodeInteraction e
        (decodeRole (sourceAtomEquiv graph e) decoration.typed).supportKind := by
    have eraseEq := toTypedInteraction_erase graph e
      (PhysicalRole.ofTypedInteraction (sourceAtomEquiv graph e) decoration.typed)
    rw [PhysicalRole.toTypedInteraction_ofTypedInteraction] at eraseEq
    simpa [decodeRole] using eraseEq
  refine ⟨?_, ?_, ?_⟩
  · have hpart := decoration.erased_participants_toFinset
    rw [herase, hsource] at hpart
    exact toFinset_map_injective_of_injective
      (fun atom : V => ((sourceAtomEquiv graph e) atom).val)
      (sourceAtomEquiv_val_injective graph e)
      (first := (decodeRole (sourceAtomEquiv graph e) decoration.typed).supportKind.1)
      (second := (graph.interactions.get
        (sourceInteractionIndex graph e decoration.index)).1)
      (by
        simpa only [FiniteAtomInteractionHypergraph.encodeInteraction] using hpart)
  · have hkind := decoration.erased_kind
    rw [herase, hsource] at hkind
    simpa only [FiniteAtomInteractionHypergraph.encodeInteraction] using hkind
  · have hlength := decoration.erased_participants_length
    rw [herase, hsource] at hlength
    simpa [FiniteAtomInteractionHypergraph.encodeInteraction,
      PhysicalRole.supportLength, PhysicalRole.supportList] using hlength

/-- Decode one encoded decoration into an independent broad annotation. -/
def decodeBroadAnnotation (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V))
    (decoration : InteractionRoles.RoleDecoration (graph.certifiedEncoding e).input.molecule) :
    BroadAnnotation graph where
  index := sourceInteractionIndex graph e decoration.index
  role := decodeRole (sourceAtomEquiv graph e) decoration.typed
  compatible := decodeCompatible graph e decoration

/-- The broad compatibility relation is *exactly* the existing `Decorates` relation after the
common encoding: no information is added and none is dropped.  This is the precise statement that
the independent annotation compatibility matches `InteractionRoles.Decorates`, including its
required participant-length condition. -/
theorem compatible_iff_decorates (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (index : Fin graph.interactions.length)
    (role : PhysicalRole V) :
    Compatible graph index role ↔
      InteractionRoles.Decorates (graph.certifiedEncoding e).input.molecule
        (encodedIndex graph e index) (role.toTypedInteraction (sourceAtomEquiv graph e)) := by
  constructor
  · intro compatible
    exact broadDecorates graph e ⟨index, role, compatible⟩
  · intro decorates
    let decoration : InteractionRoles.RoleDecoration
        (graph.certifiedEncoding e).input.molecule :=
      InteractionRoles.RoleDecoration.ofDecorates (encodedIndex graph e index)
        (role.toTypedInteraction (sourceAtomEquiv graph e)) decorates
    have recovered : Compatible graph (sourceInteractionIndex graph e decoration.index)
        (decodeRole (sourceAtomEquiv graph e) decoration.typed) :=
      decodeCompatible graph e decoration
    have indexEq : sourceInteractionIndex graph e decoration.index = index := by
      show sourceInteractionIndex graph e (encodedIndex graph e index) = index
      exact sourceInteractionIndex_encodedIndex graph e index
    have roleEq : decodeRole (sourceAtomEquiv graph e) decoration.typed = role := by
      show decodeRole (sourceAtomEquiv graph e)
        (role.toTypedInteraction (sourceAtomEquiv graph e)) = role
      exact PhysicalRole.ofTypedInteraction_toTypedInteraction (sourceAtomEquiv graph e) role
    exact indexEq ▸ roleEq ▸ recovered

/-- Decode an encoded broad joint state: the geometry is reindexed by the inverse atom equivalence
and every encoded decoration is decoded to an independent annotation.  The list order and
multiplicity of the encoded ledger are preserved.  Decoding is total. -/
def decodeBroad (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : EncodedBroadJointState graph e) :
    BroadJointState graph where
  conformation := MolecularConformation.reindex (sourceAtomEquiv graph e).symm state.conformation
  ledger := state.ledger.decorations.map (decodeBroadAnnotation graph e)

/-- Decoding an encoded annotation returns exactly the original annotation: occurrence index,
role, direction, haptic support, electron counts and compatibility are all recovered. -/
theorem decodeBroadAnnotation_broadDecoration (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (annotation : BroadAnnotation graph) :
    decodeBroadAnnotation graph e (broadDecoration graph e annotation) = annotation := by
  apply BroadAnnotation.extEq
  · show sourceInteractionIndex graph e (encodedIndex graph e annotation.index) = annotation.index
    apply Fin.ext
    simp [sourceInteractionIndex, encodedIndex]
  · show decodeRole (sourceAtomEquiv graph e)
        (annotation.role.toTypedInteraction (sourceAtomEquiv graph e)) = annotation.role
    exact PhysicalRole.ofTypedInteraction_toTypedInteraction (sourceAtomEquiv graph e)
      annotation.role

/-! ## Exact inverse and whole-state results for the broad construction -/

/-- **Broad main theorem.**  Decoding the encoded image of a broad independent joint state
recovers the *entire* original state: the independent geometry together with the whole ordered
ledger, including order and multiplicity.  Both channels use the one common atom equivalence; this
is an exact joint inverse, not separate marginal statements. -/
theorem broad_joint_encoding_left_inverse (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : BroadJointState graph) :
    decodeBroad graph e (encodeBroad graph e state) = state := by
  obtain ⟨conformation, ledger⟩ := state
  apply BroadJointState.extEq
  · show MolecularConformation.reindex (sourceAtomEquiv graph e).symm
        (MolecularConformation.reindex (sourceAtomEquiv graph e) conformation) = conformation
    exact MolecularConformation.reindex_reindex (sourceAtomEquiv graph e) conformation
  · show (ledger.map (broadDecoration graph e)).map (decodeBroadAnnotation graph e) = ledger
    rw [List.map_map]
    have identity : (decodeBroadAnnotation graph e ∘ broadDecoration graph e) = id := by
      funext annotation
      exact decodeBroadAnnotation_broadDecoration graph e annotation
    rw [identity, List.map_id]

/-- Encoding is injective on broad states, because decoding is a left inverse on the whole state. -/
theorem encodeBroad_injective (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) : Function.Injective (encodeBroad graph e) := by
  intro first second equal
  have := congrArg (decodeBroad graph e) equal
  simpa [broad_joint_encoding_left_inverse graph e first,
    broad_joint_encoding_left_inverse graph e second] using this

/-- The broad joint record retains the geometry channel exactly. -/
theorem broad_joint_encoding_conformation (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : BroadJointState graph) :
    (decodeBroad graph e (encodeBroad graph e state)).conformation = state.conformation :=
  congrArg BroadJointState.conformation (broad_joint_encoding_left_inverse graph e state)

/-- The broad joint record retains the *whole ordered ledger* channel exactly. -/
theorem broad_joint_encoding_ledger (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (state : BroadJointState graph) :
    (decodeBroad graph e (encodeBroad graph e state)).ledger = state.ledger :=
  congrArg BroadJointState.ledger (broad_joint_encoding_left_inverse graph e state)

/-! ## Whole sets of broad states -/

/-- The image of an arbitrary set of broad independent states.  The whole set is encoded as a set;
it is never replaced by a product of independently chosen marginal sets. -/
def encodeBroadSet (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (states : Set (BroadJointState graph)) :
    Set (EncodedBroadJointState graph e) :=
  encodeBroad graph e '' states

/-- Exact membership in the encoded broad set. -/
theorem mem_encodeBroadSet_iff (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (states : Set (BroadJointState graph))
    (encoded : EncodedBroadJointState graph e) :
    encoded ∈ encodeBroadSet graph e states ↔
      ∃ state, state ∈ states ∧ encodeBroad graph e state = encoded :=
  Iff.rfl

/-- Exact membership recovery for a single broad state: its encoded image lies in the encoded set
exactly when the state lies in the original set. -/
theorem mem_encodeBroadSet_image_iff (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (states : Set (BroadJointState graph))
    (state : BroadJointState graph) :
    encodeBroad graph e state ∈ encodeBroadSet graph e states ↔ state ∈ states := by
  constructor
  · rintro ⟨other, otherMem, equal⟩
    have same : other = state := encodeBroad_injective graph e equal
    simpa [same] using otherMem
  · intro member
    exact ⟨state, member, rfl⟩

/-- Decoding the image of an arbitrary set of broad joint states recovers that set exactly.  This
is the whole-set form of the joint inverse, geometry and ledger together. -/
theorem decodeBroad_image_encodeBroadSet (graph : FiniteAtomInteractionHypergraph V)
    (e : V ≃ Fin (Fintype.card V)) (states : Set (BroadJointState graph)) :
    decodeBroad graph e '' encodeBroadSet graph e states = states := by
  rw [encodeBroadSet, Set.image_image]
  have composeIdentity :
      (fun state => decodeBroad graph e (encodeBroad graph e state)) = id := by
    funext state
    exact broad_joint_encoding_left_inverse graph e state
  rw [composeIdentity, Set.image_id]

/-! ## Change of enumeration transports the entire broad state together -/

/-- **Enumeration transport.**  Under a change of enumeration, the geometry and *every* entry of the
ordered ledger are transported by the one common index permutation `encodedIndexEquiv`.  The ledger
is compared position by position, so order and multiplicity are preserved and the statement covers
the geometry and the whole ledger jointly, not separate marginals.  Each decoration's occurrence
index is unchanged as a natural number. -/
theorem broad_enumeration_transport (graph : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) (state : BroadJointState graph) :
    (encodeBroad graph second state).conformation =
        MolecularConformation.reindex (encodedIndexEquiv graph first second)
          (encodeBroad graph first state).conformation ∧
      (encodeBroad graph second state).ledger.decorations.map
          (fun decoration => decoration.typed) =
        (encodeBroad graph first state).ledger.decorations.map
          (fun decoration =>
            typedRelabel (encodedIndexEquiv graph first second) decoration.typed) ∧
      (encodeBroad graph second state).ledger.decorations.map
          (fun decoration => decoration.index.val) =
        (encodeBroad graph first state).ledger.decorations.map
          (fun decoration => decoration.index.val) := by
  refine ⟨?_, ?_, ?_⟩
  · show MolecularConformation.reindex (sourceAtomEquiv graph second) state.conformation =
      MolecularConformation.reindex (encodedIndexEquiv graph first second)
        (MolecularConformation.reindex (sourceAtomEquiv graph first) state.conformation)
    rw [← MolecularConformation.reindex_trans, sourceAtomEquiv_trans graph first second]
  · show (state.ledger.map (broadDecoration graph second)).map
        (fun decoration => decoration.typed) =
      (state.ledger.map (broadDecoration graph first)).map
        (fun decoration => typedRelabel (encodedIndexEquiv graph first second) decoration.typed)
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro annotation _
    show annotation.role.toTypedInteraction (sourceAtomEquiv graph second) =
      typedRelabel (encodedIndexEquiv graph first second)
        (annotation.role.toTypedInteraction (sourceAtomEquiv graph first))
    rw [typedRelabel_toTypedInteraction, sourceAtomEquiv_trans graph first second]
  · show (state.ledger.map (broadDecoration graph second)).map
        (fun decoration => decoration.index.val) =
      (state.ledger.map (broadDecoration graph first)).map
        (fun decoration => decoration.index.val)
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro annotation _
    rfl

/-! ## The strict state as the restricted full-ordered-ledger case -/

/-- The broad annotation of a strict state at one source index.  The strict ordered agreement
implies the broad compatibility conditions, so the whole strict state embeds into the broad one. -/
def strictAnnotation (graph : FiniteAtomInteractionHypergraph V) (state : JointState graph)
    (index : Fin graph.interactions.length) : BroadAnnotation graph where
  index := index
  role := state.roleAt index
  compatible := by
    have agrees := state.agrees index
    refine ⟨?_, ?_, ?_⟩
    · simpa [PhysicalRole.supportFinset, PhysicalRole.supportList] using
        congrArg (fun edge => edge.1.toFinset) agrees
    · simpa [PhysicalRole.kind] using congrArg (fun edge => edge.2) agrees
    · simpa [PhysicalRole.supportLength, PhysicalRole.supportList] using
        congrArg (fun edge => edge.1.length) agrees

/-- The strict state as a broad state: the full ordered ledger with exactly one annotation per
source interaction.  This is the explicit embedding that names the original strict result as the
restriction of the broad construction. -/
def ofStrict (graph : FiniteAtomInteractionHypergraph V) (state : JointState graph) :
    BroadJointState graph where
  conformation := state.conformation
  ledger := List.ofFn (fun index : Fin graph.interactions.length =>
    strictAnnotation graph state index)

@[simp] theorem ofStrict_conformation (graph : FiniteAtomInteractionHypergraph V)
    (state : JointState graph) :
    (ofStrict graph state).conformation = state.conformation := rfl

/-- A mapping lemma for `List.ofFn`, used to describe the strict ledger by position. -/
theorem list_map_ofFn {α β : Type*} :
    ∀ {n : ℕ} (values : Fin n → α) (map : α → β),
      (List.ofFn values).map map = List.ofFn (fun index => map (values index))
  | 0, values, map => by simp [List.ofFn_zero]
  | n + 1, values, map => by
      rw [List.ofFn_succ, List.map_cons, List.ofFn_succ,
        list_map_ofFn (fun index : Fin n => values index.succ) map]

/-- The strict ledger has exactly one entry per source interaction: the full ordered ledger. -/
theorem ofStrict_ledger_length (graph : FiniteAtomInteractionHypergraph V)
    (state : JointState graph) :
    (ofStrict graph state).ledger.length = graph.interactions.length := by
  simp [ofStrict]

/-- The occurrence index of the strict ledger entry at position `k` is exactly `k`: the strict
ledger is the full ordered ledger, with one decoration per source occurrence. -/
theorem ofStrict_ledger_indices (graph : FiniteAtomInteractionHypergraph V)
    (state : JointState graph) :
    (ofStrict graph state).ledger.map BroadAnnotation.index =
      List.ofFn (fun index : Fin graph.interactions.length => index) := by
  change (List.ofFn (fun index : Fin graph.interactions.length =>
    strictAnnotation graph state index)).map BroadAnnotation.index = _
  rw [list_map_ofFn]
  rfl

/-- The roles in the strict ledger are exactly the strict role assignment. -/
theorem ofStrict_ledger_roles (graph : FiniteAtomInteractionHypergraph V)
    (state : JointState graph) :
    (ofStrict graph state).ledger.map BroadAnnotation.role =
      List.ofFn (fun index : Fin graph.interactions.length => state.roleAt index) := by
  change (List.ofFn (fun index : Fin graph.interactions.length =>
    strictAnnotation graph state index)).map BroadAnnotation.role = _
  rw [list_map_ofFn]
  rfl

/-- **The original strict result, explicitly named as a restriction.**  `JointState` is the
restricted case of `BroadJointState`, and `ofStrict` is its canonical full-ordered-ledger
embedding.  Applying the broad theorem to that embedding recovers the strict state, so the strict
theorem `joint_encoding_left_inverse` is the restriction of the broad result.  The strict theorem
itself is retained unchanged above. -/
theorem strict_joint_encoding_left_inverse_restricted
    (graph : FiniteAtomInteractionHypergraph V) (e : V ≃ Fin (Fintype.card V))
    (state : JointState graph) :
    decodeBroad graph e (encodeBroad graph e (ofStrict graph state)) = ofStrict graph state :=
  broad_joint_encoding_left_inverse graph e (ofStrict graph state)

end JointCoreEncoding
end TetraStereo.OneCenter
