import TetraStereo.OneCenter.AuthoritativeChemicalInput
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option linter.unusedSimpArgs false

































namespace TetraStereo.OneCenter
namespace InteractionRoles

/-! ## Role-carrying interaction data -/

/-- An ordinary two-centre bond with an explicit bond order.  The two source atoms are distinct. -/
structure OrdinaryBond (atomCount : ℕ) where
  bondOrder : ℕ
  left : Fin atomCount
  right : Fin atomCount
  distinct : left ≠ right

/-- Explicit directed-coordination evidence: `donor` donates to `acceptor`.  The direction is part
of the data; it is never read off the stored participant order. -/
structure DirectedCoordination (atomCount : ℕ) where
  donor : Fin atomCount
  acceptor : Fin atomCount
  distinct : donor ≠ acceptor

/-- A haptic / η ligand attached to one metal centre.  The donor support is nonempty, duplicate
free and disjoint from the centre; the hapticity is derived as `donors.length` rather than stored
as a redundant number. -/
structure HapticLigand (atomCount : ℕ) where
  centre : Fin atomCount
  donors : List (Fin atomCount)
  nonempty : donors ≠ []
  nodup : donors.Nodup
  centreNotMem : centre ∉ donors

namespace HapticLigand

/-- Hapticity η of the ligand, derived from the donor support. -/
def eta {atomCount : ℕ} (ligand : HapticLigand atomCount) : ℕ :=
  ligand.donors.length

@[simp] theorem eta_eq_length {atomCount : ℕ} (ligand : HapticLigand atomCount) :
    ligand.eta = ligand.donors.length := rfl

theorem eta_pos {atomCount : ℕ} (ligand : HapticLigand atomCount) : 0 < ligand.eta :=
  List.length_pos_iff.mpr ligand.nonempty

/-- The full participant list `centre :: donors` has length `η + 1`. -/
@[simp] theorem participantLength {atomCount : ℕ} (ligand : HapticLigand atomCount) :
    (ligand.centre.val :: ligand.donors.map Fin.val).length = ligand.eta + 1 := by
  simp [eta, add_comm]

theorem participantList_nodup {atomCount : ℕ} (ligand : HapticLigand atomCount) :
    (ligand.centre.val :: ligand.donors.map Fin.val).Nodup := by
  have hnot : ligand.centre.val ∉ ligand.donors.map Fin.val := by
    intro member
    rcases List.mem_map.mp member with ⟨donor, donorMem, same⟩
    have donorEq : donor = ligand.centre := Fin.val_inj.mp same
    exact ligand.centreNotMem (by simpa [donorEq] using donorMem)
  exact List.nodup_cons.mpr
    ⟨hnot, ligand.nodup.map (fun first second equal => Fin.val_inj.mp equal)⟩

end HapticLigand

/-- Finite multicenter participant data with an explicit electron count.  Arity at least two and
duplicate-freeness are part of the data, so there is no finite-size fixture. -/
structure Multicenter (atomCount : ℕ) where
  participants : List (Fin atomCount)
  nodup : participants.Nodup
  arity : 2 ≤ participants.length
  electronCount : ℕ

/-- Finite delocalized participant data with an explicit electron count. -/
structure Delocalized (atomCount : ℕ) where
  participants : List (Fin atomCount)
  nodup : participants.Nodup
  arity : 2 ≤ participants.length
  electronCount : ℕ

namespace Multicenter

theorem card_ge_two {atomCount : ℕ} (data : Multicenter atomCount) :
    2 ≤ data.participants.toFinset.card := by
  rw [List.toFinset_card_of_nodup data.nodup]
  exact data.arity

end Multicenter

namespace Delocalized

theorem card_ge_two {atomCount : ℕ} (data : Delocalized atomCount) :
    2 ≤ data.participants.toFinset.card := by
  rw [List.toFinset_card_of_nodup data.nodup]
  exact data.arity

end Delocalized

/-- The typed interaction vocabulary.  Every constructor is parameterized by source atoms
`Fin atomCount`, so participant bounds are automatic. -/
inductive TypedInteraction (atomCount : ℕ) where
  | ordinaryBond (data : OrdinaryBond atomCount)
  | directedCoordination (data : DirectedCoordination atomCount)
  | haptic (data : HapticLigand atomCount)
  | multicenter (data : Multicenter atomCount)
  | delocalized (data : Delocalized atomCount)

namespace TypedInteraction

/-! ### Smart constructors from explicit physical data -/

def bond {atomCount : ℕ} (bondOrder : ℕ) (left right : Fin atomCount)
    (distinct : left ≠ right) : TypedInteraction atomCount :=
  .ordinaryBond ⟨bondOrder, left, right, distinct⟩

def directed {atomCount : ℕ} (donor acceptor : Fin atomCount)
    (distinct : donor ≠ acceptor) : TypedInteraction atomCount :=
  .directedCoordination ⟨donor, acceptor, distinct⟩

def mkHaptic {atomCount : ℕ} (centre : Fin atomCount) (donors : List (Fin atomCount))
    (nonempty : donors ≠ []) (nodup : donors.Nodup) (centreNotMem : centre ∉ donors) :
    TypedInteraction atomCount :=
  .haptic ⟨centre, donors, nonempty, nodup, centreNotMem⟩

def mkMulticenter {atomCount : ℕ} (participants : List (Fin atomCount))
    (nodup : participants.Nodup) (arity : 2 ≤ participants.length) (electronCount : ℕ) :
    TypedInteraction atomCount :=
  .multicenter ⟨participants, nodup, arity, electronCount⟩

def mkDelocalized {atomCount : ℕ} (participants : List (Fin atomCount))
    (nodup : participants.Nodup) (arity : 2 ≤ participants.length) (electronCount : ℕ) :
    TypedInteraction atomCount :=
  .delocalized ⟨participants, nodup, arity, electronCount⟩

/-! ### Erasure to the existing semantic interaction vocabulary -/

/-- Erase the typed roles to the existing `SemanticInteraction` representation.  Participant atoms
are preserved exactly (including their order as derived from the typed data), as are the semantic
kind and every electron count. -/
def erase {atomCount : ℕ} : TypedInteraction atomCount → SemanticInteraction
  | .ordinaryBond data =>
      { participants := [data.left.val, data.right.val],
        kind := SemanticInteractionKind.covalent data.bondOrder }
  | .directedCoordination data =>
      { participants := [data.donor.val, data.acceptor.val],
        kind := SemanticInteractionKind.coordinate }
  | .haptic data =>
      { participants := data.centre.val :: data.donors.map Fin.val,
        kind := SemanticInteractionKind.coordinate }
  | .multicenter data =>
      { participants := data.participants.map Fin.val,
        kind := SemanticInteractionKind.multicenter data.electronCount }
  | .delocalized data =>
      { participants := data.participants.map Fin.val,
        kind := SemanticInteractionKind.delocalized data.electronCount }

@[simp] theorem erase_ordinaryBond {atomCount : ℕ} (data : OrdinaryBond atomCount) :
    (TypedInteraction.ordinaryBond data).erase =
      { participants := [data.left.val, data.right.val],
        kind := SemanticInteractionKind.covalent data.bondOrder } := rfl

@[simp] theorem erase_directedCoordination {atomCount : ℕ} (data : DirectedCoordination atomCount) :
    (TypedInteraction.directedCoordination data).erase =
      { participants := [data.donor.val, data.acceptor.val],
        kind := SemanticInteractionKind.coordinate } := rfl

@[simp] theorem erase_haptic {atomCount : ℕ} (data : HapticLigand atomCount) :
    (TypedInteraction.haptic data).erase =
      { participants := data.centre.val :: data.donors.map Fin.val,
        kind := SemanticInteractionKind.coordinate } := rfl

@[simp] theorem erase_multicenter {atomCount : ℕ} (data : Multicenter atomCount) :
    (TypedInteraction.multicenter data).erase =
      { participants := data.participants.map Fin.val,
        kind := SemanticInteractionKind.multicenter data.electronCount } := rfl

@[simp] theorem erase_delocalized {atomCount : ℕ} (data : Delocalized atomCount) :
    (TypedInteraction.delocalized data).erase =
      { participants := data.participants.map Fin.val,
        kind := SemanticInteractionKind.delocalized data.electronCount } := rfl

/-- Kind and electron count of a multicenter interaction are preserved exactly by erasure. -/
@[simp] theorem erase_multicenter_kind {atomCount : ℕ} (data : Multicenter atomCount) :
    (TypedInteraction.multicenter data).erase.kind =
      SemanticInteractionKind.multicenter data.electronCount := rfl

/-- Kind and electron count of a delocalized interaction are preserved exactly by erasure. -/
@[simp] theorem erase_delocalized_kind {atomCount : ℕ} (data : Delocalized atomCount) :
    (TypedInteraction.delocalized data).erase.kind =
      SemanticInteractionKind.delocalized data.electronCount := rfl

/-! ### Typed metadata projections (retained separately from the erased source) -/

/-- Donor of a directed-coordination interaction, if present.  This projection is part of the
typed metadata that the role-free source does not carry. -/
def donor? {atomCount : ℕ} : TypedInteraction atomCount → Option (Fin atomCount)
  | .directedCoordination data => some data.donor
  | _ => none

/-- Acceptor of a directed-coordination interaction, if present. -/
def acceptor? {atomCount : ℕ} : TypedInteraction atomCount → Option (Fin atomCount)
  | .directedCoordination data => some data.acceptor
  | _ => none

/-- Metal centre of a haptic interaction, if present. -/
def hapticCentre? {atomCount : ℕ} : TypedInteraction atomCount → Option (Fin atomCount)
  | .haptic data => some data.centre
  | _ => none

/-- Donor support of a haptic interaction, if present. -/
def hapticDonors? {atomCount : ℕ} : TypedInteraction atomCount → Option (List (Fin atomCount))
  | .haptic data => some data.donors
  | _ => none

/-- Electron count of a multicenter or delocalized interaction, if present. -/
def electronCount? {atomCount : ℕ} : TypedInteraction atomCount → Option ℕ
  | .multicenter data => some data.electronCount
  | .delocalized data => some data.electronCount
  | _ => none

/-! ### Structural well-formedness of the erasure

Every typed constructor already carries the required distinctness / nonemptiness / arity proofs, so
the erased interaction is well formed for the ambient `Fin atomCount` at every arity. -/

theorem erase_wellFormed {atomCount : ℕ} (typed : TypedInteraction atomCount) :
    typed.erase.WellFormed atomCount := by
  cases typed with
  | ordinaryBond data =>
      have hne : data.left.val ≠ data.right.val :=
        fun equal => data.distinct (Fin.val_inj.mp equal)
      refine ⟨?_, ?_, ?_⟩
      · simp [TypedInteraction.erase]
      · simpa [TypedInteraction.erase] using
          (List.nodup_cons.mpr ⟨by simpa using hne, List.nodup_singleton data.right.val⟩)
      · simp [TypedInteraction.erase, data.left.isLt, data.right.isLt]
  | directedCoordination data =>
      have hne : data.donor.val ≠ data.acceptor.val :=
        fun equal => data.distinct (Fin.val_inj.mp equal)
      refine ⟨?_, ?_, ?_⟩
      · simp [TypedInteraction.erase]
      · simpa [TypedInteraction.erase] using
          (List.nodup_cons.mpr ⟨by simpa using hne, List.nodup_singleton data.acceptor.val⟩)
      · simp [TypedInteraction.erase, data.donor.isLt, data.acceptor.isLt]
  | haptic data =>
      have hpos : 0 < data.donors.length := List.length_pos_iff.mpr data.nonempty
      refine ⟨?_, ?_, ?_⟩
      · simp only [TypedInteraction.erase]
        simp only [List.length_cons, List.length_map]
        exact Nat.succ_le_succ (Nat.succ_le_of_lt hpos)
      · simpa only [TypedInteraction.erase] using data.participantList_nodup
      · simp only [TypedInteraction.erase]
        rw [List.all_eq_true]
        intro atom atomMem
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp atomMem with rfl | atomMem
        · exact data.centre.isLt
        · rcases List.mem_map.mp atomMem with ⟨donor, _, rfl⟩
          exact donor.isLt
  | multicenter data =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [TypedInteraction.erase]
        simpa using data.arity
      · simp only [TypedInteraction.erase]
        exact data.nodup.map (fun first second equal => Fin.val_inj.mp equal)
      · simp only [TypedInteraction.erase]
        rw [List.all_eq_true]
        intro atom atomMem
        simp only [decide_eq_true_eq]
        rcases List.mem_map.mp atomMem with ⟨participant, _, rfl⟩
        exact participant.isLt
  | delocalized data =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [TypedInteraction.erase]
        simpa using data.arity
      · simp only [TypedInteraction.erase]
        exact data.nodup.map (fun first second equal => Fin.val_inj.mp equal)
      · simp only [TypedInteraction.erase]
        rw [List.all_eq_true]
        intro atom atomMem
        simp only [decide_eq_true_eq]
        rcases List.mem_map.mp atomMem with ⟨participant, _, rfl⟩
        exact participant.isLt

end TypedInteraction

/-! ## Role erasure and its non-injectivity -/

/-- Unordered role-erased view of an interaction: the participant **support** as a `Finset`
together with the semantic kind (which itself carries multicenter/delocalized electron counts).
This is a quotient/view that additionally forgets participant order and multiplicity, so it does
not retain all the information of a `SemanticInteraction`; it is exactly the information against
which a role assignment is checked. -/
structure RoleErasedInteraction where
  participants : Finset ℕ
  kind : SemanticInteractionKind
  deriving DecidableEq

/-- Extensionality for the unordered role-erased view. -/
@[ext] theorem RoleErasedInteraction.ext {first second : RoleErasedInteraction}
    (participants : first.participants = second.participants)
    (kind : first.kind = second.kind) : first = second := by
  cases first
  cases second
  simp_all

/-- Role-erased view of an existing semantic interaction.  Participant ordering and multiplicity
are discarded, matching the unordered reading of coordination participants used elsewhere in the
repository. -/
def roleErasedSupport (interaction : SemanticInteraction) : RoleErasedInteraction :=
  { participants := interaction.participants.toFinset, kind := interaction.kind }

namespace TypedInteraction

/-- Role erasure at the typed level. -/
def roleErase {atomCount : ℕ} (typed : TypedInteraction atomCount) : RoleErasedInteraction :=
  roleErasedSupport typed.erase

/-- Participant support of the erasure. -/
def participantFinset {atomCount : ℕ} (typed : TypedInteraction atomCount) : Finset ℕ :=
  typed.erase.participants.toFinset

theorem roleErase_participants {atomCount : ℕ} (typed : TypedInteraction atomCount) :
    typed.roleErase.participants = typed.participantFinset := rfl

theorem roleErase_kind {atomCount : ℕ} (typed : TypedInteraction atomCount) :
    typed.roleErase.kind = typed.erase.kind := rfl

/-- Directed-coordination erasure keeps the two participant atoms in donor/acceptor order. -/
@[simp] theorem roleErase_directed_donor_acceptor {atomCount : ℕ}
    (donor acceptor : Fin atomCount) (distinct : donor ≠ acceptor) :
    (TypedInteraction.directed donor acceptor distinct).erase.participants =
      [donor.val, acceptor.val] := rfl

/-- The role-erased view of `donor → acceptor` and of `acceptor → donor` is the same: both record
the same unordered participant support and the same `coordinate` kind.  This is exactly the
information loss on which the non-injectivity theorem below rests. -/
theorem directed_roleErase_swap {atomCount : ℕ} (donor acceptor : Fin atomCount)
    (distinct : donor ≠ acceptor) :
    (TypedInteraction.directed donor acceptor distinct).roleErase =
      (TypedInteraction.directed acceptor donor distinct.symm).roleErase := by
  have hset : (([donor.val, acceptor.val] : List ℕ).toFinset) =
      (([acceptor.val, donor.val] : List ℕ).toFinset) := by
    ext atom
    simp [List.mem_toFinset, or_comm]
  refine RoleErasedInteraction.ext ?_ ?_
  · simpa [TypedInteraction.roleErase, roleErasedSupport, TypedInteraction.directed,
      TypedInteraction.erase] using hset
  · rfl

theorem directed_ne_swap {atomCount : ℕ} (donor acceptor : Fin atomCount)
    (distinct : donor ≠ acceptor) :
    TypedInteraction.directed donor acceptor distinct ≠
      TypedInteraction.directed acceptor donor distinct.symm := by
  intro equal
  have same := congrArg TypedInteraction.donor? equal
  have donorEq : donor = acceptor := by
    simpa [TypedInteraction.directed, TypedInteraction.donor?] using same
  exact distinct donorEq

/-- Role erasure is not injective: the same role-erased binary coordination has two distinct typed
preimages.  In particular no function of the role-erased view can recover the donor direction. -/
theorem roleErase_not_injective {atomCount : ℕ} (donor acceptor : Fin atomCount)
    (distinct : donor ≠ acceptor) :
    ¬ Function.Injective (fun typed : TypedInteraction atomCount => typed.roleErase) := by
  intro injective
  have typedEq : TypedInteraction.directed donor acceptor distinct =
      TypedInteraction.directed acceptor donor distinct.symm :=
    injective (directed_roleErase_swap donor acceptor distinct)
  exact directed_ne_swap donor acceptor distinct typedEq

end TypedInteraction

/-! ## Decorating actual source interactions -/

/-- A typed interaction decorates a concrete source interaction when its role-erased view is
identical — same participant support and same kind/electron counts — and its erased participant
count is identical.  The stored source ordering is not used to decide roles, and no roles can be
attached to a source interaction with different atoms or a different kind. -/
def Decorates (molecule : SemanticMolecule) (index : Fin molecule.interactions.length)
    (typed : TypedInteraction molecule.atomCount) : Prop :=
  typed.roleErase = roleErasedSupport (molecule.interactions.get index) ∧
    typed.erase.participants.length = (molecule.interactions.get index).participants.length

namespace Decorates

variable {molecule : SemanticMolecule}
variable {index : Fin molecule.interactions.length}
variable {typed : TypedInteraction molecule.atomCount}

/-- The decoration preserves the exact participant support of the source interaction. -/
theorem participants_toFinset (decorates : Decorates molecule index typed) :
    typed.erase.participants.toFinset =
      (molecule.interactions.get index).participants.toFinset :=
  congrArg RoleErasedInteraction.participants decorates.1

/-- The decoration preserves the exact semantic kind (and hence any electron count stored in it). -/
theorem kind_eq (decorates : Decorates molecule index typed) :
    typed.erase.kind = (molecule.interactions.get index).kind :=
  congrArg RoleErasedInteraction.kind decorates.1

/-- The decoration preserves the participant count. -/
theorem participants_length (decorates : Decorates molecule index typed) :
    typed.erase.participants.length =
      (molecule.interactions.get index).participants.length :=
  decorates.2

/-- A typed interaction whose kind differs from the source interaction cannot decorate it. -/
theorem not_of_kind_ne (different : typed.erase.kind ≠ (molecule.interactions.get index).kind) :
    ¬ Decorates molecule index typed :=
  fun decorates => different (kind_eq decorates)

/-- A typed interaction whose participant support differs from the source interaction cannot
decorate it. -/
theorem not_of_participants_ne
    (different : typed.erase.participants.toFinset ≠
      (molecule.interactions.get index).participants.toFinset) :
    ¬ Decorates molecule index typed :=
  fun decorates => different (participants_toFinset decorates)

end Decorates

/-- Strict variant: the whole erased semantic interaction is literally the source interaction at
the given index.  This is available when the source already stores the participant ordering derived
from the typed data; the general `Decorates` relation is order-insensitive because the existing
coordinate reading is unordered. -/
def DecoratesExact (molecule : SemanticMolecule) (index : Fin molecule.interactions.length)
    (typed : TypedInteraction molecule.atomCount) : Prop :=
  typed.erase = molecule.interactions.get index

namespace DecoratesExact

variable {molecule : SemanticMolecule}
variable {index : Fin molecule.interactions.length}
variable {typed : TypedInteraction molecule.atomCount}

theorem toDecorates (exact : DecoratesExact molecule index typed) :
    Decorates molecule index typed := by
  refine ⟨?_, ?_⟩
  · simpa only [TypedInteraction.roleErase] using
      congrArg roleErasedSupport exact
  · rw [exact]

/-- Exact decoration gives literal source equality of the erased interaction. -/
theorem source_eq (exact : DecoratesExact molecule index typed) :
    typed.erase = molecule.interactions.get index := exact

end DecoratesExact

/-! ## Lossless role ledger tied to source indices -/

/-- One role decoration attached to one concrete interaction index of a source molecule.  The index
is `Fin molecule.interactions.length`, so duplicated equal-valued source interactions remain
separately addressable and the role data can never be attached to an unrelated list position. -/
structure RoleDecoration (molecule : SemanticMolecule) where
  index : Fin molecule.interactions.length
  typed : TypedInteraction molecule.atomCount
  decorates : Decorates molecule index typed

namespace RoleDecoration

variable {molecule : SemanticMolecule}

/-- Constructor from an explicit decoration proof. -/
def ofDecorates (index : Fin molecule.interactions.length)
    (typed : TypedInteraction molecule.atomCount)
    (decorates : Decorates molecule index typed) : RoleDecoration molecule :=
  { index := index, typed := typed, decorates := decorates }

/-- Constructor from literal erased equality to a source interaction. -/
def ofExact (index : Fin molecule.interactions.length)
    (typed : TypedInteraction molecule.atomCount)
    (exact : DecoratesExact molecule index typed) : RoleDecoration molecule :=
  { index := index, typed := typed, decorates := exact.toDecorates }

/-- The decorated entry really points at an existing source interaction. -/
theorem index_is_lt (decoration : RoleDecoration molecule) :
    decoration.index.val < molecule.interactions.length :=
  decoration.index.isLt

/-- The typed metadata is retained separately: the stored typed interaction exists, and its
erasure agrees with the source interaction on participant support. -/
theorem erased_participants_toFinset (decoration : RoleDecoration molecule) :
    decoration.typed.erase.participants.toFinset =
      (molecule.interactions.get decoration.index).participants.toFinset :=
  Decorates.participants_toFinset decoration.decorates

/-- The typed metadata agrees with the source interaction on kind and electron count. -/
theorem erased_kind (decoration : RoleDecoration molecule) :
    decoration.typed.erase.kind =
      (molecule.interactions.get decoration.index).kind :=
  Decorates.kind_eq decoration.decorates

/-- The typed metadata agrees with the source interaction on participant count. -/
theorem erased_participants_length (decoration : RoleDecoration molecule) :
    decoration.typed.erase.participants.length =
      (molecule.interactions.get decoration.index).participants.length :=
  decoration.decorates.2

/-- If two source entries are literally equal (duplicated same-valued interactions), a decoration
of one index is also a decoration of the other; the ledger still records the chosen index. -/
theorem of_source_eq {typed : TypedInteraction molecule.atomCount}
    {first second : Fin molecule.interactions.length}
    (same : molecule.interactions.get first = molecule.interactions.get second)
    (decorates : Decorates molecule first typed) :
    Decorates molecule second typed := by
  refine ⟨?_, ?_⟩
  · rw [← same]
    exact decorates.1
  · rw [← same]
    exact decorates.2

end RoleDecoration

/-- A finite role ledger over a source.  It never changes the source; erasing it returns the exact
original source, while the decorations retain role information the source lacks. -/
structure RoleLedger (source : AuthoritativeChemicalInput) where
  decorations : List (RoleDecoration source.molecule)

namespace RoleLedger

variable {source : AuthoritativeChemicalInput}

/-- Erase the whole role ledger.  The result is the original source, by definition. -/
def eraseSource (_ledger : RoleLedger source) : AuthoritativeChemicalInput := source

@[simp] theorem eraseSource_eq (ledger : RoleLedger source) :
    ledger.eraseSource = source := rfl

/-- The empty ledger: a lossless embedding of a source with no role information. -/
def empty (source : AuthoritativeChemicalInput) : RoleLedger source :=
  { decorations := [] }

@[simp] theorem empty_eraseSource (source : AuthoritativeChemicalInput) :
    (empty source).eraseSource = source := rfl

end RoleLedger

/-- An enriched source is the original source together with a role ledger.  This is the only
sense in which the old input round-trips: dropping the ledger gives the source back exactly, but
the source alone does not determine the ledger. -/
structure EnrichedSource where
  source : AuthoritativeChemicalInput
  ledger : RoleLedger source

namespace EnrichedSource

/-- Erase the role ledger, retaining only the original source. -/
def eraseRoles (enriched : EnrichedSource) : AuthoritativeChemicalInput :=
  enriched.source

@[simp] theorem eraseRoles_eq (enriched : EnrichedSource) :
    enriched.eraseRoles = enriched.source := rfl

/-- Reattach a ledger to its source. -/
def ofSource (source : AuthoritativeChemicalInput) (ledger : RoleLedger source) : EnrichedSource :=
  { source := source, ledger := ledger }

/-- Round-trip of the enriched object through source erasure and reattachment. -/
@[simp] theorem reattach (enriched : EnrichedSource) :
    ofSource enriched.eraseRoles enriched.ledger = enriched := by
  cases enriched
  rfl

/-- Role erasure does not change the molecule of the source. -/
@[simp] theorem eraseRoles_molecule (enriched : EnrichedSource) :
    enriched.eraseRoles.molecule = enriched.source.molecule := rfl

end EnrichedSource

/-! ## Enrichment from explicit physical data -/

/-- Explicit physical evidence for a directed coordination at one concrete source index.  The
caller supplies the donor and acceptor atoms and the fact that the source interaction at that index
has exactly this two-atom support, length two, and `coordinate` kind.  No role is read off the
stored participant order. -/
structure DirectedEnrichment (molecule : SemanticMolecule)
    (index : Fin molecule.interactions.length) where
  coordination : DirectedCoordination molecule.atomCount
  support : (molecule.interactions.get index).participants.toFinset =
    ([coordination.donor.val, coordination.acceptor.val] : List ℕ).toFinset
  length_two : (molecule.interactions.get index).participants.length = 2
  kind_coordinate : (molecule.interactions.get index).kind = SemanticInteractionKind.coordinate

namespace DirectedEnrichment

variable {molecule : SemanticMolecule} {index : Fin molecule.interactions.length}

/-- Build the typed decoration from the explicit physical evidence. -/
def toDecoration (evidence : DirectedEnrichment molecule index) : RoleDecoration molecule :=
  RoleDecoration.ofDecorates index
    (TypedInteraction.directed evidence.coordination.donor evidence.coordination.acceptor
      evidence.coordination.distinct)
    (by
      refine ⟨?_, ?_⟩
      · refine RoleErasedInteraction.ext ?_ ?_
        · simpa [TypedInteraction.roleErase, roleErasedSupport, TypedInteraction.directed,
            TypedInteraction.erase] using evidence.support.symm
        · simpa [TypedInteraction.roleErase, roleErasedSupport, TypedInteraction.directed,
            TypedInteraction.erase] using evidence.kind_coordinate.symm
      · exact evidence.length_two.symm)

/-- The constructed decoration keeps the explicitly supplied donor. -/
@[simp] theorem toDecoration_donor (evidence : DirectedEnrichment molecule index) :
    evidence.toDecoration.typed.donor? = some evidence.coordination.donor := rfl

/-- The constructed decoration keeps the explicitly supplied acceptor. -/
@[simp] theorem toDecoration_acceptor (evidence : DirectedEnrichment molecule index) :
    evidence.toDecoration.typed.acceptor? = some evidence.coordination.acceptor := rfl

end DirectedEnrichment

/-- Explicit physical evidence for a haptic / η ligand at one concrete source index.  The metal
centre, the donor support, and the fact that the source interaction's participant support and
length match the ligand are all supplied explicitly. -/
structure HapticEnrichment (molecule : SemanticMolecule)
    (index : Fin molecule.interactions.length) where
  ligand : HapticLigand molecule.atomCount
  support : (molecule.interactions.get index).participants.toFinset =
    (ligand.centre.val :: ligand.donors.map Fin.val).toFinset
  length_eq : (molecule.interactions.get index).participants.length =
    ligand.donors.length + 1
  kind_coordinate : (molecule.interactions.get index).kind = SemanticInteractionKind.coordinate

namespace HapticEnrichment

variable {molecule : SemanticMolecule} {index : Fin molecule.interactions.length}

/-- Build the typed decoration from the explicit physical evidence. -/
def toDecoration (evidence : HapticEnrichment molecule index) : RoleDecoration molecule :=
  RoleDecoration.ofDecorates index
    (TypedInteraction.mkHaptic evidence.ligand.centre evidence.ligand.donors
      evidence.ligand.nonempty evidence.ligand.nodup evidence.ligand.centreNotMem)
    (by
      refine ⟨?_, ?_⟩
      · refine RoleErasedInteraction.ext ?_ ?_
        · simpa [TypedInteraction.roleErase, roleErasedSupport, TypedInteraction.mkHaptic,
            TypedInteraction.erase] using evidence.support.symm
        · simpa [TypedInteraction.roleErase, roleErasedSupport, TypedInteraction.mkHaptic,
            TypedInteraction.erase] using evidence.kind_coordinate.symm
      · change (evidence.ligand.centre.val :: evidence.ligand.donors.map Fin.val).length =
          (molecule.interactions.get index).participants.length
        rw [List.length_cons, List.length_map, evidence.length_eq])

/-- The constructed decoration keeps the explicitly supplied metal centre. -/
@[simp] theorem toDecoration_centre (evidence : HapticEnrichment molecule index) :
    evidence.toDecoration.typed.hapticCentre? = some evidence.ligand.centre := rfl

/-- The constructed decoration keeps the explicitly supplied donor support. -/
@[simp] theorem toDecoration_donors (evidence : HapticEnrichment molecule index) :
    evidence.toDecoration.typed.hapticDonors? = some evidence.ligand.donors := rfl

end HapticEnrichment

/-! ## General enriched molecule constructor -/

/-- A semantically specified molecule built from source atoms and a list of typed interactions at
arbitrary finite arity.  The dependent type `List (TypedInteraction atoms.length)` guarantees that
every participant is a real source atom, so no separate bounds check is needed. -/
structure EnrichedSemanticMolecule where
  atoms : List SemanticAtom
  typedInteractions : List (TypedInteraction atoms.length)

namespace EnrichedSemanticMolecule

/-- The role-free semantic molecule obtained by erasing every typed interaction. -/
def toSemanticMolecule (molecule : EnrichedSemanticMolecule) : SemanticMolecule :=
  { atoms := molecule.atoms,
    interactions := molecule.typedInteractions.map TypedInteraction.erase }

@[simp] theorem toSemanticMolecule_atoms (molecule : EnrichedSemanticMolecule) :
    molecule.toSemanticMolecule.atoms = molecule.atoms := rfl

@[simp] theorem toSemanticMolecule_interactions (molecule : EnrichedSemanticMolecule) :
    molecule.toSemanticMolecule.interactions =
      molecule.typedInteractions.map TypedInteraction.erase := rfl

@[simp] theorem toSemanticMolecule_atomCount (molecule : EnrichedSemanticMolecule) :
    molecule.toSemanticMolecule.atomCount = molecule.atoms.length := rfl

/-- The role-free semantic molecule is structurally well formed at every arbitrary finite arity. -/
theorem toSemanticMolecule_structurallyWellFormed (molecule : EnrichedSemanticMolecule) :
    molecule.toSemanticMolecule.StructurallyWellFormed := by
  unfold SemanticMolecule.StructurallyWellFormed
  apply List.all_eq_true.mpr
  intro interaction membership
  rw [EnrichedSemanticMolecule.toSemanticMolecule_interactions] at membership
  rcases List.mem_map.mp membership with ⟨typed, _, rfl⟩
  exact
    (SemanticInteraction.wellFormed?_eq_true_iff typed.erase
      molecule.toSemanticMolecule.atomCount).mpr
      (by
        simpa [EnrichedSemanticMolecule.toSemanticMolecule, SemanticMolecule.atomCount]
          using TypedInteraction.erase_wellFormed typed)

/-- The source input with no spatial or diagram evidence attached. -/
def toAuthoritativeChemicalInput (molecule : EnrichedSemanticMolecule) :
    AuthoritativeChemicalInput :=
  { molecule := molecule.toSemanticMolecule }

@[simp] theorem toAuthoritativeChemicalInput_molecule (molecule : EnrichedSemanticMolecule) :
    molecule.toAuthoritativeChemicalInput.molecule = molecule.toSemanticMolecule := rfl

/-- The constructed source input is structurally well formed. -/
theorem toAuthoritativeChemicalInput_structurallyWellFormed
    (molecule : EnrichedSemanticMolecule) :
    molecule.toAuthoritativeChemicalInput.StructurallyWellFormed := by
  refine ⟨molecule.toSemanticMolecule_structurallyWellFormed, ?_, ?_⟩
  · simp [AuthoritativeChemicalInput.SpatialIndicesWellFormed,
      EnrichedSemanticMolecule.toAuthoritativeChemicalInput]
  · simp [AuthoritativeChemicalInput.DiagramIndicesWellFormed,
      EnrichedSemanticMolecule.toAuthoritativeChemicalInput]

/-- The index of a typed interaction inside the erased interaction list. -/
def ownIndex (molecule : EnrichedSemanticMolecule)
    (index : Fin molecule.typedInteractions.length) :
    Fin molecule.toSemanticMolecule.interactions.length :=
  ⟨index.val, by
    simp [EnrichedSemanticMolecule.toSemanticMolecule, index.isLt]⟩

/-- Every typed interaction is exactly the erasure of the semantic interaction at its own index.
This is the strict, literal attachment property for molecules constructed from typed data. -/
theorem decoratesExact_own_index (molecule : EnrichedSemanticMolecule)
    (index : Fin molecule.typedInteractions.length) :
    DecoratesExact molecule.toSemanticMolecule (molecule.ownIndex index)
      (molecule.typedInteractions.get index) := by
  unfold DecoratesExact
  simp [EnrichedSemanticMolecule.toSemanticMolecule, EnrichedSemanticMolecule.ownIndex,
    List.getElem_map]

/-- Consequently every typed interaction decorates its own source index. -/
theorem decorates_own_index (molecule : EnrichedSemanticMolecule)
    (index : Fin molecule.typedInteractions.length) :
    Decorates molecule.toSemanticMolecule (molecule.ownIndex index)
      (molecule.typedInteractions.get index) :=
  (decoratesExact_own_index molecule index).toDecorates

end EnrichedSemanticMolecule

/-! ## Source-atom label preservation -/

/-- Atom lookup in the role-free semantic molecule. -/
def atomLabelAt? (molecule : SemanticMolecule) (index : ℕ) : Option SemanticAtom :=
  listGet? molecule.atoms index

/-- Atom lookup in the enriched molecule. -/
def enrichedAtomLabelAt? (molecule : EnrichedSemanticMolecule) (index : ℕ) :
    Option SemanticAtom :=
  listGet? molecule.atoms index

namespace EnrichedSemanticMolecule

@[simp] theorem toSemanticMolecule_atomLabelAt? (molecule : EnrichedSemanticMolecule)
    (index : ℕ) :
    atomLabelAt? molecule.toSemanticMolecule index = enrichedAtomLabelAt? molecule index := rfl

@[simp] theorem toAuthoritativeChemicalInput_atomLabelAt?
    (molecule : EnrichedSemanticMolecule) (index : ℕ) :
    atomLabelAt? molecule.toAuthoritativeChemicalInput.molecule index =
      enrichedAtomLabelAt? molecule index := rfl

/-- If an atom is present at a position in the enriched molecule's source list, the same atom node
is present at that position in the erased semantic molecule. -/
theorem atomLabelAt?_exact (molecule : EnrichedSemanticMolecule) (index : ℕ)
    (atom : SemanticAtom) (found : enrichedAtomLabelAt? molecule index = some atom) :
    atomLabelAt? molecule.toSemanticMolecule index = some atom := by
  simpa using found

/-- Isotope mass number at a position. -/
def isotopeMassNumberAt? (molecule : EnrichedSemanticMolecule) (index : ℕ) :
    Option (Option ℕ) :=
  (enrichedAtomLabelAt? molecule index).map fun atom => atom.isotopeMassNumber?

/-- Formal charge at a position. -/
def formalChargeAt? (molecule : EnrichedSemanticMolecule) (index : ℕ) : Option ℤ :=
  (enrichedAtomLabelAt? molecule index).map fun atom => atom.formalCharge

/-- Unpaired-electron (radical) count at a position. -/
def unpairedElectronsAt? (molecule : EnrichedSemanticMolecule) (index : ℕ) : Option ℕ :=
  (enrichedAtomLabelAt? molecule index).map fun atom => atom.unpairedElectrons

/-- Constructing the role-free source preserves the complete atom node, hence isotopic label,
formal charge and radical state, position by position. -/
theorem source_labels_preserved (molecule : EnrichedSemanticMolecule) (index : ℕ) :
    atomLabelAt? molecule.toSemanticMolecule index = enrichedAtomLabelAt? molecule index ∧
      (atomLabelAt? molecule.toSemanticMolecule index).map
          (fun atom => atom.isotopeMassNumber?) =
        (enrichedAtomLabelAt? molecule index).map (fun atom => atom.isotopeMassNumber?) ∧
      (atomLabelAt? molecule.toSemanticMolecule index).map
          (fun atom => atom.formalCharge) =
        (enrichedAtomLabelAt? molecule index).map (fun atom => atom.formalCharge) ∧
      (atomLabelAt? molecule.toSemanticMolecule index).map
          (fun atom => atom.unpairedElectrons) =
        (enrichedAtomLabelAt? molecule index).map (fun atom => atom.unpairedElectrons) :=
  ⟨rfl, rfl, rfl, rfl⟩

end EnrichedSemanticMolecule

/-! ## Concrete non-recovery witness on a binary source

The source below has exactly one `coordinate` interaction over atoms `0` and `1`.  Both the
donor-`0`/acceptor-`1` and the donor-`1`/acceptor-`0` typed decorations satisfy the decoration
relation for the *same* source index.  Hence the old source alone cannot choose between them.
This module does not claim otherwise; the role direction must come from explicit physical evidence.
-/

/-- Carbon periodic identity, used only to build a minimal concrete source. -/
def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

/-- A carbon atom with ordinary isotopic composition. -/
def carbonAtom : SemanticAtom := { element := carbon }

/-- The minimal binary source: two source atoms and one `coordinate` interaction `[0, 1]`. -/
def binaryMolecule : SemanticMolecule :=
  { atoms := [carbonAtom, carbonAtom],
    interactions :=
      [{ participants := [0, 1], kind := SemanticInteractionKind.coordinate }] }

/-- The same source as an authoritative input. -/
def binarySource : AuthoritativeChemicalInput :=
  { molecule := binaryMolecule }

/-- Donor `0` → acceptor `1`. -/
def forwardCoordinate : TypedInteraction 2 :=
  TypedInteraction.directed (0 : Fin 2) (1 : Fin 2) (by decide)

/-- Donor `1` → acceptor `0`. -/
def reverseCoordinate : TypedInteraction 2 :=
  TypedInteraction.directed (1 : Fin 2) (0 : Fin 2) (by decide)

theorem binary_decorates_forward :
    Decorates binaryMolecule ⟨0, by decide⟩ forwardCoordinate := by
  refine ⟨?_, ?_⟩
  · refine RoleErasedInteraction.ext ?_ ?_
    · simp [TypedInteraction.roleErase, roleErasedSupport,
        TypedInteraction.directed, TypedInteraction.erase, forwardCoordinate, binaryMolecule]
      decide
    · simp [TypedInteraction.roleErase, roleErasedSupport,
        TypedInteraction.directed, TypedInteraction.erase, forwardCoordinate, binaryMolecule]
  · simp [TypedInteraction.directed, TypedInteraction.erase, forwardCoordinate, binaryMolecule]

theorem binary_decorates_reverse :
    Decorates binaryMolecule ⟨0, by decide⟩ reverseCoordinate := by
  refine ⟨?_, ?_⟩
  · refine RoleErasedInteraction.ext ?_ ?_
    · simp [TypedInteraction.roleErase, roleErasedSupport,
        TypedInteraction.directed, TypedInteraction.erase, reverseCoordinate, binaryMolecule]
      decide
    · simp [TypedInteraction.roleErase, roleErasedSupport,
        TypedInteraction.directed, TypedInteraction.erase, reverseCoordinate, binaryMolecule]
  · simp [TypedInteraction.directed, TypedInteraction.erase, reverseCoordinate, binaryMolecule]

theorem forwardCoordinate_ne_reverse : forwardCoordinate ≠ reverseCoordinate := by
  intro equal
  exact TypedInteraction.directed_ne_swap (0 : Fin 2) (1 : Fin 2) (by decide) (by
    simpa [forwardCoordinate, reverseCoordinate] using equal)

/-- No function can recover the lost donor roles from this old binary source: the same source index
admits two distinct typed decorations, so a recovery function would have to return both. -/
theorem no_binary_source_role_recovery :
    ¬ ∃ recover : AuthoritativeChemicalInput → TypedInteraction 2,
        ∀ (index : Fin binaryMolecule.interactions.length) (typed : TypedInteraction 2),
          Decorates binaryMolecule index typed → recover binarySource = typed := by
  rintro ⟨recover, recovers⟩
  have forwardEq : recover binarySource = forwardCoordinate :=
    recovers ⟨0, by decide⟩ forwardCoordinate binary_decorates_forward
  have reverseEq : recover binarySource = reverseCoordinate :=
    recovers ⟨0, by decide⟩ reverseCoordinate binary_decorates_reverse
  exact forwardCoordinate_ne_reverse (forwardEq.symm.trans reverseEq)

/-- The same statement at the role-erased level: role erasure has no left inverse (no recovery
function from the unordered role-erased view back to the typed interaction).  This is *not* a
statement about right inverses / sections in the other direction. -/
theorem no_roleErase_left_inverse :
    ¬ ∃ recover : RoleErasedInteraction → TypedInteraction 2,
        ∀ typed : TypedInteraction 2, recover typed.roleErase = typed := by
  rintro ⟨recover, recovers⟩
  have same : forwardCoordinate.roleErase = reverseCoordinate.roleErase := by
    simpa [forwardCoordinate, reverseCoordinate] using
      (TypedInteraction.directed_roleErase_swap (0 : Fin 2) (1 : Fin 2) (by decide))
  exact forwardCoordinate_ne_reverse (by
    rw [← recovers forwardCoordinate, ← recovers reverseCoordinate, same])

end InteractionRoles
end TetraStereo.OneCenter
