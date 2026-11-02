import TetraStereo.OneCenter.OrganicStereoIndependentElectronicEncoding
import TetraStereo.OneCenter.MultiCenterDetection
import TetraStereo.OneCenter.CIP
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoInventoryImplicitHMaterialization

open OrganicStereoElectronicSites
open OrganicStereoIndependentElectronicEncoding

/-!
# Materializing supplied implicit protium slots in a finite atom graph

This module bridges an *actually supplied* independent implicit-protium inventory to an expanded
finite atom/interaction graph.  The source is an arbitrary finite atom label type `V` together with
a graph `FiniteAtomInteractionHypergraph V` and an `IndependentElectronicSiteSource graph`; the only
count used here is the explicit `implicitProtia` field at each owner.  No count is inferred from
nuclear geometry, and no caller-supplied coverage table is demanded: the expansion enumerates the
full dependent sigma `Σ owner, Fin (count owner)`.

The construction is deliberately literal:

* old atoms are `Sum.inl v`, with exactly the original semantic atom data;
* for every supplied slot `h : Σ owner, Fin (implicitCount owner)` there is one tagged hydrogen
  atom `Sum.inr h`, with atomic number `1`, unspecified isotope mass number, formal charge `0`,
  unpaired electrons `0`, and no aromatic flag;
* every original interaction is lifted by replacing each participant `v` with `Sum.inl v`, keeping
  its order and kind exactly;
* one selected covalent pair interaction `[Sum.inl h.1, Sum.inr h]` with bond order `1` is added
  for every supplied slot.

The canonical projection `restore` reads only the old-atom restriction `v ↦ atomData (Sum.inl v)`
and the expanded interaction list.  It filters interactions whose participant list consists
entirely of old atoms and decodes those participants back to `V`; every interaction involving a
tagged hydrogen is dropped.  It does not receive the original graph as an argument.  The introduced
slot family is likewise decoded from the expanded interaction list by
`introducedSlotOfEdge?`/`introducedSlots`, not stored separately.

The decisive concrete fixture is a heavy-atom `CHBrClF` graph (carbon, bromine, chlorine, fluorine)
with exactly one supplied implicit-protium slot at carbon.  The heavy graph has carbon of degree
three and is therefore omitted by the four-neighbor detector; the expanded graph has five atoms,
carbon of degree four, four distinct direct CIP atom labels, and is detected as a tetrahedral
center with injective CIP keys.

Boundaries made explicit:

* lone pairs, vacancies, unpaired-electron positions and CIP reference slots are never turned into
  hydrogens; `nonProtiumPayload` retains them unchanged and reconstructs the supplied counts;
* the heavy-only graph is not called chemically false: it simply carries no implicit-protium
  inventory by itself, which is why the count is supplied through the source adapter;
* this is not a full arbitrary `SemanticMolecule` chemical-graph adapter.  The pair-bond graph view
  `toMoleculeGraph` interprets only two-participant `.covalent` interactions as bonds; other
  interaction kinds remain present in the expanded hypergraph but contribute bond order zero in
  that view.  The inventory expansion/projection theorems themselves are stated for arbitrary
  `SemanticInteractionKind` lists.
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Supplied implicit-protium multiplicity and tagged slots -/

/-- The supplied implicit-protium multiplicity at each atom label. -/
abbrev ImplicitProtiumMultiplicity (V : Type*) := V → ℕ

/-- A supplied implicit-protium slot: its owner and a bounded slot index. -/
abbrev HydrogenSlot {V : Type*} (count : V → ℕ) := Σ owner : V, Fin (count owner)

/-- Expanded atom labels: old atoms on the left, tagged materialized hydrogens on the right. -/
abbrev ExpandedLabel {V : Type*} (count : V → ℕ) := V ⊕ HydrogenSlot count

/-- The semantic atom attached to every materialized implicit protium. -/
def materializedHydrogenAtom : SemanticAtom where
  element :=
    { atomicNumber := 1
      positive := by decide
      atMost118 := by decide }
  isotopeMassNumber? := none
  formalCharge := 0
  unpairedElectrons := 0
  aromaticInput := false

@[simp] theorem materializedHydrogenAtom_atomicNumber :
    materializedHydrogenAtom.element.atomicNumber = 1 :=
  rfl

@[simp] theorem materializedHydrogenAtom_isotopeMassNumber :
    materializedHydrogenAtom.isotopeMassNumber? = none :=
  rfl

@[simp] theorem materializedHydrogenAtom_formalCharge :
    materializedHydrogenAtom.formalCharge = 0 :=
  rfl

@[simp] theorem materializedHydrogenAtom_unpairedElectrons :
    materializedHydrogenAtom.unpairedElectrons = 0 :=
  rfl

/-- Two slots with different owners are different slots. -/
theorem hydrogenSlot_owner_distinct {count : V → ℕ} {owner₁ owner₂ : V}
    (slot₁ : Fin (count owner₁)) (slot₂ : Fin (count owner₂))
    (different : owner₁ ≠ owner₂) :
    (⟨owner₁, slot₁⟩ : HydrogenSlot count) ≠ ⟨owner₂, slot₂⟩ := by
  intro equal
  exact different (congrArg (fun h : HydrogenSlot count => h.1) equal)

/-- Slots at one owner are equal exactly when their indices are equal. -/
theorem hydrogenSlot_ext_iff {count : V → ℕ} {owner : V}
    {slot₁ slot₂ : Fin (count owner)} :
    (⟨owner, slot₁⟩ : HydrogenSlot count) = ⟨owner, slot₂⟩ ↔ slot₁ = slot₂ := by
  constructor
  · intro equal
    exact Fin.ext (congrArg (fun h : HydrogenSlot count => h.2.val) equal)
  · intro equal
    rw [equal]

/-- Two slots with different indices at one owner are different slots. -/
theorem hydrogenSlot_slot_distinct {count : V → ℕ} {owner : V}
    {slot₁ slot₂ : Fin (count owner)} (different : slot₁ ≠ slot₂) :
    (⟨owner, slot₁⟩ : HydrogenSlot count) ≠ ⟨owner, slot₂⟩ := by
  intro equal
  exact different (hydrogenSlot_ext_iff.mp equal)

/-- The slot index is bounded by the supplied multiplicity. -/
theorem hydrogenSlot_slot_lt {count : V → ℕ} (h : HydrogenSlot count) :
    h.2.val < count h.1 :=
  h.2.isLt

/-- The tagged-hydrogen injection is injective. -/
theorem expanded_hydrogen_injective {count : V → ℕ} :
    Function.Injective (fun h : HydrogenSlot count => (Sum.inr h : ExpandedLabel count)) := by
  intro h₁ h₂ equal
  exact Sum.inr.inj equal

/-- An old atom is never the same expanded label as a tagged hydrogen. -/
theorem expanded_atom_inl_ne_hydrogen {count : V → ℕ} (v : V) (h : HydrogenSlot count) :
    (Sum.inl v : ExpandedLabel count) ≠ Sum.inr h := by
  intro equal
  exact Sum.inl_ne_inr equal

/-- The number of supplied slots is the sum of the supplied multiplicities. -/
theorem hydrogenSlot_card (count : V → ℕ) :
    Fintype.card (HydrogenSlot count) = (Finset.univ : Finset V).sum count := by
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl ?_
  intro owner _
  exact Fintype.card_fin (count owner)

/-! ## Expanded atom data and interactions -/

/-- Old atoms keep their semantic atom; every tagged hydrogen gets the materialized protium. -/
def expandedAtomData (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    ExpandedLabel count → SemanticAtom
  | Sum.inl v => graph.atomData v
  | Sum.inr _ => materializedHydrogenAtom

/-- An original interaction, with every participant tagged as an old atom. -/
@[reducible] def liftInteraction (count : V → ℕ)
    (edge : List V × SemanticInteractionKind) :
    List (ExpandedLabel count) × SemanticInteractionKind :=
  (edge.1.map (fun v => (Sum.inl v : ExpandedLabel count)), edge.2)

/-- The selected covalent pair interaction for one supplied slot. -/
@[reducible] def hydrogenBond (count : V → ℕ) (h : HydrogenSlot count) :
    List (ExpandedLabel count) × SemanticInteractionKind :=
  ([(Sum.inl h.1 : ExpandedLabel count), Sum.inr h], SemanticInteractionKind.covalent 1)

@[simp] theorem hydrogenBond_participants (count : V → ℕ) (h : HydrogenSlot count) :
    (hydrogenBond count h).1 = [(Sum.inl h.1 : ExpandedLabel count), Sum.inr h] :=
  rfl

@[simp] theorem hydrogenBond_kind (count : V → ℕ) (h : HydrogenSlot count) :
    (hydrogenBond count h).2 = SemanticInteractionKind.covalent 1 :=
  rfl

/-- The total enumeration of supplied slots. -/
noncomputable def hydrogenOccurrences (count : V → ℕ) : List (HydrogenSlot count) :=
  (Finset.univ : Finset (HydrogenSlot count)).toList

theorem mem_hydrogenOccurrences (count : V → ℕ) (h : HydrogenSlot count) :
    h ∈ hydrogenOccurrences count := by
  unfold hydrogenOccurrences
  rw [Finset.mem_toList]
  exact Finset.mem_univ h

theorem hydrogenOccurrences_nodup (count : V → ℕ) :
    (hydrogenOccurrences count).Nodup :=
  Finset.nodup_toList _

theorem hydrogenOccurrences_length (count : V → ℕ) :
    (hydrogenOccurrences count).length = Fintype.card (HydrogenSlot count) := by
  unfold hydrogenOccurrences
  rw [Finset.length_toList, Finset.card_univ]

/-- One selected bond for every supplied slot, in the canonical slot enumeration. -/
noncomputable def hydrogenBonds (count : V → ℕ) :
    List (List (ExpandedLabel count) × SemanticInteractionKind) :=
  (hydrogenOccurrences count).map (hydrogenBond count)

theorem hydrogenBond_injective (count : V → ℕ) :
    Function.Injective (hydrogenBond count) := by
  intro h₁ h₂ equal
  have member : Sum.inr h₁ ∈ (hydrogenBond count h₂).1 := by
    rw [← equal]
    simp [hydrogenBond]
  simpa [hydrogenBond] using member

theorem hydrogenBonds_nodup (count : V → ℕ) :
    (hydrogenBonds count).Nodup :=
  (hydrogenOccurrences_nodup count).map (hydrogenBond_injective count)

theorem hydrogenBonds_length (count : V → ℕ) :
    (hydrogenBonds count).length = Fintype.card (HydrogenSlot count) := by
  unfold hydrogenBonds
  rw [List.length_map, hydrogenOccurrences_length]

/-- The expanded graph: original atom data and interactions, plus one tagged hydrogen atom and one
selected covalent pair interaction per supplied implicit-protium slot. -/
@[reducible] noncomputable def expand (graph : FiniteAtomInteractionHypergraph V)
    (count : V → ℕ) : FiniteAtomInteractionHypergraph (ExpandedLabel count) where
  atomData := expandedAtomData graph count
  interactions := graph.interactions.map (liftInteraction count) ++ hydrogenBonds count
  arity_ge_two := by
    intro edge member
    rw [List.mem_append] at member
    rcases member with member | member
    · rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      simpa [liftInteraction] using graph.arity_ge_two original originalMember
    · rcases List.mem_map.mp member with ⟨h, _, rfl⟩
      simp [hydrogenBond]
  participants_nodup := by
    intro edge member
    rw [List.mem_append] at member
    rcases member with member | member
    · rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      simpa [liftInteraction] using
        (graph.participants_nodup original originalMember).map
          (f := Sum.inl) (fun _ _ equal => Sum.inl.inj equal)
    · rcases List.mem_map.mp member with ⟨h, _, rfl⟩
      simp [hydrogenBond, Sum.inl_ne_inr]

@[simp] theorem expand_atomData (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    (expand graph count).atomData = expandedAtomData graph count :=
  rfl

@[simp] theorem expand_interactions (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    (expand graph count).interactions =
      graph.interactions.map (liftInteraction count) ++ hydrogenBonds count :=
  rfl

/-- Old atoms keep their exact original semantic data. -/
@[simp] theorem expand_atomData_old (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ)
    (v : V) :
    (expand graph count).atomData (Sum.inl v) = graph.atomData v :=
  rfl

/-- Every materialized atom is the protium record. -/
@[simp] theorem expand_atomData_hydrogen (graph : FiniteAtomInteractionHypergraph V)
    (count : V → ℕ) (h : HydrogenSlot count) :
    (expand graph count).atomData (Sum.inr h) = materializedHydrogenAtom :=
  rfl

/-- Every original interaction participates in the expanded graph with its exact participants and
kind. -/
theorem expand_lift_mem (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ)
    {edge : List V × SemanticInteractionKind} (member : edge ∈ graph.interactions) :
    liftInteraction count edge ∈ (expand graph count).interactions := by
  rw [expand_interactions]
  exact List.mem_append_left _ (List.mem_map_of_mem member)

/-- Every supplied slot has its selected covalent hydrogen interaction in the expanded graph. -/
theorem expand_hydrogenBond_mem (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ)
    (h : HydrogenSlot count) :
    hydrogenBond count h ∈ (expand graph count).interactions := by
  rw [expand_interactions]
  exact List.mem_append_right _ (List.mem_map_of_mem (mem_hydrogenOccurrences count h))

/-- Total materialization: every supplied slot gets exactly its tagged atom and selected pair
interaction.  This is not a coverage table supplied by the caller; it is an enumeration of the
dependent sigma of all supplied `Fin` slots. -/
theorem expand_materializes_slot (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ)
    (h : HydrogenSlot count) :
    (expand graph count).atomData (Sum.inr h) = materializedHydrogenAtom ∧
      hydrogenBond count h ∈ (expand graph count).interactions ∧
      (hydrogenBond count h).1 = [(Sum.inl h.1 : ExpandedLabel count), Sum.inr h] ∧
      (hydrogenBond count h).2 = SemanticInteractionKind.covalent 1 :=
  ⟨rfl, expand_hydrogenBond_mem graph count h, rfl, rfl⟩

theorem expand_interactions_length (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    (expand graph count).interactions.length =
      graph.interactions.length + Fintype.card (HydrogenSlot count) := by
  rw [expand_interactions, List.length_append, List.length_map, hydrogenBonds_length]

/-! ## Canonical projection by old-atom restriction -/

/-- Decode a participant list whose entries are all old atoms.  Any tagged hydrogen makes the whole
interaction introduced, so decoding fails and the projection drops it. -/
def decodeOriginalParticipants (count : V → ℕ) :
    List (ExpandedLabel count) → Option (List V)
  | [] => some []
  | Sum.inl v :: rest => (decodeOriginalParticipants count rest).map (List.cons v)
  | Sum.inr _ :: _ => none

/-- Decode one expanded interaction if all its participants are old atoms. -/
def decodeOriginalInteraction (count : V → ℕ)
    (edge : List (ExpandedLabel count) × SemanticInteractionKind) :
    Option (List V × SemanticInteractionKind) :=
  (decodeOriginalParticipants count edge.1).map fun participants => (participants, edge.2)

@[simp] theorem decodeOriginalParticipants_map_inl (count : V → ℕ)
    (atoms : List V) :
    decodeOriginalParticipants count
        (atoms.map (fun v => (Sum.inl v : ExpandedLabel count))) = some atoms := by
  induction atoms with
  | nil => rfl
  | cons v rest ih =>
      simp [decodeOriginalParticipants, ih]

@[simp] theorem decodeOriginalInteraction_lift (count : V → ℕ)
    (edge : List V × SemanticInteractionKind) :
    decodeOriginalInteraction count (liftInteraction count edge) = some edge := by
  obtain ⟨participants, kind⟩ := edge
  simp [decodeOriginalInteraction, liftInteraction]

@[simp] theorem decodeOriginalInteraction_hydrogenBond (count : V → ℕ)
    (h : HydrogenSlot count) :
    decodeOriginalInteraction count (hydrogenBond count h) = none :=
  rfl

theorem decodeOriginalParticipants_length (count : V → ℕ)
    {labels : List (ExpandedLabel count)} {atoms : List V}
    (decoded : decodeOriginalParticipants count labels = some atoms) :
    atoms.length = labels.length := by
  induction labels generalizing atoms with
  | nil =>
      simp only [decodeOriginalParticipants, Option.some.injEq] at decoded
      subst atoms
      rfl
  | cons head rest ih =>
      cases head with
      | inl v =>
          simp only [decodeOriginalParticipants] at decoded
          rcases Option.map_eq_some_iff.mp decoded with ⟨tailAtoms, tailDecoded, atomsEq⟩
          subst atoms
          simp [ih tailDecoded]
      | inr h =>
          simp [decodeOriginalParticipants] at decoded

theorem mem_of_decodeOriginalParticipants (count : V → ℕ)
    {labels : List (ExpandedLabel count)} {atoms : List V}
    (decoded : decodeOriginalParticipants count labels = some atoms)
    {v : V} (member : v ∈ atoms) :
    (Sum.inl v : ExpandedLabel count) ∈ labels := by
  induction labels generalizing atoms with
  | nil =>
      simp only [decodeOriginalParticipants, Option.some.injEq] at decoded
      subst atoms
      simp at member
  | cons head rest ih =>
      cases head with
      | inr h =>
          simp [decodeOriginalParticipants] at decoded
      | inl w =>
          simp only [decodeOriginalParticipants] at decoded
          rcases Option.map_eq_some_iff.mp decoded with ⟨tailAtoms, tailDecoded, atomsEq⟩
          subst atoms
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih tailDecoded tailMember)

theorem decodeOriginalParticipants_nodup (count : V → ℕ)
    {labels : List (ExpandedLabel count)} {atoms : List V}
    (decoded : decodeOriginalParticipants count labels = some atoms)
    (nodup : labels.Nodup) : atoms.Nodup := by
  induction labels generalizing atoms with
  | nil =>
      simp only [decodeOriginalParticipants, Option.some.injEq] at decoded
      subst atoms
      simp
  | cons head rest ih =>
      cases head with
      | inr h =>
          simp [decodeOriginalParticipants] at decoded
      | inl v =>
          simp only [decodeOriginalParticipants] at decoded
          rcases Option.map_eq_some_iff.mp decoded with ⟨tailAtoms, tailDecoded, atomsEq⟩
          subst atoms
          have headFresh : (Sum.inl v : ExpandedLabel count) ∉ rest :=
            (List.nodup_cons.mp nodup).1
          have tailNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
          have atomsTailNodup : tailAtoms.Nodup := ih tailDecoded tailNodup
          have vFresh : v ∉ tailAtoms := by
            intro vMember
            exact headFresh (mem_of_decodeOriginalParticipants count tailDecoded vMember)
          exact List.nodup_cons.mpr ⟨vFresh, atomsTailNodup⟩

theorem decodeOriginalInteraction_eq_some_iff (count : V → ℕ)
    {edge : List (ExpandedLabel count) × SemanticInteractionKind}
    {decoded : List V × SemanticInteractionKind} :
    decodeOriginalInteraction count edge = some decoded ↔
      ∃ atoms : List V,
        decodeOriginalParticipants count edge.1 = some atoms ∧
          decoded = (atoms, edge.2) := by
  unfold decodeOriginalInteraction
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨atoms, decodedParticipants, rfl⟩
    exact ⟨atoms, decodedParticipants, rfl⟩
  · rintro ⟨atoms, decodedParticipants, rfl⟩
    exact ⟨atoms, decodedParticipants, rfl⟩

/-- The canonical projection.  It reads only `expanded.atomData` at old labels and
`expanded.interactions`; it never receives the original graph. -/
def restore (count : V → ℕ)
    (expanded : FiniteAtomInteractionHypergraph (ExpandedLabel count)) :
    FiniteAtomInteractionHypergraph V where
  atomData := fun v => expanded.atomData (Sum.inl v)
  interactions := expanded.interactions.filterMap (decodeOriginalInteraction count)
  arity_ge_two := by
    intro edge member
    rw [List.mem_filterMap] at member
    rcases member with ⟨original, _, decoded⟩
    rcases (decodeOriginalInteraction_eq_some_iff count).mp decoded with
      ⟨atoms, decodedParticipants, edgeEq⟩
    subst edge
    have lengthEq := decodeOriginalParticipants_length count decodedParticipants
    have originalArity := expanded.arity_ge_two original ‹original ∈ expanded.interactions›
    simpa [lengthEq] using originalArity
  participants_nodup := by
    intro edge member
    rw [List.mem_filterMap] at member
    rcases member with ⟨original, originalMember, decoded⟩
    rcases (decodeOriginalInteraction_eq_some_iff count).mp decoded with
      ⟨atoms, decodedParticipants, edgeEq⟩
    subst edge
    exact decodeOriginalParticipants_nodup count decodedParticipants
      (expanded.participants_nodup original originalMember)

@[simp] theorem restore_atomData (count : V → ℕ)
    (expanded : FiniteAtomInteractionHypergraph (ExpandedLabel count)) (v : V) :
    (restore count expanded).atomData v = expanded.atomData (Sum.inl v) :=
  rfl

@[simp] theorem restore_interactions (count : V → ℕ)
    (expanded : FiniteAtomInteractionHypergraph (ExpandedLabel count)) :
    (restore count expanded).interactions =
      expanded.interactions.filterMap (decodeOriginalInteraction count) :=
  rfl

/-- The projection's atom data is exactly the old-atom restriction of the expanded atom data. -/
theorem restore_atomData_eq_restriction     (count : V → ℕ)
    (expanded : FiniteAtomInteractionHypergraph (ExpandedLabel count)) :
    (restore count expanded).atomData =
      fun v => expanded.atomData (Sum.inl v) :=
  rfl

/-- Old interactions survive projection with their exact original form. -/
theorem filterMap_liftInteractions_eq (count : V → ℕ)
    (interactions : List (List V × SemanticInteractionKind)) :
    (interactions.map (liftInteraction count)).filterMap
        (decodeOriginalInteraction count) = interactions := by
  rw [List.filterMap_map]
  have functionEq :
      (decodeOriginalInteraction count ∘ liftInteraction count) = some := by
    funext edge
    exact decodeOriginalInteraction_lift count edge
  rw [functionEq, List.filterMap_some]

/-- Filtering by a constantly-`none` function removes everything. -/
theorem filterMap_none_eq_nil {α β : Type*} (items : List α) :
    items.filterMap (fun _ => (none : Option β)) = [] := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.filterMap_cons]
      exact ih

/-- Introduced hydrogen interactions are exactly the ones the projection drops. -/
theorem filterMap_hydrogenBonds_eq_nil (count : V → ℕ) :
    (hydrogenBonds count).filterMap (decodeOriginalInteraction count) = [] := by
  rw [hydrogenBonds, List.filterMap_map]
  have functionEq :
      (decodeOriginalInteraction count ∘ hydrogenBond count) = (fun _ => none) := by
    funext h
    exact decodeOriginalInteraction_hydrogenBond count h
  rw [functionEq]
  exact filterMap_none_eq_nil _

/-- The projection removes exactly the introduction block and recovers the original interaction
list. -/
theorem restore_interactions_expand     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    (restore count (expand graph count)).interactions = graph.interactions := by
  change (graph.interactions.map (liftInteraction count) ++ hydrogenBonds count).filterMap
      (decodeOriginalInteraction count) = graph.interactions
  rw [List.filterMap_append, filterMap_liftInteractions_eq,
    filterMap_hydrogenBonds_eq_nil, List.append_nil]

/-- The projection recovers the original atom data exactly. -/
theorem restore_atomData_expand     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    (restore count (expand graph count)).atomData = graph.atomData :=
  rfl

/-- A local structure equality principle for finite atom interaction hypergraphs. -/
theorem graph_ext     {left right : FiniteAtomInteractionHypergraph V}
    (atomDataEq : left.atomData = right.atomData)
    (interactionsEq : left.interactions = right.interactions) : left = right := by
  obtain ⟨leftAtoms, leftInteractions, leftArity, leftNodup⟩ := left
  obtain ⟨rightAtoms, rightInteractions, rightArity, rightNodup⟩ := right
  dsimp only at atomDataEq interactionsEq
  cases atomDataEq
  cases interactionsEq
  rfl

/-- Canonical projection recovers the original graph exactly. -/
theorem restore_expand     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    restore count (expand graph count) = graph := by
  apply graph_ext
  · exact restore_atomData_expand graph count
  · exact restore_interactions_expand graph count

/-- The projection is determined only by the expanded graph's old-atom restriction and interaction
list; the original graph is not an input. -/
theorem restore_determined_by_restriction     (count : V → ℕ)
    {left right : FiniteAtomInteractionHypergraph (ExpandedLabel count)}
    (atomDataEq : (fun v => left.atomData (Sum.inl v)) =
      (fun v => right.atomData (Sum.inl v)))
    (interactionsEq : left.interactions = right.interactions) :
    restore count left = restore count right := by
  apply graph_ext
  · exact atomDataEq
  · change left.interactions.filterMap (decodeOriginalInteraction count) =
      right.interactions.filterMap (decodeOriginalInteraction count)
    rw [interactionsEq]

/-! ## The introduced occurrence family is decoded from interactions -/

/-- Decode an interaction whose only tagged participant is a single hydrogen slot.  Original lifted
interactions contain only old atoms and decode to `none`; each selected hydrogen bond decodes to its
slot. -/
def introducedSlotOfEdge? (count : V → ℕ)
    (edge : List (ExpandedLabel count) × SemanticInteractionKind) :
    Option (HydrogenSlot count) :=
  match edge.1, edge.2 with
  | [Sum.inr h], _ => some h
  | [Sum.inl _, Sum.inr h], _ => some h
  | [Sum.inr h, Sum.inl _], _ => some h
  | _, _ => none

/-- The introduced slot family read from an expanded graph's interactions. -/
def introducedSlots (count : V → ℕ)
    (expanded : FiniteAtomInteractionHypergraph (ExpandedLabel count)) :
    List (HydrogenSlot count) :=
  expanded.interactions.filterMap (introducedSlotOfEdge? count)

@[simp] theorem introducedSlotOfEdge?_lift (count : V → ℕ)
    (edge : List V × SemanticInteractionKind) :
    introducedSlotOfEdge? count (liftInteraction count edge) = none := by
  obtain ⟨participants, kind⟩ := edge
  cases participants with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest => rfl

@[simp] theorem introducedSlotOfEdge?_hydrogenBond (count : V → ℕ)
    (h : HydrogenSlot count) :
    introducedSlotOfEdge? count (hydrogenBond count h) = some h :=
  rfl

theorem introducedSlots_liftInteractions (count : V → ℕ)
    (interactions : List (List V × SemanticInteractionKind)) :
    (interactions.map (liftInteraction count)).filterMap
        (introducedSlotOfEdge? count) = [] := by
  rw [List.filterMap_map]
  have functionEq : (introducedSlotOfEdge? count ∘ liftInteraction count) = (fun _ => none) := by
    funext edge
    exact introducedSlotOfEdge?_lift count edge
  rw [functionEq]
  exact filterMap_none_eq_nil _

theorem introducedSlots_hydrogenBonds (count : V → ℕ) :
    (hydrogenBonds count).filterMap (introducedSlotOfEdge? count) =
      hydrogenOccurrences count := by
  rw [hydrogenBonds, List.filterMap_map]
  have functionEq : (introducedSlotOfEdge? count ∘ hydrogenBond count) = some := by
    funext h
    exact introducedSlotOfEdge?_hydrogenBond count h
  rw [functionEq, List.filterMap_some]

/-- The introduced occurrence family of the expanded graph is exactly the total supplied slot
enumeration. -/
theorem introducedSlots_expand     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    introducedSlots count (expand graph count) = hydrogenOccurrences count := by
  change (graph.interactions.map (liftInteraction count) ++ hydrogenBonds count).filterMap
      (introducedSlotOfEdge? count) = hydrogenOccurrences count
  rw [List.filterMap_append, introducedSlots_liftInteractions,
    introducedSlots_hydrogenBonds, List.nil_append]

/-- Every supplied slot occurs in the decoded introduced family. -/
theorem introducedSlots_complete     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ)
    (h : HydrogenSlot count) :
    h ∈ introducedSlots count (expand graph count) := by
  rw [introducedSlots_expand]
  exact mem_hydrogenOccurrences count h

theorem introducedSlots_expand_nodup     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    (introducedSlots count (expand graph count)).Nodup := by
  rw [introducedSlots_expand]
  exact hydrogenOccurrences_nodup count

theorem introducedSlots_expand_length     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    (introducedSlots count (expand graph count)).length =
      (Finset.univ : Finset V).sum count := by
  rw [introducedSlots_expand, hydrogenOccurrences_length, hydrogenSlot_card]

/-- Total, duplicate-free materialization with exact identity: the introduced family is the entire
canonical slot enumeration. -/
theorem introducedSlots_expand_exact     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) :
    (introducedSlots count (expand graph count)).Nodup ∧
      (∀ h : HydrogenSlot count, h ∈ introducedSlots count (expand graph count)) ∧
      introducedSlots count (expand graph count) = hydrogenOccurrences count :=
  ⟨introducedSlots_expand_nodup graph count,
    fun h => introducedSlots_complete graph count h,
    introducedSlots_expand graph count⟩

/-- The introduced family is determined by the expanded interaction list alone. -/
theorem introducedSlots_determined_by_interactions (count : V → ℕ)
    {left right : FiniteAtomInteractionHypergraph (ExpandedLabel count)}
    (interactionsEq : left.interactions = right.interactions) :
    introducedSlots count left = introducedSlots count right := by
  change left.interactions.filterMap (introducedSlotOfEdge? count) =
    right.interactions.filterMap (introducedSlotOfEdge? count)
  rw [interactionsEq]

/-! ## Bridge from the independent site inventory to slot identities -/

/-- The implicit-protium count component of an independent electronic site source. -/
def siteImplicitCount     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph) : V → ℕ :=
  fun owner =>
    (siteSource.siteCounts.counts owner).count
      (SiteKind.electronic ElectronicSiteKind.implicitProtium)

/-- A supplied implicit-protium slot is exactly an individual site identity of kind
`implicitProtium` at that owner. -/
def materializedSiteIdentity     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource)) :
    IndependentSiteIdentity siteSource.siteCounts :=
  ⟨h.1, SiteKind.electronic ElectronicSiteKind.implicitProtium, h.2⟩

@[simp] theorem materializedSiteIdentity_owner     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource)) :
    (materializedSiteIdentity siteSource h).owner = h.1 :=
  rfl

@[simp] theorem materializedSiteIdentity_kind     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource)) :
    (materializedSiteIdentity siteSource h).kind =
      SiteKind.electronic ElectronicSiteKind.implicitProtium :=
  rfl

@[simp] theorem materializedSiteIdentity_slot_val     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource)) :
    (materializedSiteIdentity siteSource h).slot.val = h.2.val :=
  rfl

/-- The slot-to-site-identity map is injective: owner and slot index are both retained. -/
theorem materializedSiteIdentity_injective     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph) :
    Function.Injective (materializedSiteIdentity siteSource) := by
  intro h₁ h₂ equal
  rcases h₁ with ⟨owner₁, slot₁⟩
  rcases h₂ with ⟨owner₂, slot₂⟩
  cases equal
  rfl

/-- Every individual site identity of kind `implicitProtium` is a supplied slot. -/
theorem materializedSiteIdentity_surjective     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (identity : IndependentSiteIdentity siteSource.siteCounts)
    (kindEq : identity.kind =
      SiteKind.electronic ElectronicSiteKind.implicitProtium) :
    ∃ h : HydrogenSlot (siteImplicitCount siteSource),
      materializedSiteIdentity siteSource h = identity := by
  rcases identity with ⟨owner, kind, slot⟩
  cases kindEq
  exact ⟨⟨owner, slot⟩, rfl⟩

/-- A materialized slot is never an identity of another site kind. -/
theorem materializedSiteIdentity_ne_of_kind_ne     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource))
    {owner : V} {kind : SiteKind}
    {slot : Fin ((siteSource.siteCounts.counts owner).count kind)}
    (kindNe : kind ≠ SiteKind.electronic ElectronicSiteKind.implicitProtium) :
    materializedSiteIdentity siteSource h ≠
      (⟨owner, kind, slot⟩ : IndependentSiteIdentity siteSource.siteCounts) := by
  intro equal
  have kindEq := congrArg
    (fun identity : IndependentSiteIdentity siteSource.siteCounts => identity.kind) equal
  exact kindNe kindEq.symm

theorem materializedSiteIdentity_not_lonePair     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource))
    {owner : V}
    (slot : Fin ((siteSource.siteCounts.counts owner).count
      (SiteKind.electronic ElectronicSiteKind.lonePair))) :
    materializedSiteIdentity siteSource h ≠
      (⟨owner, SiteKind.electronic ElectronicSiteKind.lonePair, slot⟩ :
        IndependentSiteIdentity siteSource.siteCounts) :=
  materializedSiteIdentity_ne_of_kind_ne siteSource h (by decide)

theorem materializedSiteIdentity_not_vacancy     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource))
    {owner : V}
    (slot : Fin ((siteSource.siteCounts.counts owner).count
      (SiteKind.electronic ElectronicSiteKind.vacancy))) :
    materializedSiteIdentity siteSource h ≠
      (⟨owner, SiteKind.electronic ElectronicSiteKind.vacancy, slot⟩ :
        IndependentSiteIdentity siteSource.siteCounts) :=
  materializedSiteIdentity_ne_of_kind_ne siteSource h (by decide)

theorem materializedSiteIdentity_not_unpairedElectron     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource))
    {owner : V}
    (slot : Fin ((siteSource.siteCounts.counts owner).count
      (SiteKind.electronic ElectronicSiteKind.unpairedElectron))) :
    materializedSiteIdentity siteSource h ≠
      (⟨owner, SiteKind.electronic ElectronicSiteKind.unpairedElectron, slot⟩ :
        IndependentSiteIdentity siteSource.siteCounts) :=
  materializedSiteIdentity_ne_of_kind_ne siteSource h (by decide)

theorem materializedSiteIdentity_not_cipReference     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph)
    (h : HydrogenSlot (siteImplicitCount siteSource))
    {owner : V} (kind : CIPReferenceKind)
    (slot : Fin ((siteSource.siteCounts.counts owner).count
      (SiteKind.cipReference kind))) :
    materializedSiteIdentity siteSource h ≠
      (⟨owner, SiteKind.cipReference kind, slot⟩ :
        IndependentSiteIdentity siteSource.siteCounts) :=
  materializedSiteIdentity_ne_of_kind_ne siteSource h (by cases kind <;> decide)

/-- The number of materialized slots is exactly the total supplied implicit-protium count. -/
theorem materializedSlot_card_eq_implicitTotal     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph) :
    Fintype.card (HydrogenSlot (siteImplicitCount siteSource)) =
      (Finset.univ : Finset V).sum fun owner =>
        (siteSource.siteCounts.counts owner).implicitProtia := by
  rw [hydrogenSlot_card]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-! ## Non-protium payload preservation -/

/-- The supplied counts with the implicit-protium field blanked.  This is the explicit unaffected
electron/reference payload; it is not discarded. -/
def nonProtiumPayload (counts : SuppliedSiteCounts) : SuppliedSiteCounts :=
  { counts with implicitProtia := 0 }

@[simp] theorem nonProtiumPayload_lonePairs (counts : SuppliedSiteCounts) :
    (nonProtiumPayload counts).lonePairs = counts.lonePairs :=
  rfl

@[simp] theorem nonProtiumPayload_vacancies (counts : SuppliedSiteCounts) :
    (nonProtiumPayload counts).vacancies = counts.vacancies :=
  rfl

@[simp] theorem nonProtiumPayload_unpairedElectronPositions (counts : SuppliedSiteCounts) :
    (nonProtiumPayload counts).unpairedElectronPositions =
      counts.unpairedElectronPositions :=
  rfl

@[simp] theorem nonProtiumPayload_cipNotionalPhantoms (counts : SuppliedSiteCounts) :
    (nonProtiumPayload counts).cipNotionalPhantoms = counts.cipNotionalPhantoms :=
  rfl

@[simp] theorem nonProtiumPayload_cipVirtualDuplicates (counts : SuppliedSiteCounts) :
    (nonProtiumPayload counts).cipVirtualDuplicates = counts.cipVirtualDuplicates :=
  rfl

/-- No non-protium site kind is changed by blanking the protium field. -/
theorem nonProtiumPayload_count_of_kind_ne (counts : SuppliedSiteCounts) {kind : SiteKind}
    (kindNe : kind ≠ SiteKind.electronic ElectronicSiteKind.implicitProtium) :
    (nonProtiumPayload counts).count kind = counts.count kind := by
  cases kind with
  | electronic electronicKind =>
      cases electronicKind with
      | implicitProtium => exact False.elim (kindNe rfl)
      | lonePair => rfl
      | vacancy => rfl
      | unpairedElectron => rfl
  | cipReference cipKind =>
      cases cipKind <;> rfl

/-- Reattaching the supplied protium count reconstructs the original counts exactly. -/
theorem nonProtiumPayload_reconstruct (counts : SuppliedSiteCounts) :
    { nonProtiumPayload counts with implicitProtia := counts.implicitProtia } = counts := by
  cases counts
  rfl

/-- The non-protium payload of an independent source, still satisfying the unpaired-electron tie. -/
def nonProtiumSiteCounts     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph) :
    IndependentSiteCounts V where
  counts owner := nonProtiumPayload (siteSource.siteCounts.counts owner)

/-- The unaffected payload source.  Its unpaired tie is the original one, because that field is
preserved by `nonProtiumPayload`. -/
def nonProtiumSource     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph) :
    IndependentElectronicSiteSource graph where
  siteCounts := nonProtiumSiteCounts siteSource
  unpaired_tied owner := by
    change (nonProtiumPayload (siteSource.siteCounts.counts owner)).unpairedElectronPositions =
      (graph.atomData owner).unpairedElectrons
    rw [nonProtiumPayload_unpairedElectronPositions]
    exact siteSource.unpaired_tied owner

/-- Reattaching the supplied protium counts reconstructs the whole original count function. -/
theorem nonProtiumSiteCounts_reconstruct     {graph : FiniteAtomInteractionHypergraph V}
    (siteSource : IndependentElectronicSiteSource graph) :
    (⟨fun owner =>
        { (nonProtiumSiteCounts siteSource).counts owner with
            implicitProtia := (siteSource.siteCounts.counts owner).implicitProtia }⟩ :
      IndependentSiteCounts V) = siteSource.siteCounts := by
  cases siteSource with
  | mk siteCounts unpaired =>
      cases siteCounts with
      | mk counts =>
          exact congrArg IndependentSiteCounts.mk
            (funext fun owner => nonProtiumPayload_reconstruct (counts owner))

/-! ## A pair-bond `MoleculeGraph` view -/

/-- The bond order contributed by one interaction at one unordered pair.  Only two-participant
`.covalent` interactions contribute; every other interaction kind contributes zero here while
remaining present in the expanded hypergraph. -/
@[reducible] def edgeBondOrderAt    (edge : List V × SemanticInteractionKind) (u v : V) : ℕ :=
  match edge.1, edge.2 with
  | [a, b], SemanticInteractionKind.covalent order =>
      if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then order else 0
  | _, _ => 0

/-- The symmetric pair-bond adjacency obtained by summing pair-covalent contributions. -/
@[reducible] def pairBond    (graph : FiniteAtomInteractionHypergraph V) (u v : V) : ℕ :=
  (graph.interactions.map fun edge => edgeBondOrderAt edge u v).sum

theorem edgeBondOrderAt_comm    (edge : List V × SemanticInteractionKind) (u v : V) :
    edgeBondOrderAt edge u v = edgeBondOrderAt edge v u := by
  obtain ⟨participants, kind⟩ := edge
  cases participants with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil =>
              cases kind with
              | covalent order =>
                  have conditionEq :
                      ((first = u ∧ second = v) ∨ (first = v ∧ second = u)) ↔
                        ((first = v ∧ second = u) ∨ (first = u ∧ second = v)) :=
                    or_comm
                  by_cases holds : (first = u ∧ second = v) ∨ (first = v ∧ second = u)
                  · have holds' : (first = v ∧ second = u) ∨ (first = u ∧ second = v) :=
                      conditionEq.mp holds
                    simp only [edgeBondOrderAt]
                    rw [if_pos holds, if_pos holds']
                  · have holds' : ¬ ((first = v ∧ second = u) ∨ (first = u ∧ second = v)) :=
                      fun h' => holds (conditionEq.mpr h')
                    simp only [edgeBondOrderAt]
                    rw [if_neg holds, if_neg holds']
              | _ => rfl
          | cons third rest =>
              cases kind <;> rfl

theorem pairBond_comm    (graph : FiniteAtomInteractionHypergraph V) (u v : V) :
    pairBond graph u v = pairBond graph v u := by
  unfold pairBond
  exact congrArg List.sum
    (List.map_congr_left fun edge _ => edgeBondOrderAt_comm edge u v)

/-- A duplicate-free participant list cannot have the same pair twice with both positions equal. -/
theorem edgeBondOrderAt_self_of_nodup    (edge : List V × SemanticInteractionKind) (nodup : edge.1.Nodup) (u : V) :
    edgeBondOrderAt edge u u = 0 := by
  obtain ⟨participants, kind⟩ := edge
  cases participants with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil =>
              cases kind with
              | covalent order =>
                  have firstNeSecond : first ≠ second := by
                    intro equal
                    have nodupPair : ([first, second] : List V).Nodup := nodup
                    simp [equal] at nodupPair
                  have conditionFalse :
                      ¬ ((first = u ∧ second = u) ∨ (first = u ∧ second = u)) := by
                    rintro (⟨firstEq, secondEq⟩ | ⟨firstEq, secondEq⟩)
                    · exact firstNeSecond (firstEq.trans secondEq.symm)
                    · exact firstNeSecond (firstEq.trans secondEq.symm)
                  simp only [edgeBondOrderAt]
                  rw [if_neg conditionFalse]
              | _ => rfl
          | cons third rest => rfl

theorem sum_edgeBondOrderAt_self_eq_zero    (interactions : List (List V × SemanticInteractionKind))
    (nodup : ∀ edge ∈ interactions, edge.1.Nodup) (u : V) :
    (interactions.map fun edge => edgeBondOrderAt edge u u).sum = 0 := by
  induction interactions with
  | nil => rfl
  | cons edge rest ih =>
      have edgeZero : edgeBondOrderAt edge u u = 0 :=
        edgeBondOrderAt_self_of_nodup edge (nodup edge List.mem_cons_self) u
      have restZero : (rest.map fun e => edgeBondOrderAt e u u).sum = 0 :=
        ih fun e member => nodup e (List.mem_cons_of_mem edge member)
      simp [edgeZero, restZero]

theorem pairBond_self    (graph : FiniteAtomInteractionHypergraph V) (u : V) :
    pairBond graph u u = 0 :=
  sum_edgeBondOrderAt_self_eq_zero graph.interactions graph.participants_nodup u

/-- The symmetric molecule-graph view of a finite atom interaction hypergraph.  Atom data supply
atomic number, isotope mass, and formal charge; pair-covalent interactions supply bond orders. -/
@[reducible] def toMoleculeGraph     (graph : FiniteAtomInteractionHypergraph V) : MoleculeGraph V where
  atomZ := fun atom => (graph.atomData atom).element.atomicNumber
  atomMass := fun atom => (graph.atomData atom).isotopeMassNumber?.getD 0
  formalCharge := fun atom => (graph.atomData atom).formalCharge
  bond := pairBond graph
  bond_symm := pairBond_comm graph
  bond_self := pairBond_self graph

@[simp] theorem toMoleculeGraph_atomZ     (graph : FiniteAtomInteractionHypergraph V) (atom : V) :
    (toMoleculeGraph graph).atomZ atom = (graph.atomData atom).element.atomicNumber :=
  rfl

@[simp] theorem toMoleculeGraph_atomMass     (graph : FiniteAtomInteractionHypergraph V) (atom : V) :
    (toMoleculeGraph graph).atomMass atom =
      (graph.atomData atom).isotopeMassNumber?.getD 0 :=
  rfl

@[simp] theorem toMoleculeGraph_formalCharge     (graph : FiniteAtomInteractionHypergraph V) (atom : V) :
    (toMoleculeGraph graph).formalCharge atom = (graph.atomData atom).formalCharge :=
  rfl

@[simp] theorem toMoleculeGraph_bond     (graph : FiniteAtomInteractionHypergraph V) (u v : V) :
    (toMoleculeGraph graph).bond u v = pairBond graph u v :=
  rfl

/-! ### Bond contributions before and after expansion -/

@[simp] theorem edgeBondOrderAt_lift_inl_inl    (count : V → ℕ) (edge : List V × SemanticInteractionKind) (a b : V) :
    edgeBondOrderAt (liftInteraction count edge) (Sum.inl a) (Sum.inl b) =
      edgeBondOrderAt edge a b := by
  obtain ⟨participants, kind⟩ := edge
  cases participants with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          cases ys with
          | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
          | cons z zs => cases kind <;> rfl

@[simp] theorem edgeBondOrderAt_lift_inl_inr    (count : V → ℕ) (edge : List V × SemanticInteractionKind) (a : V)
    (h : HydrogenSlot count) :
    edgeBondOrderAt (liftInteraction count edge) (Sum.inl a) (Sum.inr h) = 0 := by
  obtain ⟨participants, kind⟩ := edge
  cases participants with
  | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
  | cons x xs =>
      cases xs with
      | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
      | cons y ys =>
          cases ys with
          | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
          | cons z zs => cases kind <;> simp [liftInteraction, edgeBondOrderAt]

@[simp] theorem edgeBondOrderAt_lift_inr_inl    (count : V → ℕ) (edge : List V × SemanticInteractionKind) (a : V)
    (h : HydrogenSlot count) :
    edgeBondOrderAt (liftInteraction count edge) (Sum.inr h) (Sum.inl a) = 0 := by
  obtain ⟨participants, kind⟩ := edge
  cases participants with
  | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
  | cons x xs =>
      cases xs with
      | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
      | cons y ys =>
          cases ys with
          | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
          | cons z zs => cases kind <;> simp [liftInteraction, edgeBondOrderAt]

@[simp] theorem edgeBondOrderAt_lift_inr_inr    (count : V → ℕ) (edge : List V × SemanticInteractionKind)
    (h₁ h₂ : HydrogenSlot count) :
    edgeBondOrderAt (liftInteraction count edge) (Sum.inr h₁) (Sum.inr h₂) = 0 := by
  obtain ⟨participants, kind⟩ := edge
  cases participants with
  | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
  | cons x xs =>
      cases xs with
      | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
      | cons y ys =>
          cases ys with
          | nil => cases kind <;> simp [liftInteraction, edgeBondOrderAt]
          | cons z zs => cases kind <;> simp [liftInteraction, edgeBondOrderAt]

@[simp] theorem edgeBondOrderAt_hydrogenBond_inl_inl    (count : V → ℕ) (h : HydrogenSlot count) (a b : V) :
    edgeBondOrderAt (hydrogenBond count h) (Sum.inl a) (Sum.inl b) = 0 := by
  simp [hydrogenBond, edgeBondOrderAt]

@[simp] theorem edgeBondOrderAt_hydrogenBond_same    (count : V → ℕ) (h : HydrogenSlot count) :
    edgeBondOrderAt (hydrogenBond count h) (Sum.inl h.1) (Sum.inr h) = 1 := by
  simp [hydrogenBond, edgeBondOrderAt]

theorem sum_eq_zero_of_forall_eq_zero {items : List ℕ}
    (zero : ∀ item ∈ items, item = 0) : items.sum = 0 := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.sum_cons, zero head List.mem_cons_self,
        ih (fun item member => zero item (List.mem_cons_of_mem head member)), Nat.add_zero]

/-- Expanding preserves the pair bond between two old atoms: lifted original interactions contribute
their original bond order and hydrogen interactions contribute nothing at old–old pairs. -/
theorem pairBond_expand_inl_inl     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ) (a b : V) :
    pairBond (expand graph count) (Sum.inl a) (Sum.inl b) = pairBond graph a b := by
  unfold pairBond
  rw [expand_interactions, List.map_append, List.sum_append]
  have lifted :
      ((graph.interactions.map (liftInteraction count)).map
          (fun edge => edgeBondOrderAt edge (Sum.inl a) (Sum.inl b))).sum =
        (graph.interactions.map (fun edge => edgeBondOrderAt edge a b)).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun edge _ =>
      edgeBondOrderAt_lift_inl_inl count edge a b
  have hydro :
      ((hydrogenBonds count).map
          (fun edge => edgeBondOrderAt edge (Sum.inl a) (Sum.inl b))).sum = 0 := by
    apply sum_eq_zero_of_forall_eq_zero
    intro item member
    rcases List.mem_map.mp member with ⟨edge, edgeMember, rfl⟩
    rcases List.mem_map.mp edgeMember with ⟨h, _, rfl⟩
    exact edgeBondOrderAt_hydrogenBond_inl_inl count h a b
  rw [lifted, hydro, Nat.add_zero]

/-- The selected covalent pair interaction makes the materialized hydrogen a positive-bond neighbor
of its owner. -/
theorem pairBond_expand_selected_pos     (graph : FiniteAtomInteractionHypergraph V) (count : V → ℕ)
    (h : HydrogenSlot count) :
    0 < pairBond (expand graph count) (Sum.inl h.1) (Sum.inr h) := by
  unfold pairBond
  rw [expand_interactions, Nat.sum_pos_iff_exists_pos]
  refine ⟨edgeBondOrderAt (hydrogenBond count h) (Sum.inl h.1) (Sum.inr h), ?_, ?_⟩
  · rw [List.mem_map]
    exact ⟨hydrogenBond count h,
      List.mem_append_right _ (List.mem_map_of_mem (mem_hydrogenOccurrences count h)), rfl⟩
  · rw [edgeBondOrderAt_hydrogenBond_same]
    decide

/-! ## The decisive `CHBrClF` fixture

The heavy graph has four atoms: carbon `0`, bromine `1`, chlorine `2`, fluorine `3`, with three
carbon–halogen single bonds.  The supplied inventory puts one implicit protium on carbon and three
lone pairs on each halogen.  No other count is nonzero.
-/

def fixtureCarbon : SemanticAtom :=
  { element :=
      { atomicNumber := 6
        positive := by decide
        atMost118 := by decide } }

def fixtureBromine : SemanticAtom :=
  { element :=
      { atomicNumber := 35
        positive := by decide
        atMost118 := by decide } }

def fixtureChlorine : SemanticAtom :=
  { element :=
      { atomicNumber := 17
        positive := by decide
        atMost118 := by decide } }

def fixtureFluorine : SemanticAtom :=
  { element :=
      { atomicNumber := 9
        positive := by decide
        atMost118 := by decide } }

@[reducible] def fixtureAtomData (i : Fin 4) : SemanticAtom :=
  match i.val with
  | 0 => fixtureCarbon
  | 1 => fixtureBromine
  | 2 => fixtureChlorine
  | _ => fixtureFluorine

def fixtureInteractions : List (List (Fin 4) × SemanticInteractionKind) :=
  [([(0 : Fin 4), 1], SemanticInteractionKind.covalent 1),
    ([(0 : Fin 4), 2], SemanticInteractionKind.covalent 1),
    ([(0 : Fin 4), 3], SemanticInteractionKind.covalent 1)]

@[reducible] def fixtureGraph : FiniteAtomInteractionHypergraph (Fin 4) where
  atomData := fixtureAtomData
  interactions := fixtureInteractions
  arity_ge_two := by
    intro edge member
    simp only [fixtureInteractions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  participants_nodup := by
    intro edge member
    simp only [fixtureInteractions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide

@[simp] theorem fixtureGraph_atomData :
    fixtureGraph.atomData = fixtureAtomData :=
  rfl

@[simp] theorem fixtureGraph_interactions :
    fixtureGraph.interactions = fixtureInteractions :=
  rfl

def fixtureZeroCounts : SuppliedSiteCounts where
  implicitProtia := 0
  lonePairs := 0
  vacancies := 0
  unpairedElectronPositions := 0
  cipNotionalPhantoms := 0
  cipVirtualDuplicates := 0

def fixtureCarbonCounts : SuppliedSiteCounts :=
  { fixtureZeroCounts with implicitProtia := 1 }

def fixtureHalogenCounts : SuppliedSiteCounts :=
  { fixtureZeroCounts with lonePairs := 3 }

def fixtureCountsAt (i : Fin 4) : SuppliedSiteCounts :=
  if i = 0 then fixtureCarbonCounts else fixtureHalogenCounts

@[simp] theorem fixtureCountsAt_zero : fixtureCountsAt 0 = fixtureCarbonCounts := by
  decide

@[simp] theorem fixtureCountsAt_one : fixtureCountsAt 1 = fixtureHalogenCounts := by
  decide

@[simp] theorem fixtureCountsAt_two : fixtureCountsAt 2 = fixtureHalogenCounts := by
  decide

@[simp] theorem fixtureCountsAt_three : fixtureCountsAt 3 = fixtureHalogenCounts := by
  decide

def fixtureSiteSource : IndependentElectronicSiteSource fixtureGraph where
  siteCounts := { counts := fixtureCountsAt }
  unpaired_tied := by
    intro owner
    fin_cases owner <;> rfl

def fixtureImplicitCount : Fin 4 → ℕ :=
  siteImplicitCount fixtureSiteSource

theorem fixtureImplicitCount_zero : fixtureImplicitCount 0 = 1 := by
  change (fixtureCountsAt 0).count
      (SiteKind.electronic ElectronicSiteKind.implicitProtium) = 1
  rw [fixtureCountsAt_zero]
  rfl

theorem fixtureImplicitCount_one : fixtureImplicitCount 1 = 0 := by
  change (fixtureCountsAt 1).count
      (SiteKind.electronic ElectronicSiteKind.implicitProtium) = 0
  rw [fixtureCountsAt_one]
  rfl

theorem fixtureImplicitCount_two : fixtureImplicitCount 2 = 0 := by
  change (fixtureCountsAt 2).count
      (SiteKind.electronic ElectronicSiteKind.implicitProtium) = 0
  rw [fixtureCountsAt_two]
  rfl

theorem fixtureImplicitCount_three : fixtureImplicitCount 3 = 0 := by
  change (fixtureCountsAt 3).count
      (SiteKind.electronic ElectronicSiteKind.implicitProtium) = 0
  rw [fixtureCountsAt_three]
  rfl

def fixtureHydrogen : HydrogenSlot fixtureImplicitCount :=
  ⟨0, ⟨0, by rw [fixtureImplicitCount_zero]; decide⟩⟩

@[simp] theorem fixtureHydrogen_owner : fixtureHydrogen.1 = 0 :=
  rfl

@[simp] theorem fixtureHydrogen_slot_val : fixtureHydrogen.2.val = 0 :=
  rfl

theorem fixtureHydrogenSlot_card :
    Fintype.card (HydrogenSlot fixtureImplicitCount) = 1 := by
  rw [hydrogenSlot_card, Fin.sum_univ_four]
  rw [fixtureImplicitCount_zero, fixtureImplicitCount_one,
    fixtureImplicitCount_two, fixtureImplicitCount_three]

theorem fixtureHydrogen_unique (h : HydrogenSlot fixtureImplicitCount) :
    h = fixtureHydrogen := by
  rcases Fintype.card_eq_one_iff.mp fixtureHydrogenSlot_card with ⟨unique, hunique⟩
  exact (hunique h).trans (hunique fixtureHydrogen).symm

theorem fixture_hydrogenOccurrences :
    hydrogenOccurrences fixtureImplicitCount = [fixtureHydrogen] := by
  unfold hydrogenOccurrences
  have univEq : (Finset.univ : Finset (HydrogenSlot fixtureImplicitCount)) =
      {fixtureHydrogen} := by
    ext h
    simp [fixtureHydrogen_unique h]
  rw [univEq]
  simp

theorem fixture_hydrogenBonds :
    hydrogenBonds fixtureImplicitCount =
      [hydrogenBond fixtureImplicitCount fixtureHydrogen] := by
  rw [hydrogenBonds, fixture_hydrogenOccurrences]
  rfl

/-! ### Heavy graph and its degree-three detector behaviour -/

@[reducible] def fixtureHeavyGraph : MoleculeGraph (Fin 4) :=
  toMoleculeGraph fixtureGraph

@[simp] theorem fixtureHeavyGraph_atomZ (i : Fin 4) :
    fixtureHeavyGraph.atomZ i = (fixtureAtomData i).element.atomicNumber :=
  rfl

theorem fixtureHeavyGraph_neighborFinset_zero :
    fixtureHeavyGraph.neighborFinset 0 = ({1, 2, 3} : Finset (Fin 4)) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide

theorem fixtureHeavyGraph_neighborFinset_one :
    fixtureHeavyGraph.neighborFinset 1 = ({0} : Finset (Fin 4)) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide

theorem fixtureHeavyGraph_neighborFinset_two :
    fixtureHeavyGraph.neighborFinset 2 = ({0} : Finset (Fin 4)) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide

theorem fixtureHeavyGraph_neighborFinset_three :
    fixtureHeavyGraph.neighborFinset 3 = ({0} : Finset (Fin 4)) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide

theorem fixtureHeavyGraph_center_degree_three :
    (fixtureHeavyGraph.neighborFinset 0).card = 3 := by
  rw [fixtureHeavyGraph_neighborFinset_zero]
  decide

theorem fixtureHeavyGraph_center_not_tetrahedral :
    ¬ fixtureHeavyGraph.IsTetrahedralCenter 0 := by
  rw [MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card,
    fixtureHeavyGraph_center_degree_three]
  decide

theorem fixtureHeavyGraph_no_detected_center :
    fixtureHeavyGraph.tetrahedralCenterSet = (∅ : Finset (Fin 4)) := by
  ext c
  fin_cases c <;>
    simp [MoleculeGraph.mem_tetrahedralCenterSet,
      MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card,
      fixtureHeavyGraph_neighborFinset_zero, fixtureHeavyGraph_neighborFinset_one,
      fixtureHeavyGraph_neighborFinset_two, fixtureHeavyGraph_neighborFinset_three]

theorem fixtureHeavyGraph_center_omitted :
    0 ∉ fixtureHeavyGraph.tetrahedralCenterSet := by
  rw [fixtureHeavyGraph_no_detected_center]
  simp

theorem fixtureHeavyGraph_direct_priority_labels :
    (([(1 : Fin 4), 2, 3]).map (MoleculeGraph.rawCIPAtomLabel fixtureHeavyGraph)) =
      [toLex ((35 : ℕ), 0), toLex ((17 : ℕ), 0), toLex ((9 : ℕ), 0)] := by
  decide

/-! ### The expanded five-atom graph and its detector behaviour -/

@[reducible] noncomputable def fixtureExpandedGraph :
    FiniteAtomInteractionHypergraph (ExpandedLabel fixtureImplicitCount) :=
  expand fixtureGraph fixtureImplicitCount

@[reducible] noncomputable def fixtureExpandedMoleculeGraph :
    MoleculeGraph (ExpandedLabel fixtureImplicitCount) :=
  toMoleculeGraph fixtureExpandedGraph

@[simp] theorem fixtureExpandedGraph_interactions :
    fixtureExpandedGraph.interactions =
      fixtureGraph.interactions.map (liftInteraction fixtureImplicitCount) ++
        hydrogenBonds fixtureImplicitCount :=
  rfl

theorem fixtureExpanded_five_atoms :
    Fintype.card (ExpandedLabel fixtureImplicitCount) = 5 := by
  rw [Fintype.card_sum, Fintype.card_fin, fixtureHydrogenSlot_card]

def fixtureExpandedAtoms : List (ExpandedLabel fixtureImplicitCount) :=
  [Sum.inl (0 : Fin 4), Sum.inl (1 : Fin 4), Sum.inl (2 : Fin 4), Sum.inl (3 : Fin 4),
    Sum.inr fixtureHydrogen]

theorem fixtureExpandedAtoms_nodup : fixtureExpandedAtoms.Nodup := by
  decide

theorem fixtureExpandedAtoms_length : fixtureExpandedAtoms.length = 5 :=
  rfl

theorem fixtureExpandedAtoms_complete (w : ExpandedLabel fixtureImplicitCount) :
    w ∈ fixtureExpandedAtoms := by
  cases w with
  | inl v =>
      fin_cases v <;> simp [fixtureExpandedAtoms]
  | inr h =>
      have hEq : h = fixtureHydrogen := fixtureHydrogen_unique h
      subst h
      simp [fixtureExpandedAtoms]

theorem fixture_lift_mem (edge : List (Fin 4) × SemanticInteractionKind)
    (member : edge ∈ fixtureGraph.interactions) :
    liftInteraction fixtureImplicitCount edge ∈ fixtureExpandedGraph.interactions := by
  rw [fixtureExpandedGraph_interactions]
  exact List.mem_append_left _ (List.mem_map_of_mem member)

theorem fixture_original_bond_mem :
    (([(Sum.inl (0 : Fin 4) : ExpandedLabel fixtureImplicitCount),
        Sum.inl (1 : Fin 4)],
        SemanticInteractionKind.covalent 1) : List (ExpandedLabel fixtureImplicitCount) ×
          SemanticInteractionKind) ∈ fixtureExpandedGraph.interactions := by
  have member : (([(0 : Fin 4), 1], SemanticInteractionKind.covalent 1) :
      List (Fin 4) × SemanticInteractionKind) ∈ fixtureGraph.interactions := by
    rw [fixtureGraph_interactions]
    simp [fixtureInteractions]
  have lifted := fixture_lift_mem _ member
  simpa [liftInteraction] using lifted

theorem fixture_hydrogen_bond_mem :
    hydrogenBond fixtureImplicitCount fixtureHydrogen ∈ fixtureExpandedGraph.interactions := by
  rw [fixtureExpandedGraph_interactions]
  exact List.mem_append_right _
    (List.mem_map_of_mem (mem_hydrogenOccurrences fixtureImplicitCount fixtureHydrogen))

theorem fixture_introducedSlots :
    introducedSlots fixtureImplicitCount fixtureExpandedGraph = [fixtureHydrogen] := by
  show introducedSlots fixtureImplicitCount (expand fixtureGraph fixtureImplicitCount) =
    [fixtureHydrogen]
  rw [introducedSlots_expand, fixture_hydrogenOccurrences]

@[simp] theorem fixtureExpanded_atomZ_hydrogen
    (h : HydrogenSlot fixtureImplicitCount) :
    fixtureExpandedMoleculeGraph.atomZ (Sum.inr h) = 1 :=
  rfl

@[simp] theorem fixtureExpanded_atomMass_hydrogen
    (h : HydrogenSlot fixtureImplicitCount) :
    fixtureExpandedMoleculeGraph.atomMass (Sum.inr h) = 0 :=
  rfl

@[simp] theorem fixtureExpanded_formalCharge_hydrogen
    (h : HydrogenSlot fixtureImplicitCount) :
    fixtureExpandedMoleculeGraph.formalCharge (Sum.inr h) = 0 :=
  rfl

@[simp] theorem fixtureExpanded_atomZ_old (v : Fin 4) :
    fixtureExpandedMoleculeGraph.atomZ (Sum.inl v) =
      (fixtureAtomData v).element.atomicNumber :=
  rfl

@[simp] theorem fixtureExpanded_atomMass_old (v : Fin 4) :
    fixtureExpandedMoleculeGraph.atomMass (Sum.inl v) = 0 := by
  fin_cases v <;> rfl

theorem fixtureExpanded_neighborFinset_center :
    fixtureExpandedMoleculeGraph.neighborFinset (Sum.inl (0 : Fin 4)) =
      ({Sum.inl (1 : Fin 4), Sum.inl (2 : Fin 4), Sum.inl (3 : Fin 4),
        Sum.inr fixtureHydrogen} : Finset (ExpandedLabel fixtureImplicitCount)) := by
  ext w
  rw [MoleculeGraph.mem_neighborFinset]
  cases w with
  | inl v =>
      have adjIff :
          fixtureExpandedMoleculeGraph.Adj (Sum.inl (0 : Fin 4)) (Sum.inl v) ↔
            fixtureHeavyGraph.Adj (0 : Fin 4) v := by
        show 0 < pairBond fixtureExpandedGraph (Sum.inl (0 : Fin 4)) (Sum.inl v) ↔
          0 < pairBond fixtureGraph (0 : Fin 4) v
        rw [fixtureExpandedGraph, pairBond_expand_inl_inl]
      rw [adjIff, ← (fixtureHeavyGraph.mem_neighborFinset (v := (0 : Fin 4)) (u := v)),
        fixtureHeavyGraph_neighborFinset_zero]
      fin_cases v <;> simp
  | inr h =>
      have hEq : h = fixtureHydrogen := fixtureHydrogen_unique h
      subst h
      have positive :
          fixtureExpandedMoleculeGraph.Adj (Sum.inl (0 : Fin 4)) (Sum.inr fixtureHydrogen) := by
        show 0 < pairBond fixtureExpandedGraph (Sum.inl (0 : Fin 4)) (Sum.inr fixtureHydrogen)
        exact pairBond_expand_selected_pos fixtureGraph fixtureImplicitCount fixtureHydrogen
      simp [positive]

theorem fixtureExpanded_center_tetrahedral :
    fixtureExpandedMoleculeGraph.IsTetrahedralCenter (Sum.inl (0 : Fin 4)) := by
  rw [MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card,
    fixtureExpanded_neighborFinset_center]
  decide

theorem fixtureExpanded_center_mem_detected :
    Sum.inl (0 : Fin 4) ∈ fixtureExpandedMoleculeGraph.tetrahedralCenterSet :=
  (MoleculeGraph.mem_tetrahedralCenterSet _ _).2 fixtureExpanded_center_tetrahedral

def fixtureCenter : fixtureExpandedMoleculeGraph.TetrahedralCenter :=
  ⟨Sum.inl (0 : Fin 4), fixtureExpanded_center_mem_detected⟩

noncomputable def fixtureOneCenterMolecule :
    OneCenterMolecule (ExpandedLabel fixtureImplicitCount) :=
  MoleculeGraph.detectedOneCenterMolecule fixtureExpandedMoleculeGraph fixtureCenter

theorem fixture_restore_expanded :
    restore fixtureImplicitCount fixtureExpandedGraph = fixtureGraph := by
  show restore fixtureImplicitCount (expand fixtureGraph fixtureImplicitCount) = fixtureGraph
  exact restore_expand fixtureGraph fixtureImplicitCount

/-! ### Four distinct direct priorities and CIP injectivity -/

def fixtureCarbonNeighbors : List (ExpandedLabel fixtureImplicitCount) :=
  [Sum.inl (1 : Fin 4), Sum.inl (2 : Fin 4), Sum.inl (3 : Fin 4), Sum.inr fixtureHydrogen]

theorem fixtureCarbonNeighbors_mem_iff (w : ExpandedLabel fixtureImplicitCount) :
    w ∈ fixtureCarbonNeighbors ↔
      w ∈ fixtureExpandedMoleculeGraph.neighborFinset (Sum.inl (0 : Fin 4)) := by
  rw [fixtureExpanded_neighborFinset_center]
  cases w with
  | inl v => fin_cases v <;> simp [fixtureCarbonNeighbors]
  | inr h =>
      have hEq : h = fixtureHydrogen := fixtureHydrogen_unique h
      subst h
      simp [fixtureCarbonNeighbors]

theorem expanded_direct_priority_labels :
    (fixtureCarbonNeighbors.map
        (MoleculeGraph.rawCIPAtomLabel fixtureExpandedMoleculeGraph)) =
      [toLex ((35 : ℕ), 0), toLex ((17 : ℕ), 0), toLex ((9 : ℕ), 0),
        toLex ((1 : ℕ), 0)] := by
  decide

theorem expanded_direct_priority_labels_heavy_prefix :
    ((fixtureCarbonNeighbors.take 3).map
        (MoleculeGraph.rawCIPAtomLabel fixtureExpandedMoleculeGraph)) =
      [toLex ((35 : ℕ), 0), toLex ((17 : ℕ), 0), toLex ((9 : ℕ), 0)] := by
  decide

theorem expanded_fourth_priority_is_hydrogen :
    MoleculeGraph.rawCIPAtomLabel fixtureExpandedMoleculeGraph (Sum.inr fixtureHydrogen) =
      toLex ((1 : ℕ), 0) := by
  decide

theorem expanded_direct_priorities_nodup :
    (fixtureCarbonNeighbors.map
        (MoleculeGraph.rawCIPAtomLabel fixtureExpandedMoleculeGraph)).Nodup := by
  rw [expanded_direct_priority_labels]
  decide

theorem expanded_hydrogen_priority_distinct :
    MoleculeGraph.rawCIPAtomLabel fixtureExpandedMoleculeGraph (Sum.inr fixtureHydrogen) ∉
      ([toLex ((35 : ℕ), 0), toLex ((17 : ℕ), 0), toLex ((9 : ℕ), 0)] :
        List MoleculeGraph.AtomLabel) := by
  decide

theorem fixture_cipKeyFrom_heads :
    (fixtureCarbonNeighbors.map fun w =>
        (MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph
          (Sum.inl (0 : Fin 4)) w).head?) =
      (fixtureCarbonNeighbors.map fun w =>
        some (MoleculeGraph.rawCIPAtomLabel fixtureExpandedMoleculeGraph w)) := by
  apply List.map_congr_left
  intro w _
  exact MoleculeGraph.cipKeyFrom_head? fixtureExpandedMoleculeGraph (Sum.inl (0 : Fin 4)) w

theorem fixture_cipKeyFrom_heads_nodup :
    (fixtureCarbonNeighbors.map fun w =>
        (MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph
          (Sum.inl (0 : Fin 4)) w).head?).Nodup := by
  rw [fixture_cipKeyFrom_heads]
  exact expanded_direct_priorities_nodup.map
    (f := some) (fun _ _ equal => Option.some.inj equal)

theorem expanded_cipKeys_nodup :
    (fixtureCarbonNeighbors.map fun w =>
        MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph
          (Sum.inl (0 : Fin 4)) w).Nodup := by
  apply List.Nodup.of_map List.head?
  simpa only [List.map_map, Function.comp_def] using fixture_cipKeyFrom_heads_nodup

theorem fixture_cipKeyFrom_inj_on_neighbors :
    ∀ ⦃x⦄, x ∈ fixtureCarbonNeighbors →
      ∀ ⦃y⦄, y ∈ fixtureCarbonNeighbors →
        MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph (Sum.inl (0 : Fin 4)) x =
          MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph (Sum.inl (0 : Fin 4)) y →
          x = y :=
  List.inj_on_of_nodup_map
    (f := fun w => MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph (Sum.inl (0 : Fin 4)) w)
    (l := fixtureCarbonNeighbors) expanded_cipKeys_nodup

/-- The detected one-center molecule at the expanded carbon has injective CIP keys: the original
three halogens and the materialized hydrogen give four distinct direct priorities. -/
theorem fixtureOneCenter_stereogenicByCIP :
    OneCenterMolecule.StereogenicByCIP fixtureOneCenterMolecule := by
  intro i j keyEq
  apply fixtureOneCenterMolecule.ligandAtom_injective
  have adjI : fixtureExpandedMoleculeGraph.Adj (Sum.inl (0 : Fin 4))
      (fixtureOneCenterMolecule.ligandAtom i) :=
    fixtureOneCenterMolecule.ligandAtom_adj i
  have adjJ : fixtureExpandedMoleculeGraph.Adj (Sum.inl (0 : Fin 4))
      (fixtureOneCenterMolecule.ligandAtom j) :=
    fixtureOneCenterMolecule.ligandAtom_adj j
  have memberI : fixtureOneCenterMolecule.ligandAtom i ∈ fixtureCarbonNeighbors :=
    (fixtureCarbonNeighbors_mem_iff _).2
      ((MoleculeGraph.mem_neighborFinset fixtureExpandedMoleculeGraph
        (Sum.inl (0 : Fin 4)) (fixtureOneCenterMolecule.ligandAtom i)).2 adjI)
  have memberJ : fixtureOneCenterMolecule.ligandAtom j ∈ fixtureCarbonNeighbors :=
    (fixtureCarbonNeighbors_mem_iff _).2
      ((MoleculeGraph.mem_neighborFinset fixtureExpandedMoleculeGraph
        (Sum.inl (0 : Fin 4)) (fixtureOneCenterMolecule.ligandAtom j)).2 adjJ)
  have keyEqOnNeighbors :
      MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph (Sum.inl (0 : Fin 4))
          (fixtureOneCenterMolecule.ligandAtom i) =
        MoleculeGraph.cipKeyFrom fixtureExpandedMoleculeGraph (Sum.inl (0 : Fin 4))
          (fixtureOneCenterMolecule.ligandAtom j) := by
    simpa [OneCenterMolecule.cipKey] using keyEq
  exact fixture_cipKeyFrom_inj_on_neighbors memberI memberJ keyEqOnNeighbors

end OrganicStereoInventoryImplicitHMaterialization
end OneCenter
end TetraStereo
