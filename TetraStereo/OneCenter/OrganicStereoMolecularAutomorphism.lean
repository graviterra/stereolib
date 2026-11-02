import TetraStereo.OneCenter.AuthoritativeChemicalInput
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace SemanticMolecule

/-!
# Constitution-preserving relabellings of a full semantic molecule

This module supplies the arbitrary, source-bound relabelling infrastructure for the complete
`SemanticMolecule` representation of `TetraStereo.OneCenter.AuthoritativeChemicalInput`.  It does
not restrict the molecule to a localized or pair-bond-only fragment: atoms, isotope labels,
charge, radical count, aromatic input flags, interaction kinds (including multicenter,
delocalized, ionic, metallic, hydrogen-bond and `other authorityCode` interactions) and arbitrary
finite participant lists are all in scope.

The data of a relabelling are

* an atom permutation `Fin molecule.atomCount ≃ Fin molecule.atomCount`, and
* an interaction-occurrence permutation
  `Fin molecule.interactions.length ≃ Fin molecule.interactions.length`.

The second permutation is deliberately a permutation of *occurrences*, identified by their
position in `molecule.interactions`.  Equal `SemanticInteraction` values at different positions
are distinct chemical occurrences; duplicates are allowed, and no `Nodup` hypothesis on the
interaction list is imposed.  Consequently the construction respects source interaction identity
rather than quotienting by interaction value.

An atom label is preserved when the atom stored at the image index is exactly the atom stored at
the source index.  Interaction kind is preserved as an equality.  Participant incidences are
compared up to `List.Perm`: the order of a participant list is an implementation detail of a
serialization, not a chemical orientation.  The original source lists are never reordered here;
`List.Perm` only appears in the preservation criterion.

The resulting objects form an honest subgroup of the product permutation group, so identity,
inverse and composition are available and their preservation properties are proved from the
subgroup closure conditions.

Two boundaries are explicit and are not hidden:

* graph/constitution automorphisms are *not* rigid motions and are *not* chirality verdicts.
  The conformation action below only reassigns coordinates to atom labels; it never moves a point
  in space.
* donor/acceptor/haptic and other roles are not fields of `SemanticAtom` or
  `SemanticInteraction`.  Role-enriched automorphisms are a separate, explicitly compatible
  subgroup (`RoleEnrichedAut`); the raw automorphism group makes no role claim.
-/

/-! ## The bounded action of an atom permutation on raw participant indices -/

/-- Apply an atom-index permutation to a raw participant index.

Participant lists are stored as `List ℕ`.  On an index inside the finite atom carrier this is the
exact bounded action of the permutation; on an index outside the carrier (which cannot occur in a
structurally well-formed molecule) the index is left fixed.  The definition is uniform in
`molecule.atomCount`; no finite atom-count cap is used anywhere in this module. -/
def applyAtomIndex (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) (index : ℕ) : ℕ :=
  if bounded : index < molecule.atomCount then (atomPerm ⟨index, bounded⟩).val else index

@[simp] theorem applyAtomIndex_of_lt (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) {index : ℕ}
    (bounded : index < molecule.atomCount) :
    applyAtomIndex molecule atomPerm index = (atomPerm ⟨index, bounded⟩).val := by
  simp [applyAtomIndex, bounded]

@[simp] theorem applyAtomIndex_of_not_lt (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) {index : ℕ}
    (unbounded : ¬ index < molecule.atomCount) :
    applyAtomIndex molecule atomPerm index = index := by
  simp [applyAtomIndex, unbounded]

/-- The exact bounded action stays inside the finite atom carrier. -/
theorem applyAtomIndex_lt (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) {index : ℕ}
    (bounded : index < molecule.atomCount) :
    applyAtomIndex molecule atomPerm index < molecule.atomCount := by
  rw [applyAtomIndex_of_lt molecule atomPerm bounded]
  exact (atomPerm ⟨index, bounded⟩).isLt

/-- An index is inside the atom carrier exactly when its image under the bounded action is. -/
theorem applyAtomIndex_lt_iff (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) (index : ℕ) :
    applyAtomIndex molecule atomPerm index < molecule.atomCount ↔
      index < molecule.atomCount := by
  constructor
  · intro imageBounded
    by_contra unbounded
    rw [applyAtomIndex_of_not_lt molecule atomPerm unbounded] at imageBounded
    exact unbounded imageBounded
  · exact applyAtomIndex_lt molecule atomPerm

/-- The bounded action is injective on all natural-number indices.  Unbounded indices are fixed,
and bounded indices are permuted by a bijection. -/
theorem applyAtomIndex_injective (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) :
    Function.Injective (applyAtomIndex molecule atomPerm) := by
  intro left right equal
  by_cases leftBounded : left < molecule.atomCount
  · have rightBounded : right < molecule.atomCount := by
      by_contra rightUnbounded
      have rightFixed : applyAtomIndex molecule atomPerm right = right :=
        applyAtomIndex_of_not_lt molecule atomPerm rightUnbounded
      have leftImage : applyAtomIndex molecule atomPerm left =
          (atomPerm ⟨left, leftBounded⟩).val :=
        applyAtomIndex_of_lt molecule atomPerm leftBounded
      rw [leftImage, rightFixed] at equal
      have imageLt := (atomPerm ⟨left, leftBounded⟩).isLt
      omega
    have leftImage : applyAtomIndex molecule atomPerm left =
        (atomPerm ⟨left, leftBounded⟩).val :=
      applyAtomIndex_of_lt molecule atomPerm leftBounded
    have rightImage : applyAtomIndex molecule atomPerm right =
        (atomPerm ⟨right, rightBounded⟩).val :=
      applyAtomIndex_of_lt molecule atomPerm rightBounded
    have finEqual : atomPerm ⟨left, leftBounded⟩ = atomPerm ⟨right, rightBounded⟩ := by
      apply Fin.ext
      rw [leftImage, rightImage] at equal
      exact equal
    have argumentEqual := atomPerm.injective finEqual
    exact congrArg Fin.val argumentEqual
  · have leftFixed : applyAtomIndex molecule atomPerm left = left :=
      applyAtomIndex_of_not_lt molecule atomPerm leftBounded
    have rightUnbounded : ¬ right < molecule.atomCount := by
      intro rightBounded
      have rightImage : applyAtomIndex molecule atomPerm right =
          (atomPerm ⟨right, rightBounded⟩).val :=
        applyAtomIndex_of_lt molecule atomPerm rightBounded
      rw [leftFixed, rightImage] at equal
      have imageLt := (atomPerm ⟨right, rightBounded⟩).isLt
      omega
    have rightFixed : applyAtomIndex molecule atomPerm right = right :=
      applyAtomIndex_of_not_lt molecule atomPerm rightUnbounded
    rw [leftFixed, rightFixed] at equal
    exact equal

/-! ### The bounded action is a monoid action on raw indices -/

@[simp] theorem applyAtomIndex_one (molecule : SemanticMolecule) (index : ℕ) :
    applyAtomIndex molecule (1 : Equiv.Perm (Fin molecule.atomCount)) index = index := by
  by_cases bounded : index < molecule.atomCount
  · rw [applyAtomIndex_of_lt molecule 1 bounded]
    simp
  · rw [applyAtomIndex_of_not_lt molecule 1 bounded]

/-- Composition of atom permutations acts by composing the bounded actions. -/
theorem applyAtomIndex_mul (molecule : SemanticMolecule)
    (σ τ : Equiv.Perm (Fin molecule.atomCount)) (index : ℕ) :
    applyAtomIndex molecule (σ * τ) index =
      applyAtomIndex molecule σ (applyAtomIndex molecule τ index) := by
  by_cases bounded : index < molecule.atomCount
  · simp [applyAtomIndex, bounded, Equiv.Perm.mul_apply]
  · simp [applyAtomIndex, bounded]

/-- The bounded action of an inverse permutation undoes the forward action. -/
theorem applyAtomIndex_inv_apply (molecule : SemanticMolecule)
    (σ : Equiv.Perm (Fin molecule.atomCount)) (index : ℕ) :
    applyAtomIndex molecule σ⁻¹ (applyAtomIndex molecule σ index) = index := by
  by_cases bounded : index < molecule.atomCount
  · simp [applyAtomIndex, bounded, Equiv.Perm.inv_def]
  · simp [applyAtomIndex, bounded]

/-- The forward bounded action undoes the inverse permutation. -/
theorem applyAtomIndex_apply_inv (molecule : SemanticMolecule)
    (σ : Equiv.Perm (Fin molecule.atomCount)) (index : ℕ) :
    applyAtomIndex molecule σ (applyAtomIndex molecule σ⁻¹ index) = index := by
  by_cases bounded : index < molecule.atomCount
  · simp [applyAtomIndex, bounded, Equiv.Perm.inv_def]
  · simp [applyAtomIndex, bounded]

/-! ## Participant lists -/

theorem map_applyAtomIndex_one (molecule : SemanticMolecule) (participants : List ℕ) :
    participants.map
        (applyAtomIndex molecule (1 : Equiv.Perm (Fin molecule.atomCount))) = participants := by
  induction participants with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [applyAtomIndex_one, inductionHypothesis]

theorem map_applyAtomIndex_mul (molecule : SemanticMolecule)
    (σ τ : Equiv.Perm (Fin molecule.atomCount)) (participants : List ℕ) :
    participants.map (applyAtomIndex molecule (σ * τ)) =
      (participants.map (applyAtomIndex molecule τ)).map
        (applyAtomIndex molecule σ) := by
  induction participants with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, applyAtomIndex_mul, inductionHypothesis]

theorem map_applyAtomIndex_inv_apply (molecule : SemanticMolecule)
    (σ : Equiv.Perm (Fin molecule.atomCount)) (participants : List ℕ) :
    (participants.map (applyAtomIndex molecule σ)).map
        (applyAtomIndex molecule σ⁻¹) = participants := by
  induction participants with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, applyAtomIndex_inv_apply, inductionHypothesis]

theorem map_applyAtomIndex_apply_inv (molecule : SemanticMolecule)
    (σ : Equiv.Perm (Fin molecule.atomCount)) (participants : List ℕ) :
    (participants.map (applyAtomIndex molecule σ⁻¹)).map
        (applyAtomIndex molecule σ) = participants := by
  induction participants with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, applyAtomIndex_apply_inv, inductionHypothesis]

/-- Relabel the participant incidence of one interaction.  The interaction kind is unchanged. -/
def mapInteractionParticipants (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount))
    (interaction : SemanticInteraction) : SemanticInteraction where
  participants := interaction.participants.map (applyAtomIndex molecule atomPerm)
  kind := interaction.kind

@[simp] theorem mapInteractionParticipants_participants (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) (interaction : SemanticInteraction) :
    (mapInteractionParticipants molecule atomPerm interaction).participants =
      interaction.participants.map (applyAtomIndex molecule atomPerm) := rfl

@[simp] theorem mapInteractionParticipants_kind (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) (interaction : SemanticInteraction) :
    (mapInteractionParticipants molecule atomPerm interaction).kind = interaction.kind := rfl

theorem mapInteractionParticipants_nodup (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) {interaction : SemanticInteraction}
    (nodup : interaction.participants.Nodup) :
    (mapInteractionParticipants molecule atomPerm interaction).participants.Nodup := by
  simpa [mapInteractionParticipants] using
    nodup.map (applyAtomIndex_injective molecule atomPerm)

/-- Mapping participants preserves boundedness of every participant. -/
theorem mapInteractionParticipants_all_bounded_iff (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) (interaction : SemanticInteraction) :
    (mapInteractionParticipants molecule atomPerm interaction).participants.all
        (fun atom => decide (atom < molecule.atomCount)) = true ↔
      interaction.participants.all (fun atom => decide (atom < molecule.atomCount)) = true := by
  constructor
  · intro mapped
    rw [List.all_eq_true]
    intro index indexMem
    have imageMem : applyAtomIndex molecule atomPerm index ∈
        interaction.participants.map (applyAtomIndex molecule atomPerm) :=
      List.mem_map_of_mem indexMem
    have imageBounded : applyAtomIndex molecule atomPerm index < molecule.atomCount := by
      have := (List.all_eq_true.mp mapped) _ (by simpa using imageMem)
      simpa using this
    simpa using (applyAtomIndex_lt_iff molecule atomPerm index).mp imageBounded
  · intro original
    rw [List.all_eq_true]
    intro index indexMem
    rcases List.mem_map.mp indexMem with ⟨source, sourceMem, imageEq⟩
    subst imageEq
    have sourceBounded : source < molecule.atomCount := by
      have := (List.all_eq_true.mp original) _ sourceMem
      simpa using this
    simpa using applyAtomIndex_lt molecule atomPerm sourceBounded

/-- Relabelling participants preserves structural well-formedness of the interaction. -/
theorem mapInteractionParticipants_wellFormed_iff (molecule : SemanticMolecule)
    (atomPerm : Equiv.Perm (Fin molecule.atomCount)) (interaction : SemanticInteraction) :
    (mapInteractionParticipants molecule atomPerm interaction).WellFormed
        molecule.atomCount ↔
      interaction.WellFormed molecule.atomCount := by
  have lengthEq : (interaction.participants.map
      (applyAtomIndex molecule atomPerm)).length = interaction.participants.length :=
    List.length_map _
  rw [SemanticInteraction.WellFormed, SemanticInteraction.WellFormed,
    mapInteractionParticipants_participants, lengthEq]
  constructor
  · rintro ⟨lengthBound, nodup, allBounded⟩
    exact ⟨lengthBound, List.Nodup.of_map _ nodup,
      (mapInteractionParticipants_all_bounded_iff molecule atomPerm interaction).mp allBounded⟩
  · rintro ⟨lengthBound, nodup, allBounded⟩
    exact ⟨lengthBound, nodup.map (applyAtomIndex_injective molecule atomPerm),
      (mapInteractionParticipants_all_bounded_iff molecule atomPerm interaction).mpr allBounded⟩

/-- Two interactions with participant lists related by a permutation have the same structural
well-formedness.  This is the order-insensitivity used for participant incidences. -/
theorem wellFormed_of_participants_perm {atomCount : ℕ}
    {first second : SemanticInteraction}
    (participantsPerm : second.participants.Perm first.participants) :
    second.WellFormed atomCount ↔ first.WellFormed atomCount := by
  have lengthEq : second.participants.length = first.participants.length :=
    participantsPerm.length_eq
  rw [SemanticInteraction.WellFormed, SemanticInteraction.WellFormed]
  constructor
  · rintro ⟨lengthBound, nodup, allBounded⟩
    refine ⟨by omega, participantsPerm.nodup_iff.mp nodup, ?_⟩
    rw [List.all_eq_true] at allBounded ⊢
    intro index indexMem
    exact allBounded index (participantsPerm.mem_iff.mpr indexMem)
  · rintro ⟨lengthBound, nodup, allBounded⟩
    refine ⟨by omega, participantsPerm.nodup_iff.mpr nodup, ?_⟩
    rw [List.all_eq_true] at allBounded ⊢
    intro index indexMem
    exact allBounded index (participantsPerm.mem_iff.mp indexMem)

/-! ## Molecular automorphisms -/

/-- The ambient permutation group of a molecule: atom indices together with interaction
occurrences.  `PermutationCarrier molecule` is a group under componentwise multiplication. -/
abbrev PermutationCarrier (molecule : SemanticMolecule) : Type :=
  Equiv.Perm (Fin molecule.atomCount) ×
    Equiv.Perm (Fin molecule.interactions.length)

/-- A permutation of atom indices and interaction occurrences is a molecular automorphism when it
preserves every stored `SemanticAtom` (hence element, isotope, charge, radical count and aromatic
flag), every interaction kind, and every participant incidence up to `List.Perm`.

Interaction identity is occurrence identity: the interaction permutation is an equivalence on
`Fin molecule.interactions.length`, so duplicate interaction values remain distinct occurrences. -/
def IsAutomorphism (molecule : SemanticMolecule)
    (perm : PermutationCarrier molecule) : Prop :=
  (∀ atom : Fin molecule.atomCount,
      molecule.atoms.get (perm.1 atom) = molecule.atoms.get atom) ∧
    (∀ interaction : Fin molecule.interactions.length,
      (molecule.interactions.get (perm.2 interaction)).kind =
        (molecule.interactions.get interaction).kind) ∧
    ∀ interaction : Fin molecule.interactions.length,
      ((molecule.interactions.get interaction).participants.map
          (applyAtomIndex molecule perm.1)).Perm
        (molecule.interactions.get (perm.2 interaction)).participants

theorem isAutomorphism_one (molecule : SemanticMolecule) :
    molecule.IsAutomorphism 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom
    simp
  · intro interaction
    rfl
  · intro interaction
    have oneFirst : (1 : PermutationCarrier molecule).1 =
        (1 : Equiv.Perm (Fin molecule.atomCount)) := rfl
    have oneSecond : (1 : PermutationCarrier molecule).2 =
        (1 : Equiv.Perm (Fin molecule.interactions.length)) := rfl
    rw [oneFirst, map_applyAtomIndex_one, oneSecond]
    simp

theorem isAutomorphism_mul (molecule : SemanticMolecule)
    {σ τ : PermutationCarrier molecule}
    (hσ : molecule.IsAutomorphism σ) (hτ : molecule.IsAutomorphism τ) :
    molecule.IsAutomorphism (σ * τ) := by
  rcases hσ with ⟨hσatom, hσkind, hσparticipants⟩
  rcases hτ with ⟨hτatom, hτkind, hτparticipants⟩
  refine ⟨?_, ?_, ?_⟩
  · intro atom
    calc molecule.atoms.get ((σ * τ).1 atom)
        = molecule.atoms.get (σ.1 (τ.1 atom)) := by
          simp [Equiv.Perm.mul_apply]
      _ = molecule.atoms.get (τ.1 atom) := hσatom (τ.1 atom)
      _ = molecule.atoms.get atom := hτatom atom
  · intro interaction
    calc (molecule.interactions.get ((σ * τ).2 interaction)).kind
        = (molecule.interactions.get (σ.2 (τ.2 interaction))).kind := by
          simp [Equiv.Perm.mul_apply]
      _ = (molecule.interactions.get (τ.2 interaction)).kind :=
          hσkind (τ.2 interaction)
      _ = (molecule.interactions.get interaction).kind := hτkind interaction
  · intro interaction
    have composed :=
      ((hτparticipants interaction).map (applyAtomIndex molecule σ.1)).trans
        (hσparticipants (τ.2 interaction))
    simpa [Equiv.Perm.mul_apply, map_applyAtomIndex_mul] using composed

theorem isAutomorphism_inv (molecule : SemanticMolecule)
    {σ : PermutationCarrier molecule}
    (hσ : molecule.IsAutomorphism σ) : molecule.IsAutomorphism σ⁻¹ := by
  rcases hσ with ⟨hσatom, hσkind, hσparticipants⟩
  refine ⟨?_, ?_, ?_⟩
  · intro atom
    have preserved := hσatom (σ.1.symm atom)
    simpa using preserved.symm
  · intro interaction
    have preserved := hσkind (σ.2.symm interaction)
    simpa using preserved.symm
  · intro interaction
    have preserved : ((molecule.interactions.get (σ.2.symm interaction)).participants.map
        (applyAtomIndex molecule σ.1)).Perm
          (molecule.interactions.get interaction).participants := by
      simpa using hσparticipants (σ.2.symm interaction)
    have mapped := preserved.map (applyAtomIndex molecule σ.1⁻¹)
    rw [map_applyAtomIndex_inv_apply] at mapped
    simpa [Equiv.Perm.inv_def] using mapped.symm

/-- The automorphism group of a full semantic molecule, as a subgroup of the product permutation
group.  Group identity, inverse and composition are inherited from the ambient product, and the
subgroup proof fields are exactly the preservation obligations. -/
def Aut (molecule : SemanticMolecule) : Subgroup (PermutationCarrier molecule) where
  carrier := {perm | molecule.IsAutomorphism perm}
  one_mem' := molecule.isAutomorphism_one
  mul_mem' := by
    intro σ τ hσ hτ
    exact molecule.isAutomorphism_mul hσ hτ
  inv_mem' := by
    intro σ hσ
    exact molecule.isAutomorphism_inv hσ

/-- The atom-index permutation underlying a molecular automorphism. -/
def atomPerm (molecule : SemanticMolecule) (e : molecule.Aut) :
    Equiv.Perm (Fin molecule.atomCount) :=
  (e : PermutationCarrier molecule).1

/-- The interaction-occurrence permutation underlying a molecular automorphism. -/
def interactionPerm (molecule : SemanticMolecule) (e : molecule.Aut) :
    Equiv.Perm (Fin molecule.interactions.length) :=
  (e : PermutationCarrier molecule).2

@[simp] theorem atomPerm_one (molecule : SemanticMolecule) :
    molecule.atomPerm (1 : molecule.Aut) = 1 := rfl

@[simp] theorem interactionPerm_one (molecule : SemanticMolecule) :
    molecule.interactionPerm (1 : molecule.Aut) = 1 := rfl

@[simp] theorem atomPerm_mul (molecule : SemanticMolecule) (e f : molecule.Aut) :
    molecule.atomPerm (e * f) = molecule.atomPerm e * molecule.atomPerm f := rfl

@[simp] theorem interactionPerm_mul (molecule : SemanticMolecule) (e f : molecule.Aut) :
    molecule.interactionPerm (e * f) =
      molecule.interactionPerm e * molecule.interactionPerm f := rfl

@[simp] theorem atomPerm_inv (molecule : SemanticMolecule) (e : molecule.Aut) :
    molecule.atomPerm e⁻¹ = (molecule.atomPerm e)⁻¹ := rfl

@[simp] theorem interactionPerm_inv (molecule : SemanticMolecule) (e : molecule.Aut) :
    molecule.interactionPerm e⁻¹ = (molecule.interactionPerm e)⁻¹ := rfl

/-- Every automorphism preserves every stored atom exactly. -/
theorem atom_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (atom : Fin molecule.atomCount) :
    molecule.atoms.get (molecule.atomPerm e atom) = molecule.atoms.get atom :=
  e.property.1 atom

/-- Every automorphism preserves every interaction kind. -/
theorem kind_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (interaction : Fin molecule.interactions.length) :
    (molecule.interactions.get (molecule.interactionPerm e interaction)).kind =
      (molecule.interactions.get interaction).kind :=
  e.property.2.1 interaction

/-- Every automorphism preserves every interaction incidence up to participant-list order. -/
theorem participants_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (interaction : Fin molecule.interactions.length) :
    ((molecule.interactions.get interaction).participants.map
        (applyAtomIndex molecule (molecule.atomPerm e))).Perm
      (molecule.interactions.get (molecule.interactionPerm e interaction)).participants :=
  e.property.2.2 interaction

/-! ### Component data of a preserved atom -/

theorem atom_element_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (atom : Fin molecule.atomCount) :
    (molecule.atoms.get (molecule.atomPerm e atom)).element =
      (molecule.atoms.get atom).element :=
  congrArg SemanticAtom.element (molecule.atom_preserving e atom)

theorem atom_isotopeMassNumber?_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (atom : Fin molecule.atomCount) :
    (molecule.atoms.get (molecule.atomPerm e atom)).isotopeMassNumber? =
      (molecule.atoms.get atom).isotopeMassNumber? :=
  congrArg SemanticAtom.isotopeMassNumber? (molecule.atom_preserving e atom)

theorem atom_formalCharge_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (atom : Fin molecule.atomCount) :
    (molecule.atoms.get (molecule.atomPerm e atom)).formalCharge =
      (molecule.atoms.get atom).formalCharge :=
  congrArg SemanticAtom.formalCharge (molecule.atom_preserving e atom)

theorem atom_unpairedElectrons_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (atom : Fin molecule.atomCount) :
    (molecule.atoms.get (molecule.atomPerm e atom)).unpairedElectrons =
      (molecule.atoms.get atom).unpairedElectrons :=
  congrArg SemanticAtom.unpairedElectrons (molecule.atom_preserving e atom)

theorem atom_aromaticInput_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (atom : Fin molecule.atomCount) :
    (molecule.atoms.get (molecule.atomPerm e atom)).aromaticInput =
      (molecule.atoms.get atom).aromaticInput :=
  congrArg SemanticAtom.aromaticInput (molecule.atom_preserving e atom)

/-! ### Exact bounded action of an automorphism on participants -/

theorem participant_apply_of_lt (molecule : SemanticMolecule) (e : molecule.Aut)
    {index : ℕ} (bounded : index < molecule.atomCount) :
    applyAtomIndex molecule (molecule.atomPerm e) index =
      (molecule.atomPerm e ⟨index, bounded⟩).val :=
  applyAtomIndex_of_lt molecule (molecule.atomPerm e) bounded

theorem participant_apply_lt (molecule : SemanticMolecule) (e : molecule.Aut)
    {index : ℕ} (bounded : index < molecule.atomCount) :
    applyAtomIndex molecule (molecule.atomPerm e) index < molecule.atomCount :=
  applyAtomIndex_lt molecule (molecule.atomPerm e) bounded

/-! ### Identity, inverse and composition preserve the same data -/

theorem one_atom_preserving (molecule : SemanticMolecule)
    (atom : Fin molecule.atomCount) :
    molecule.atoms.get ((molecule.atomPerm (1 : molecule.Aut)) atom) =
      molecule.atoms.get atom := by
  simp

theorem one_kind_preserving (molecule : SemanticMolecule)
    (interaction : Fin molecule.interactions.length) :
    (molecule.interactions.get
        ((molecule.interactionPerm (1 : molecule.Aut)) interaction)).kind =
      (molecule.interactions.get interaction).kind := by
  simp

theorem one_participants_preserving (molecule : SemanticMolecule)
    (interaction : Fin molecule.interactions.length) :
    ((molecule.interactions.get interaction).participants.map
        (applyAtomIndex molecule
          (molecule.atomPerm (1 : molecule.Aut)))).Perm
      (molecule.interactions.get interaction).participants := by
  simp [atomPerm_one, map_applyAtomIndex_one]

theorem mul_atom_preserving (molecule : SemanticMolecule) (e f : molecule.Aut)
    (atom : Fin molecule.atomCount) :
    molecule.atoms.get
        (molecule.atomPerm e (molecule.atomPerm f atom)) =
      molecule.atoms.get atom :=
  (molecule.atom_preserving e (molecule.atomPerm f atom)).trans
    (molecule.atom_preserving f atom)

theorem mul_kind_preserving (molecule : SemanticMolecule) (e f : molecule.Aut)
    (interaction : Fin molecule.interactions.length) :
    (molecule.interactions.get
        (molecule.interactionPerm e
          (molecule.interactionPerm f interaction))).kind =
      (molecule.interactions.get interaction).kind :=
  (molecule.kind_preserving e (molecule.interactionPerm f interaction)).trans
    (molecule.kind_preserving f interaction)

theorem mul_participants_preserving (molecule : SemanticMolecule) (e f : molecule.Aut)
    (interaction : Fin molecule.interactions.length) :
    ((molecule.interactions.get interaction).participants.map
        (applyAtomIndex molecule
          (molecule.atomPerm e * molecule.atomPerm f))).Perm
      (molecule.interactions.get
        (molecule.interactionPerm e
          (molecule.interactionPerm f interaction))).participants := by
  have composed :=
    ((molecule.participants_preserving f interaction).map
      (applyAtomIndex molecule (molecule.atomPerm e))).trans
      (molecule.participants_preserving e (molecule.interactionPerm f interaction))
  simpa [map_applyAtomIndex_mul] using composed

theorem inv_atom_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (atom : Fin molecule.atomCount) :
    molecule.atoms.get ((molecule.atomPerm e).symm atom) =
      molecule.atoms.get atom := by
  have preserved := molecule.atom_preserving e ((molecule.atomPerm e).symm atom)
  simpa using preserved.symm

theorem inv_kind_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (interaction : Fin molecule.interactions.length) :
    (molecule.interactions.get
        ((molecule.interactionPerm e).symm interaction)).kind =
      (molecule.interactions.get interaction).kind := by
  have preserved := molecule.kind_preserving e
    ((molecule.interactionPerm e).symm interaction)
  simpa using preserved.symm

theorem inv_participants_preserving (molecule : SemanticMolecule) (e : molecule.Aut)
    (interaction : Fin molecule.interactions.length) :
    ((molecule.interactions.get interaction).participants.map
        (applyAtomIndex molecule (molecule.atomPerm e).symm)).Perm
      (molecule.interactions.get
        ((molecule.interactionPerm e).symm interaction)).participants := by
  simpa [Equiv.Perm.inv_def] using
    molecule.participants_preserving e⁻¹ interaction

/-! ### Interaction occurrences transport their structural contract -/

/-- An automorphism carries the structural well-formedness of an interaction occurrence to the
occurrence that is its image under the interaction permutation, and back. -/
theorem wellFormed_at_interactionPerm_iff (molecule : SemanticMolecule) (e : molecule.Aut)
    (interaction : Fin molecule.interactions.length) :
    (molecule.interactions.get
        (molecule.interactionPerm e interaction)).WellFormed molecule.atomCount ↔
      (molecule.interactions.get interaction).WellFormed molecule.atomCount := by
  have permuted : (molecule.interactions.get
      (molecule.interactionPerm e interaction)).participants.Perm
      (mapInteractionParticipants molecule (molecule.atomPerm e)
        (molecule.interactions.get interaction)).participants := by
    simpa [mapInteractionParticipants_participants] using
      (molecule.participants_preserving e interaction).symm
  exact (wellFormed_of_participants_perm
      (first := mapInteractionParticipants molecule (molecule.atomPerm e)
        (molecule.interactions.get interaction)) permuted).trans
    (mapInteractionParticipants_wellFormed_iff molecule (molecule.atomPerm e)
      (molecule.interactions.get interaction))

/-! ## Conformations and relabelling orbits

The action below reassigns a coordinate to an atom label.  It is *not* a Euclidean motion and it
carries no chirality verdict: `AtomAssignment.relabel` leaves the set of occupied points unchanged
(see `range_relabel`), while a rigid motion changes that set in general. -/

/-- An assignment of an arbitrary value (typically an exact rational point) to every atom index. -/
abbrev AtomAssignment (molecule : SemanticMolecule) (Point : Type*) :=
  Fin molecule.atomCount → Point

/-- Reassign coordinates to atom labels under an atom permutation.  The point carried by the atom
named `atom` after relabelling is the point that was carried by `σ.symm atom` before. -/
def AtomAssignment.relabel {molecule : SemanticMolecule} {Point : Type*}
    (positions : AtomAssignment molecule Point)
    (σ : Equiv.Perm (Fin molecule.atomCount)) : AtomAssignment molecule Point :=
  fun atom => positions (σ.symm atom)

@[simp] theorem AtomAssignment.relabel_one {molecule : SemanticMolecule} {Point : Type*}
    (positions : AtomAssignment molecule Point) :
    AtomAssignment.relabel positions
        (1 : Equiv.Perm (Fin molecule.atomCount)) = positions := by
  funext atom
  simp [AtomAssignment.relabel]

theorem AtomAssignment.relabel_mul {molecule : SemanticMolecule} {Point : Type*}
    (positions : AtomAssignment molecule Point)
    (σ τ : Equiv.Perm (Fin molecule.atomCount)) :
    AtomAssignment.relabel positions (σ * τ) =
      AtomAssignment.relabel (AtomAssignment.relabel positions τ) σ := by
  funext atom
  simp only [AtomAssignment.relabel]
  congr 1

/-- Relabelling only moves points between atom labels; the occupied point set is unchanged. -/
theorem AtomAssignment.range_relabel {molecule : SemanticMolecule} {Point : Type*}
    (positions : AtomAssignment molecule Point)
    (σ : Equiv.Perm (Fin molecule.atomCount)) :
    Set.range (AtomAssignment.relabel positions σ) = Set.range positions := by
  apply Set.Subset.antisymm
  · rintro point ⟨atom, rfl⟩
    exact ⟨σ.symm atom, rfl⟩
  · rintro point ⟨atom, rfl⟩
    exact ⟨σ atom, by simp [AtomAssignment.relabel]⟩

/-- The action of a molecular automorphism on atom-indexed coordinates. -/
def applyPositions {molecule : SemanticMolecule} {Point : Type*} (e : molecule.Aut)
    (positions : AtomAssignment molecule Point) : AtomAssignment molecule Point :=
  AtomAssignment.relabel positions (molecule.atomPerm e)

@[simp] theorem applyPositions_one {molecule : SemanticMolecule} {Point : Type*}
    (positions : AtomAssignment molecule Point) :
    applyPositions (1 : molecule.Aut) positions = positions := by
  simp [applyPositions]

theorem applyPositions_mul {molecule : SemanticMolecule} {Point : Type*} (e f : molecule.Aut)
    (positions : AtomAssignment molecule Point) :
    applyPositions (e * f) positions =
      applyPositions e (applyPositions f positions) := by
  simp [applyPositions, SemanticMolecule.AtomAssignment.relabel_mul]

theorem applyPositions_inv_left {molecule : SemanticMolecule} {Point : Type*}
    (e : molecule.Aut) (positions : AtomAssignment molecule Point) :
    applyPositions e⁻¹ (applyPositions e positions) = positions := by
  rw [← applyPositions_mul]
  simp

theorem applyPositions_inv_right {molecule : SemanticMolecule} {Point : Type*}
    (e : molecule.Aut) (positions : AtomAssignment molecule Point) :
    applyPositions e (applyPositions e⁻¹ positions) = positions := by
  rw [← applyPositions_mul]
  simp

/-- Two coordinate assignments are in the same relabelling orbit when some molecular automorphism
carries one to the other.  This is geometric *relabelling* equivalence, not rigid congruence. -/
def SamePositionOrbit (molecule : SemanticMolecule) {Point : Type*}
    (positions target : AtomAssignment molecule Point) : Prop :=
  ∃ e : molecule.Aut, target = applyPositions e positions

theorem samePositionOrbit_refl (molecule : SemanticMolecule) {Point : Type*}
    (positions : AtomAssignment molecule Point) :
    SamePositionOrbit molecule positions positions :=
  ⟨1, by simp⟩

theorem samePositionOrbit_symm (molecule : SemanticMolecule) {Point : Type*}
    {positions target : AtomAssignment molecule Point}
    (related : SamePositionOrbit molecule positions target) :
    SamePositionOrbit molecule target positions := by
  rcases related with ⟨e, rfl⟩
  refine ⟨e⁻¹, ?_⟩
  exact (applyPositions_inv_left e positions).symm

theorem samePositionOrbit_trans (molecule : SemanticMolecule) {Point : Type*}
    {positions middle target : AtomAssignment molecule Point}
    (first : SamePositionOrbit molecule positions middle)
    (second : SamePositionOrbit molecule middle target) :
    SamePositionOrbit molecule positions target := by
  rcases first with ⟨e, rfl⟩
  rcases second with ⟨f, rfl⟩
  refine ⟨f * e, ?_⟩
  rw [applyPositions_mul]

/-- The relabelling-orbit setoid on coordinate assignments. -/
def positionOrbitSetoid (molecule : SemanticMolecule) (Point : Type*) :
    Setoid (AtomAssignment molecule Point) where
  r := SamePositionOrbit molecule
  iseqv :=
    ⟨samePositionOrbit_refl molecule, samePositionOrbit_symm molecule,
      samePositionOrbit_trans molecule⟩

/-- The relabelling orbit of a coordinate assignment. -/
def positionOrbit (molecule : SemanticMolecule) {Point : Type*}
    (positions : AtomAssignment molecule Point) : Set (AtomAssignment molecule Point) :=
  {target | SamePositionOrbit molecule positions target}

@[simp] theorem mem_positionOrbit_iff (molecule : SemanticMolecule) {Point : Type*}
    (positions target : AtomAssignment molecule Point) :
    target ∈ molecule.positionOrbit positions ↔
      SamePositionOrbit molecule positions target := Iff.rfl

/-- Exact rational atom-indexed conformations: the concrete geometry specialization of
`AtomAssignment` using the rational point type already present in the authoritative input module.
This is an ordinary conformation of the full semantic molecule, indexed by atom label. -/
abbrev RationalConformation (molecule : SemanticMolecule) : Type :=
  AtomAssignment molecule CartesianPoint3

/-- Membership in a rational-conformation relabelling orbit is exactly transport by some molecular
automorphism.  Together with `positionOrbitSetoid` this gives a genuine equivalence relation and an
honest orbit set on conformations, without any rigid-motion claim. -/
theorem rationalConformation_mem_orbit_iff (molecule : SemanticMolecule)
    (positions target : RationalConformation molecule) :
    target ∈ molecule.positionOrbit positions ↔
      ∃ e : molecule.Aut, target = applyPositions e positions :=
  Iff.rfl

/-! ## Role-enriched automorphisms

`SemanticAtom` and `SemanticInteraction` do not record donor, acceptor, haptic or other role
data.  A role assignment is therefore genuinely extra structure.  An automorphism of the raw
semantic molecule has no reason to respect it; `RoleEnrichedAut` is the subgroup that does, and
the rest of this section states exactly that extra obligation. -/

/-- Extra role data attached to atom indices and interaction occurrences.  This is the explicit
extension point for donor/acceptor/haptic and similar chemistry that the raw representation does
not encode. -/
structure RoleAssignment (molecule : SemanticMolecule)
    (AtomRole : Type*) (InteractionRole : Type*) where
  atomRole : Fin molecule.atomCount → AtomRole
  interactionRole : Fin molecule.interactions.length → InteractionRole

variable {AtomRole InteractionRole : Type*}

namespace RoleAssignment

/-- Compatibility of a permutation carrier with a role assignment: every role *color* is
constant along the atom permutation and the interaction-occurrence permutation.

This is only a generic fixed-color condition.  It does not transport donor/acceptor/haptic
incidence data: an `InteractionRole` that itself mentions atom indices would have those indices
frozen rather than moved by the atom permutation.  Genuine joint role integration would require an
additional equivariance obligation linking the atom action to the interaction-role action. -/
def Compatible {molecule : SemanticMolecule}
    (roles : RoleAssignment molecule AtomRole InteractionRole)
    (perm : PermutationCarrier molecule) : Prop :=
  (∀ atom : Fin molecule.atomCount,
      roles.atomRole (perm.1 atom) = roles.atomRole atom) ∧
    ∀ interaction : Fin molecule.interactions.length,
      roles.interactionRole (perm.2 interaction) =
        roles.interactionRole interaction

end RoleAssignment

theorem roleCompatible_one (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole) :
    roles.Compatible 1 := by
  refine ⟨?_, ?_⟩ <;> intro index <;> rfl

theorem roleCompatible_mul (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole)
    {σ τ : PermutationCarrier molecule}
    (hσ : roles.Compatible σ) (hτ : roles.Compatible τ) :
    roles.Compatible (σ * τ) := by
  rcases hσ with ⟨hσatom, hσinteraction⟩
  rcases hτ with ⟨hτatom, hτinteraction⟩
  refine ⟨?_, ?_⟩
  · intro atom
    calc roles.atomRole ((σ * τ).1 atom)
        = roles.atomRole (σ.1 (τ.1 atom)) := by simp [Equiv.Perm.mul_apply]
      _ = roles.atomRole (τ.1 atom) := hσatom (τ.1 atom)
      _ = roles.atomRole atom := hτatom atom
  · intro interaction
    calc roles.interactionRole ((σ * τ).2 interaction)
        = roles.interactionRole (σ.2 (τ.2 interaction)) := by
          simp [Equiv.Perm.mul_apply]
      _ = roles.interactionRole (τ.2 interaction) := hσinteraction (τ.2 interaction)
      _ = roles.interactionRole interaction := hτinteraction interaction

theorem roleCompatible_inv (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole)
    {σ : PermutationCarrier molecule} (hσ : roles.Compatible σ) :
    roles.Compatible σ⁻¹ := by
  rcases hσ with ⟨hσatom, hσinteraction⟩
  refine ⟨?_, ?_⟩
  · intro atom
    have preserved := hσatom (σ.1.symm atom)
    simpa using preserved.symm
  · intro interaction
    have preserved := hσinteraction (σ.2.symm interaction)
    simpa using preserved.symm

/-- The subgroup of the ambient permutation group that respects a fixed role assignment. -/
def rolePreservingSubgroup (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole) :
    Subgroup (PermutationCarrier molecule) where
  carrier := {perm | roles.Compatible perm}
  one_mem' := molecule.roleCompatible_one roles
  mul_mem' := by
    intro σ τ hσ hτ
    exact molecule.roleCompatible_mul roles hσ hτ
  inv_mem' := by
    intro σ hσ
    exact molecule.roleCompatible_inv roles hσ

/-- Role-enriched molecular automorphisms: constitution-preserving automorphisms that additionally
respect the supplied fixed role coloring.

This is a subgroup of `Aut`, and it may be *equal* to `Aut` (for example when the role assignment
is constant).  It is not a proper refinement in general.  Nothing in this module proves that raw
`SemanticMolecule` data determines these roles, and no theorem silently drops them.

The construction is a generic color-preserving subgroup, not an incidence-transporting role
semantics: role data that depends on atom indices is not transported by the atom permutation, and
donor/acceptor/haptic incidence transport remains a separate obligation for a future joint
role/constitution integration. -/
def RoleEnrichedAut (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole) :
    Subgroup (PermutationCarrier molecule) :=
  molecule.Aut ⊓ rolePreservingSubgroup molecule roles

theorem mem_roleEnrichedAut_iff (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole)
    (perm : PermutationCarrier molecule) :
    perm ∈ molecule.RoleEnrichedAut roles ↔
      perm ∈ molecule.Aut ∧ roles.Compatible perm := by
  simp [RoleEnrichedAut, rolePreservingSubgroup]

/-- Role enrichment can only shrink the automorphism group. -/
theorem roleEnrichedAut_le_aut (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole) :
    molecule.RoleEnrichedAut roles ≤ molecule.Aut :=
  inf_le_left

/-- The role-enriched automorphism group is itself a subgroup, so its elements have identity,
inverse and composition laws inherited from `PermutationCarrier`. -/
theorem roleEnrichedAut_one_mem (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole) :
    (1 : PermutationCarrier molecule) ∈ molecule.RoleEnrichedAut roles :=
  (molecule.RoleEnrichedAut roles).one_mem

/-- An element of the role-enriched group is a molecular automorphism. -/
theorem roleEnrichedAut_isAutomorphism (molecule : SemanticMolecule)
    (roles : RoleAssignment molecule AtomRole InteractionRole)
    {perm : PermutationCarrier molecule}
    (member : perm ∈ molecule.RoleEnrichedAut roles) :
    molecule.IsAutomorphism perm :=
  (molecule.roleEnrichedAut_le_aut roles) member

end SemanticMolecule

end TetraStereo.OneCenter
