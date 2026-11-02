import TetraStereo.OneCenter.SmilesTetrahedral
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false

namespace TetraStereo.OneCenter.Rule6HandednessSemantics

/-!
# Exact handedness semantics for a four-ligand Rule-6 carrier

This module identifies the mathematical content of the Rule-6 odd-automorphism gate.  A priority
ordering is represented by a permutation of four ligand positions.  Transporting that ordering by
a constitutional automorphism preserves its `R/S` descriptor exactly when that automorphism is
even.  Consequently, descriptor invariance under every admissible constitutional automorphism is
equivalent to the absence of an odd one.

The proof uses the sign homomorphism of the finite symmetric group.  The small bridge to the
production inversion-count Boolean is proved by kernel-checked case analysis over the twenty-four
members of `S₄`; it uses neither native evaluation nor a compiler-trust axiom.
-/

open RawMolecule

/-- The production list representation of a permutation of four positions. -/
def finFourPermutationList (permutation : Equiv.Perm (Fin 4)) : List Nat :=
  List.ofFn fun position : Fin 4 => (permutation position).val

/-- Every group-theoretic `S₄` permutation encodes one of the production permutations. -/
theorem finFourPermutationList_perm_range (permutation : Equiv.Perm (Fin 4)) :
    (finFourPermutationList permutation).Perm (List.range 4) := by
  simpa [finFourPermutationList, Function.comp_def, List.ofFn_eq_map] using
    permutation.ofFn_comp_perm (f := fun position : Fin 4 => position.val)

theorem finFourPermutationList_mem_permutations (permutation : Equiv.Perm (Fin 4)) :
    finFourPermutationList permutation ∈ List.permutations (List.range 4) :=
  List.mem_permutations.mpr (finFourPermutationList_perm_range permutation)

/-- Recover an `S₄` permutation from any duplicate-free production permutation list. -/
noncomputable def finFourEquivOfPermutationList (values : List Nat)
    (permutation : values.Perm (List.range 4)) : Equiv.Perm (Fin 4) :=
  let length_eq : values.length = 4 := by simpa using permutation.length_eq
  let toFun : Fin 4 → Fin 4 := fun position =>
    ⟨values[position.val]'(by simp [length_eq]),
      List.mem_range.mp (permutation.mem_iff.mp
        (values.getElem_mem (n := position.val)
          (by simp [length_eq])))⟩
  Equiv.ofBijective toFun ((Fintype.bijective_iff_injective_and_card toFun).mpr ⟨by
    intro left right equal
    apply Fin.ext
    have values_nodup : values.Nodup := permutation.nodup_iff.mpr List.nodup_range
    apply values_nodup.getElem_inj_iff.mp
    exact congrArg Fin.val equal
  , rfl⟩)

/-- Encoding after recovery returns the original production list exactly. -/
theorem finFourPermutationList_equivOfPermutationList (values : List Nat)
    (permutation : values.Perm (List.range 4)) :
    finFourPermutationList (finFourEquivOfPermutationList values permutation) = values := by
  have length_eq : values.length = 4 := by simpa using permutation.length_eq
  apply List.ext_get
  · simp [finFourPermutationList, length_eq]
  · intro n _ valueBound
    have n_lt : n < 4 := by simpa [length_eq] using valueBound
    interval_cases n <;> simp [finFourPermutationList, finFourEquivOfPermutationList]

/-- Every production list in the exhaustive four-position enumeration comes from an `S₄`
permutation. -/
theorem exists_finFourEquiv_permutationList_eq (values : List Nat)
    (member : values ∈ List.permutations (List.range 4)) :
    ∃ permutation : Equiv.Perm (Fin 4), finFourPermutationList permutation = values := by
  let permutation :=
    finFourEquivOfPermutationList values (List.mem_permutations.mp member)
  exact ⟨permutation, finFourPermutationList_equivOfPermutationList values _⟩

/-- The production inversion-count parity is exactly the sign of the corresponding `S₄`
permutation.  `fin_cases` emits twenty-four ordinary kernel proof branches. -/
theorem finFourPermutationIsEven_eq_sign (permutation : Equiv.Perm (Fin 4)) :
    RawMolecule.permutationIsEven (finFourPermutationList permutation) =
      (Equiv.Perm.sign permutation == 1) := by
  fin_cases permutation <;> decide

/-- The production `false` parity value is exactly group-theoretic odd sign. -/
theorem finFourPermutationIsOdd_iff_sign_negOne (permutation : Equiv.Perm (Fin 4)) :
    RawMolecule.permutationIsEven (finFourPermutationList permutation) = false ↔
      Equiv.Perm.sign permutation = -1 := by
  rw [finFourPermutationIsEven_eq_sign]
  rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with signEq | signEq
  · simp [signEq]
  · simp [signEq]

/-- The production `R/S` descriptor attached to an `S₄` priority ordering. -/
def descriptorOfFinFourOrdering (parity : TetrahedralInputParity)
    (ordering : Equiv.Perm (Fin 4)) : RS :=
  RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven (finFourPermutationList ordering))

/-- Descriptor handedness is invariant under every permutation satisfying `automorphism`. -/
def DescriptorInvariantUnder (automorphism : Equiv.Perm (Fin 4) → Prop)
    (parity : TetrahedralInputParity) : Prop :=
  ∀ ordering permutation,
    automorphism permutation →
    descriptorOfFinFourOrdering parity (ordering.trans permutation) =
      descriptorOfFinFourOrdering parity ordering

/-- Even automorphisms preserve every descriptor ordering. -/
theorem descriptor_eq_under_even
    {automorphism : Equiv.Perm (Fin 4) → Prop}
    (parity : TetrahedralInputParity)
    (all_even : ∀ permutation, automorphism permutation →
      Equiv.Perm.sign permutation = 1) :
    DescriptorInvariantUnder automorphism parity := by
  intro ordering permutation isAutomorphism
  have signEq := all_even permutation isAutomorphism
  unfold descriptorOfFinFourOrdering
  rw [finFourPermutationIsEven_eq_sign, finFourPermutationIsEven_eq_sign,
    Equiv.Perm.sign_trans, signEq]
  simp

/-- An odd automorphism reverses the descriptor of every ordering. -/
theorem descriptor_ne_under_odd
    (parity : TetrahedralInputParity) (ordering permutation : Equiv.Perm (Fin 4))
    (odd : Equiv.Perm.sign permutation = -1) :
    descriptorOfFinFourOrdering parity (ordering.trans permutation) ≠
      descriptorOfFinFourOrdering parity ordering := by
  unfold descriptorOfFinFourOrdering
  rw [finFourPermutationIsEven_eq_sign, finFourPermutationIsEven_eq_sign,
    Equiv.Perm.sign_trans, odd]
  rcases Int.units_eq_one_or (Equiv.Perm.sign ordering) with signEq | signEq <;>
    cases parity <;> norm_num [signEq, RawMolecule.descriptorOfParity] <;> decide

/-- Exact finite-group theorem: a four-position carrier has a well-defined descriptor modulo a
class of admissible permutations iff every admissible permutation is even.  No closure assumptions
on the class are needed for this equivalence. -/
theorem descriptorInvariantUnder_iff_all_even
    (automorphism : Equiv.Perm (Fin 4) → Prop)
    (parity : TetrahedralInputParity) :
    DescriptorInvariantUnder automorphism parity ↔
      ∀ permutation, automorphism permutation → Equiv.Perm.sign permutation = 1 := by
  constructor
  · intro invariant permutation isAutomorphism
    rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with even | odd
    · exact even
    · exact False.elim ((descriptor_ne_under_odd parity 1 permutation odd)
        (invariant 1 permutation isAutomorphism))
  · exact descriptor_eq_under_even parity

end TetraStereo.OneCenter.Rule6HandednessSemantics
