import TetraStereo.OneCenter.LocalizedRetainedCoherentSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
Every positive edge of a normalized component-incidence mass extends to a perfect
matching. The positive mass gives strict Hall inequality on any source family that
omits the prescribed source but can reach its prescribed target. Deleting those two
vertices therefore preserves Hall's inequality.

For the actual entry-equivalence mass, the resulting component bijection retains an
entry witness function using the prescribed entry exactly. This is a finite structural
matching result. It does not preserve physical signs of an earlier reconstruction or
identify all path images with one previously chosen molecular automorphism.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingForcedComponentMatching

open RetainedCoherentSymmetry
open scoped BigOperators

noncomputable section
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A positive edge arriving from outside a source family makes Hall's inequality
strict whenever its target belongs to that family's neighborhood. -/
theorem strict_hall_of_external_positive (neighbors : A → Finset B)
    (M : NormalizedEntryMass A B neighbors) (a₀ : A) (b₀ : B)
    (positive : 0 < M.mass a₀ b₀) (X : Finset A) (outside : a₀ ∉ X)
    (targetMember : b₀ ∈ X.biUnion neighbors) :
    X.card < (X.biUnion neighbors).card := by
  let N := X.biUnion neighbors
  have rowN (a : A) (member : a ∈ X) : (∑ b ∈ N, M.mass a b) = 1 := by
    calc
      (∑ b ∈ N, M.mass a b) = ∑ b : B, M.mass a b := by
        apply Finset.sum_subset (Finset.subset_univ N)
        intro b _ absent
        by_contra nonzero
        exact absent (Finset.mem_biUnion.mpr ⟨a, member, M.support a b nonzero⟩)
      _ = 1 := M.row_sum a
  have columnX (b : B) : (∑ a ∈ X, M.mass a b) ≤ 1 := by
    calc
      (∑ a ∈ X, M.mass a b) ≤ ∑ a : A, M.mass a b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X)
          (fun a _ _ => M.nonneg a b)
      _ = 1 := M.column_sum b
  have withSource : M.mass a₀ b₀ + (∑ a ∈ X, M.mass a b₀) ≤ 1 := by
    calc
      M.mass a₀ b₀ + (∑ a ∈ X, M.mass a b₀) =
          ∑ a ∈ insert a₀ X, M.mass a b₀ :=
            (Finset.sum_insert (f := fun a => M.mass a b₀) outside).symm
      _ ≤ ∑ a : A, M.mass a b₀ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun a _ _ => M.nonneg a b₀)
      _ = 1 := M.column_sum b₀
  have strictColumn : (∑ a ∈ X, M.mass a b₀) < 1 :=
    lt_of_lt_of_le (lt_add_of_pos_left _ positive) withSource
  have strictTotal : (∑ b ∈ N, ∑ a ∈ X, M.mass a b) < ∑ _b ∈ N, (1 : ℚ) :=
    Finset.sum_lt_sum (fun b _ => columnX b) ⟨b₀, targetMember, strictColumn⟩
  have mass : (X.card : ℚ) < (N.card : ℚ) := by
    calc
      (X.card : ℚ) = ∑ a ∈ X, (1 : ℚ) := by simp
      _ = ∑ a ∈ X, ∑ b ∈ N, M.mass a b :=
        Finset.sum_congr rfl (fun a member => (rowN a member).symm)
      _ = ∑ b ∈ N, ∑ a ∈ X, M.mass a b := Finset.sum_comm
      _ < ∑ _b ∈ N, (1 : ℚ) := strictTotal
      _ = (N.card : ℚ) := by simp
  exact_mod_cast mass

/-- The unmatched vertices satisfy Hall after the prescribed positive edge is removed. -/
theorem erase_hall_of_positive (neighbors : A → Finset B)
    (M : NormalizedEntryMass A B neighbors) (a₀ : A) (b₀ : B)
    (positive : 0 < M.mass a₀ b₀) (X : Finset A) (outside : a₀ ∉ X) :
    X.card ≤ (X.biUnion fun a => (neighbors a).erase b₀).card := by
  have unionErase : X.biUnion (fun a => (neighbors a).erase b₀) =
      (X.biUnion neighbors).erase b₀ := by
    ext b
    constructor
    · intro member
      obtain ⟨a, inX, atA⟩ := Finset.mem_biUnion.mp member
      obtain ⟨different, atA⟩ := Finset.mem_erase.mp atA
      exact Finset.mem_erase.mpr ⟨different, Finset.mem_biUnion.mpr ⟨a, inX, atA⟩⟩
    · intro member
      obtain ⟨different, present⟩ := Finset.mem_erase.mp member
      obtain ⟨a, inX, atA⟩ := Finset.mem_biUnion.mp present
      exact Finset.mem_biUnion.mpr ⟨a, inX, Finset.mem_erase.mpr ⟨different, atA⟩⟩
  rw [unionErase]
  by_cases present : b₀ ∈ X.biUnion neighbors
  · have strict := strict_hall_of_external_positive neighbors M a₀ b₀ positive X outside present
    rw [Finset.card_erase_of_mem present]
    omega
  · rw [Finset.erase_eq_of_notMem present]
    exact normalized_entry_mass_hall neighbors M X

/-- A positive mass entry is contained in a full component bijection supported by the
original neighbor relation. Neither the bijection nor its forced edge is assumed. -/
theorem exists_bijection_of_positive (neighbors : A → Finset B)
    (M : NormalizedEntryMass A B neighbors) (a₀ : A) (b₀ : B)
    (positive : 0 < M.mass a₀ b₀) :
    ∃ f : A ≃ B, f a₀ = b₀ ∧ ∀ a, f a ∈ neighbors a := by
  let S : Finset A := Finset.univ.erase a₀
  let rest : A → Finset B := fun a => (neighbors a).erase b₀
  have hall : ∀ X : Finset A, X ⊆ S → X.card ≤ (X.biUnion rest).card := by
    intro X subset
    apply erase_hall_of_positive neighbors M a₀ b₀ positive X
    intro member
    exact (Finset.mem_erase.mp (subset member)).1 rfl
  obtain ⟨g, injective, supported⟩ := exists_reps_of_card_le_biUnion S rest hall
  let f : A → B := fun a => if h : a = a₀ then b₀
    else g ⟨a, Finset.mem_erase.mpr ⟨h, Finset.mem_univ a⟩⟩
  have fInjective : Function.Injective f := by
    intro a b same
    dsimp only [f] at same
    split_ifs at same with ha hb
    · exact ha.trans hb.symm
    · exact False.elim ((Finset.mem_erase.mp
        (supported ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩⟩)).1 same.symm)
    · exact False.elim ((Finset.mem_erase.mp
        (supported ⟨a, Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩⟩)).1 same)
    · exact congrArg Subtype.val (injective same)
  have fSupported (a : A) : f a ∈ neighbors a := by
    by_cases same : a = a₀
    · subst a
      simpa only [f, dif_pos rfl] using M.support a₀ b₀ (ne_of_gt positive)
    · dsimp only [f]
      rw [dif_neg same]
      exact (Finset.mem_erase.mp
        (supported ⟨a, Finset.mem_erase.mpr ⟨same, Finset.mem_univ a⟩⟩)).2
  let equivalence := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨fInjective, normalized_entry_mass_card_eq M⟩)
  refine ⟨equivalence, ?_, fSupported⟩
  change f a₀ = b₀
  simp only [f, dif_pos rfl]

/-- An actual matched entry may be prescribed as the witness for its component pair.
All other pairs retain concrete matched-entry witnesses from the same entry equivalence. -/
theorem exists_component_bijection_forced_entry
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (ownerE : E → A) (ownerF : F → B) (entryEquiv : E ≃ F)
    (hEpos : ∀ a, 0 < (Finset.univ.filter fun x => ownerE x = a).card)
    (hFpos : ∀ b, 0 < (Finset.univ.filter fun y => ownerF y = b).card)
    (hFiber : ∀ x : E,
      (Finset.univ.filter fun z => ownerE z = ownerE x).card =
        (Finset.univ.filter fun y => ownerF y = ownerF (entryEquiv x)).card)
    (chosen : E) :
    ∃ (f : A ≃ B) (witness : A → E),
      f (ownerE chosen) = ownerF (entryEquiv chosen) ∧
      witness (ownerE chosen) = chosen ∧
      ∀ a, ownerE (witness a) = a ∧ ownerF (entryEquiv (witness a)) = f a := by
  let N := entryNeighbors ownerE ownerF entryEquiv
  let M := normalizedEntryMass_of_entryEquiv ownerE ownerF entryEquiv hEpos hFpos hFiber
  have countPositive : 0 < entryPairCount ownerE ownerF entryEquiv
      (ownerE chosen) (ownerF (entryEquiv chosen)) := by
    unfold entryPairCount
    apply Finset.card_pos.mpr
    exact ⟨chosen, by simp⟩
  have denominatorPositive :
      (0 : ℚ) < ((Finset.univ.filter fun x => ownerE x = ownerE chosen).card : ℚ) := by
    exact_mod_cast hEpos (ownerE chosen)
  have positive : 0 < M.mass (ownerE chosen) (ownerF (entryEquiv chosen)) := by
    change 0 < (entryPairCount ownerE ownerF entryEquiv
      (ownerE chosen) (ownerF (entryEquiv chosen)) : ℚ) *
      ((Finset.univ.filter fun x => ownerE x = ownerE chosen).card : ℚ)⁻¹
    exact mul_pos (by exact_mod_cast countPositive) (inv_pos.mpr denominatorPositive)
  obtain ⟨f, forced, supported⟩ :=
    exists_bijection_of_positive N M (ownerE chosen) (ownerF (entryEquiv chosen)) positive
  have witnesses : ∀ a, ∃ x : E, ownerE x = a ∧ ownerF (entryEquiv x) = f a := by
    intro a
    have member := supported a
    change f a ∈ (Finset.univ.filter fun x => ownerE x = a).image
      (fun x => ownerF (entryEquiv x)) at member
    obtain ⟨x, present, image⟩ := Finset.mem_image.mp member
    exact ⟨x, (Finset.mem_filter.mp present).2, image⟩
  choose original owner image using witnesses
  let witness : A → E := fun a => if a = ownerE chosen then chosen else original a
  refine ⟨f, witness, forced, ?_, ?_⟩
  · simp only [witness, if_pos rfl]
  · intro a
    by_cases same : a = ownerE chosen
    · subst a
      simpa only [witness, if_pos rfl] using
        (show ownerE chosen = ownerE chosen ∧ ownerF (entryEquiv chosen) = f (ownerE chosen)
          from ⟨rfl, forced.symm⟩)
    · simpa only [witness, if_neg same] using And.intro (owner a) (image a)

end
end TetraStereo.OneCenter.LocalizedChemicalRingForcedComponentMatching

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingForcedComponentMatching.strict_hall_of_external_positive
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingForcedComponentMatching.erase_hall_of_positive
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingForcedComponentMatching.exists_bijection_of_positive
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingForcedComponentMatching.exists_component_bijection_forced_entry
