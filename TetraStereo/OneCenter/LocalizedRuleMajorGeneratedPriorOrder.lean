import TetraStereo.OneCenter.LocalizedRuleMajorGeneratedCompoundComparison
import TetraStereo.OneCenter.DeclarativeCIPCompleteLigandOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The four generated compounds admit a numeric rank that realizes the independent complete
prior-key order, including exact tie classes. The rank counts strictly smaller keys, so no
injectivity or distinctness assumption is needed. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open DeclarativeCIP
noncomputable section

variable {α : Type*} [LinearOrder α]

/-- The finite rank comparator agrees with key comparison even when several positions share a
key. -/
theorem keyRank_compare_without_injectivity (key : Fin 4 → α) (left right : Fin 4) :
    compare (keyRank key left) (keyRank key right) = compare (key left) (key right) := by
  rcases lt_trichotomy (key left) (key right) with hlt | heq | hgt
  · rw [compare_lt_iff_lt.2 hlt,
      compare_lt_iff_lt.2 (keyRank_lt_of_lt key hlt)]
  · have rankEq : keyRank key left = keyRank key right := by
      unfold keyRank
      rw [heq]
    rw [compare_eq_iff_eq.2 rankEq, compare_eq_iff_eq.2 heq]
  · rw [compare_gt_iff_gt.2 hgt,
      compare_gt_iff_gt.2 (keyRank_lt_of_lt key hgt)]

theorem keyRank_lt_iff_without_injectivity (key : Fin 4 → α) (left right : Fin 4) :
    keyRank key left < keyRank key right ↔ key left < key right := by
  rw [← compare_lt_iff_lt, keyRank_compare_without_injectivity,
    compare_lt_iff_lt]

theorem keyRank_eq_iff_without_injectivity (key : Fin 4 → α) (left right : Fin 4) :
    keyRank key left = keyRank key right ↔ key left = key right := by
  rw [← compare_eq_iff_eq, keyRank_compare_without_injectivity,
    compare_eq_iff_eq]

end
end TetraStereo.OneCenter.Rule4aTableBridge

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
noncomputable section
open scoped Classical

/-- One generated own-state package supplies all four successful compounds, their independent
keys at one shared layout bound, and a count-smaller priority whose comparator realizes both
strict order and ties. -/
theorem generated_prior_order (input : Input)
    (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    let target := ActualReaderPhysicalBranchInverse.topTarget input center
    let descriptorMap := descriptorMap input
    let stages : ∀ index : Fin 4,
        input.certified.RuleMajorBranchStages center index descriptorMap target :=
      fun index => Classical.choice
        (input.certified.exists_ruleMajorBranchStages center index descriptorMap target)
    let compounds : ∀ _index : Fin 4, input.certified.LocalizedRerootCompoundRule45Key :=
      fun _index => Classical.choose (by
        have valid := input.certified.localizedRerootCursorValid_of_incoming
          (input.certified.localizedLigandRootCursor center _index)
          (input.certified.localizedLigandRootCursor_incoming center _index)
        exact input.certified.exists_buildActualRuleMajorCompoundRule45Key_at_twice
          target (input.certified.localizedDependencyView (referenceState input) target)
          (input.certified.localizedLigandRootCursor center _index) valid)
    let W := max (stages ⟨0, by decide⟩).widthBound
      (max (stages ⟨1, by decide⟩).widthBound
        (max (stages ⟨2, by decide⟩).widthBound (stages ⟨3, by decide⟩).widthBound))
    let D := max (stages ⟨0, by decide⟩).depthBound
      (max (stages ⟨1, by decide⟩).depthBound
        (max (stages ⟨2, by decide⟩).depthBound (stages ⟨3, by decide⟩).depthBound))
    let key : Fin 4 → CompleteLigandPriorKey := fun index =>
      completeLigandPriorKeyAt input.certified.moleculeGraph descriptorMap
        (input.certified.topUnit center) (stages index).graph W D
    let rank : Fin 4 → Nat := keyRank key
    (∀ index : Fin 4,
      input.certified.buildActualRuleMajorCompoundRule45Key? target
        (input.certified.localizedDependencyView (referenceState input) target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center index) = some (compounds index)) ∧
    (∀ index : Fin 4,
      input.certified.buildActualRuleMajorCompoundRule45KeyExec? target
        (input.certified.localizedDependencyView (referenceState input) target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center index) = some (compounds index)) ∧
    (∀ index : Fin 4, rank index = (Finset.univ.filter fun other => key other < key index).card) ∧
    (∀ left right : Fin 4,
      input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (compounds left).prior (compounds right).prior = compare (key left) (key right)) ∧
    (∀ left right : Fin 4,
      input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (compounds left).prior (compounds right).prior = compare (rank left) (rank right)) ∧
    (∀ left right : Fin 4,
      input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (compounds left).prior (compounds right).prior = .lt ↔ key left < key right) ∧
    (∀ left right : Fin 4,
      input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (compounds left).prior (compounds right).prior = .eq ↔ key left = key right) ∧
    (∀ left right : Fin 4,
      rank left < rank right ↔ key left < key right) ∧
    (∀ left right : Fin 4,
      rank left = rank right ↔ key left = key right) := by
  let target := ActualReaderPhysicalBranchInverse.topTarget input center
  let descriptorMap := descriptorMap input
  let stages : ∀ index : Fin 4,
      input.certified.RuleMajorBranchStages center index descriptorMap target :=
    fun index => Classical.choice
      (input.certified.exists_ruleMajorBranchStages center index descriptorMap target)
  let compounds : ∀ _index : Fin 4, input.certified.LocalizedRerootCompoundRule45Key :=
    fun _index => Classical.choose (by
      have valid := input.certified.localizedRerootCursorValid_of_incoming
        (input.certified.localizedLigandRootCursor center _index)
        (input.certified.localizedLigandRootCursor_incoming center _index)
      exact input.certified.exists_buildActualRuleMajorCompoundRule45Key_at_twice
        target (input.certified.localizedDependencyView (referenceState input) target)
        (input.certified.localizedLigandRootCursor center _index) valid)
  let W := max (stages ⟨0, by decide⟩).widthBound
    (max (stages ⟨1, by decide⟩).widthBound
      (max (stages ⟨2, by decide⟩).widthBound (stages ⟨3, by decide⟩).widthBound))
  let D := max (stages ⟨0, by decide⟩).depthBound
    (max (stages ⟨1, by decide⟩).depthBound
      (max (stages ⟨2, by decide⟩).depthBound (stages ⟨3, by decide⟩).depthBound))
  let key : Fin 4 → CompleteLigandPriorKey := fun index =>
    completeLigandPriorKeyAt input.certified.moleculeGraph descriptorMap
      (input.certified.topUnit center) (stages index).graph W D
  let rank : Fin 4 → Nat := keyRank key
  have generated := generated_compound_prior_comparison input center singleBonded acyclic
  change (∀ index : Fin 4,
      input.certified.buildActualRuleMajorCompoundRule45Key? target
        (input.certified.localizedDependencyView (referenceState input) target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center index) = some (compounds index)) ∧
    (∀ left right : Fin 4,
      input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (compounds left).prior (compounds right).prior = compare (key left) (key right)) at generated
  refine ⟨generated.1, ?_, ?_, generated.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro index
    rw [input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact generated.1 index
  · intro index
    rfl
  · intro left right
    have ltRank :
        input.certified.compareLocalizedRerootCompoundRule4bcKeys
            (compounds left).prior (compounds right).prior = .lt ↔
          rank left < rank right := by
      rw [generated.2 left right, completeLigandPriorKey_compare_lt_iff]
      exact (keyRank_lt_iff_without_injectivity key left right).symm
    have eqRank :
        input.certified.compareLocalizedRerootCompoundRule4bcKeys
            (compounds left).prior (compounds right).prior = .eq ↔
          rank left = rank right := by
      rw [generated.2 left right, completeLigandPriorKey_compare_eq_iff]
      exact (keyRank_eq_iff_without_injectivity key left right).symm
    exact eq_compare_of_iff _ _ _ ltRank eqRank
  · intro left right
    rw [generated.2 left right, completeLigandPriorKey_compare_lt_iff]
  · intro left right
    rw [generated.2 left right, completeLigandPriorKey_compare_eq_iff]
  · intro left right
    exact keyRank_lt_iff_without_injectivity key left right
  · intro left right
    exact keyRank_eq_iff_without_injectivity key left right

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.keyRank_compare_without_injectivity
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.keyRank_lt_iff_without_injectivity
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.keyRank_eq_iff_without_injectivity
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_prior_order
