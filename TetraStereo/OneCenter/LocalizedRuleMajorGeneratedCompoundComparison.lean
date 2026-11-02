import TetraStereo.OneCenter.LocalizedRuleMajorActualCompoundComparison
import TetraStereo.OneCenter.LocalizedRuleMajorOwnMolecularEvidence
import TetraStereo.OneCenter.LocalizedRuleMajorBranchStages
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Pairwise generated-own-state compound comparisons for every actual ligand branch. Stage
families and compound successes are chosen from their totality theorems; the resulting comparison
is against the independent complete molecular prior key. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput Rule4aTableBridge DeclarativeCIP
noncomputable section
open scoped Classical

theorem generated_compound_prior_comparison (input : Input)
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
    (∀ index : Fin 4,
      input.certified.buildActualRuleMajorCompoundRule45Key? target
        (input.certified.localizedDependencyView (referenceState input) target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center index) = some (compounds index)) ∧
    (∀ leftIndex rightIndex : Fin 4,
      input.certified.compareLocalizedRerootCompoundRule4bcKeys
          (compounds leftIndex).prior (compounds rightIndex).prior =
        compare
          (completeLigandPriorKeyAt input.certified.moleculeGraph descriptorMap
            (input.certified.topUnit center) (stages leftIndex).graph W D)
          (completeLigandPriorKeyAt input.certified.moleculeGraph descriptorMap
            (input.certified.topUnit center) (stages rightIndex).graph W D)) := by
  let target := ActualReaderPhysicalBranchInverse.topTarget input center
  let descriptorMap := descriptorMap input
  let stages : ∀ index : Fin 4,
      input.certified.RuleMajorBranchStages center index descriptorMap target :=
    fun index => Classical.choice
      (input.certified.exists_ruleMajorBranchStages center index descriptorMap target)
  let compoundExists : ∀ index : Fin 4,
      ∃ compound, input.certified.buildActualRuleMajorCompoundRule45Key? target
        (input.certified.localizedDependencyView (referenceState input) target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center index) = some compound := by
    intro index
    have valid := input.certified.localizedRerootCursorValid_of_incoming
      (input.certified.localizedLigandRootCursor center index)
      (input.certified.localizedLigandRootCursor_incoming center index)
    exact input.certified.exists_buildActualRuleMajorCompoundRule45Key_at_twice
      target (input.certified.localizedDependencyView (referenceState input) target)
      (input.certified.localizedLigandRootCursor center index) valid
  let compounds : ∀ index : Fin 4, input.certified.LocalizedRerootCompoundRule45Key :=
    fun index => Classical.choose (compoundExists index)
  have compoundsBuilt index := Classical.choose_spec (compoundExists index)
  let W := max (stages ⟨0, by decide⟩).widthBound
    (max (stages ⟨1, by decide⟩).widthBound
      (max (stages ⟨2, by decide⟩).widthBound (stages ⟨3, by decide⟩).widthBound))
  let D := max (stages ⟨0, by decide⟩).depthBound
    (max (stages ⟨1, by decide⟩).depthBound
      (max (stages ⟨2, by decide⟩).depthBound (stages ⟨3, by decide⟩).depthBound))
  have widthBound index : (stages index).widthBound ≤ W := by
    fin_cases index <;> simp [W]
  have depthBound index : (stages index).depthBound ≤ D := by
    fin_cases index <;> simp [D]
  constructor
  · exact compoundsBuilt
  · intro leftIndex rightIndex
    have builtL : input.certified.buildActualRuleMajorCompoundRule45Key? target
        (input.certified.molecularView descriptorMap target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center leftIndex) =
          some (compounds leftIndex) := by
      rw [molecularView_eq_generatedView input singleBonded acyclic target]
      exact compoundsBuilt leftIndex
    have builtR : input.certified.buildActualRuleMajorCompoundRule45Key? target
        (input.certified.molecularView descriptorMap target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center rightIndex) =
          some (compounds rightIndex) := by
      rw [molecularView_eq_generatedView input singleBonded acyclic target]
      exact compoundsBuilt rightIndex
    change input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (compounds leftIndex).prior (compounds rightIndex).prior = _
    exact actual_ruleMajor_compound_prior_compare descriptorMap
      (descriptorMap_tetrahedral input) target
      (ActualReaderPhysicalBranchInverse.topTarget_root input center)
      (ActualReaderPhysicalBranchInverse.topTarget_address input center)
      singleBonded acyclic (stages leftIndex) (stages rightIndex)
      (widthBound leftIndex) (depthBound leftIndex)
      (widthBound rightIndex) (depthBound rightIndex) builtL builtR

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_compound_prior_comparison
