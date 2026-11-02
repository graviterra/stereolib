import TetraStereo.OneCenter.LocalizedRuleMajorGeneratedPriorOrder
import TetraStereo.OneCenter.LocalizedRuleMajorFullComparison
import TetraStereo.OneCenter.LocalizedRuleMajorOwnMolecularEvidence
import TetraStereo.OneCenter.LocalizedRuleMajorBranchStages
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The revised evaluator's generated own-state supplies all four successful compounds and
independent complete Rule-5 keys at one shared layout. Its actual pairwise ordering and
reference-sensitivity flag are then characterized from those independent keys and reading lists.
This package does not identify reference-sensitivity with physical enantiomorphism. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
noncomputable section
open scoped Classical

def generatedTarget (input : Input) (center : input.certified.TetrahedralCenter) :=
  ActualReaderPhysicalBranchInverse.topTarget input center

def generatedDescriptorMap (input : Input) :
    DescriptorMap (DetectedOccurrence input.certified.moleculeGraph) :=
  descriptorMap input

/-- Generated data for all four ligand arms at a common complete-reading layout. The target and
descriptor map are fixed by the input; successful branch stages and actual compounds are derived
inside the package, so its conclusions do not depend on caller-supplied keys or build premises. -/
structure GeneratedRuleMajorFullComparisonData (input : Input)
    (center : input.certified.TetrahedralCenter) where
  stages : ∀ index : Fin 4,
    input.certified.RuleMajorBranchStages center index
      (generatedDescriptorMap input) (generatedTarget input center)
  compounds : Fin 4 → input.certified.LocalizedRerootCompoundRule45Key
  W : Nat
  D : Nat
  widthBound : ∀ index : Fin 4, (stages index).widthBound ≤ W
  depthBound : ∀ index : Fin 4, (stages index).depthBound ≤ D
  built : ∀ index : Fin 4,
    input.certified.buildActualRuleMajorCompoundRule45Key? (generatedTarget input center)
      (input.certified.localizedDependencyView (referenceState input)
        (generatedTarget input center))
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center index) = some (compounds index)
  execBuilt : ∀ index : Fin 4,
    input.certified.buildActualRuleMajorCompoundRule45KeyExec? (generatedTarget input center)
      (input.certified.localizedDependencyView (referenceState input)
        (generatedTarget input center))
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center index) = some (compounds index)
  actualOrdering : ∀ left right : Fin 4,
    (input.certified.compareLocalizedRerootCompoundThroughRule5
      (compounds left) (compounds right)).ordering =
      compare
        (completeLigandRule5KeyAt input.certified.moleculeGraph (generatedDescriptorMap input)
          (input.certified.topUnit center) (stages left).graph W D)
        (completeLigandRule5KeyAt input.certified.moleculeGraph (generatedDescriptorMap input)
          (input.certified.topUnit center) (stages right).graph W D)
  pseudoFlag : ∀ left right : Fin 4,
    (input.certified.compareLocalizedRerootCompoundThroughRule5
      (compounds left) (compounds right)).pseudo = true ↔
      ReferenceSensitiveRule5PairAt input.certified.moleculeGraph (generatedDescriptorMap input)
        (input.certified.topUnit center) (stages left).graph (stages right).graph W D

namespace GeneratedRuleMajorFullComparisonData

variable {input : Input} {center : input.certified.TetrahedralCenter}
  (data : GeneratedRuleMajorFullComparisonData input center)

/-- The independent complete Rules 1–5 key for each generated ligand arm. -/
def fullKey : Fin 4 → CompleteLigandRule5Key := fun index =>
  completeLigandRule5KeyAt input.certified.moleculeGraph (generatedDescriptorMap input)
    (input.certified.topUnit center) (data.stages index).graph data.W data.D

/-- Numeric priority is the number of generated ligand keys that are strictly smaller. -/
def rank (index : Fin 4) : Nat := keyRank data.fullKey index

theorem rank_eq_count (index : Fin 4) :
    data.rank index = (Finset.univ.filter fun other => data.fullKey other < data.fullKey index).card :=
  rfl

theorem rank_lt_iff_fullKey_lt (left right : Fin 4) :
    data.rank left < data.rank right ↔ data.fullKey left < data.fullKey right :=
  Rule4aTableBridge.keyRank_lt_iff_without_injectivity data.fullKey left right

theorem rank_eq_iff_fullKey_eq (left right : Fin 4) :
    data.rank left = data.rank right ↔ data.fullKey left = data.fullKey right :=
  Rule4aTableBridge.keyRank_eq_iff_without_injectivity data.fullKey left right

theorem actualOrdering_eq_rankCompare (left right : Fin 4) :
    (input.certified.compareLocalizedRerootCompoundThroughRule5
      (data.compounds left) (data.compounds right)).ordering =
      compare (data.rank left) (data.rank right) := by
  have strict :
      (input.certified.compareLocalizedRerootCompoundThroughRule5
        (data.compounds left) (data.compounds right)).ordering = .lt ↔
        data.rank left < data.rank right := by
    rw [data.actualOrdering left right, completeLigandRule5Key_compare_lt_iff]
    exact (data.rank_lt_iff_fullKey_lt left right).symm
  have tie :
      (input.certified.compareLocalizedRerootCompoundThroughRule5
        (data.compounds left) (data.compounds right)).ordering = .eq ↔
        data.rank left = data.rank right := by
    rw [data.actualOrdering left right, completeLigandRule5Key_compare_eq_iff]
    exact (data.rank_eq_iff_fullKey_eq left right).symm
  exact Rule4aTableBridge.eq_compare_of_iff _ _ _ strict tie

theorem actualOrdering_lt_iff_fullKey_lt (left right : Fin 4) :
    (input.certified.compareLocalizedRerootCompoundThroughRule5
      (data.compounds left) (data.compounds right)).ordering = .lt ↔
      data.fullKey left < data.fullKey right := by
  rw [data.actualOrdering left right, completeLigandRule5Key_compare_lt_iff]
  rfl

theorem actualOrdering_eq_iff_fullKey_eq (left right : Fin 4) :
    (input.certified.compareLocalizedRerootCompoundThroughRule5
      (data.compounds left) (data.compounds right)).ordering = .eq ↔
      data.fullKey left = data.fullKey right := by
  rw [data.actualOrdering left right, completeLigandRule5Key_compare_eq_iff]
  rfl

end GeneratedRuleMajorFullComparisonData

/-- Construct every stage, compound, shared layout bound, and comparison result from only the
certified input, its actual tetrahedral center, simple-bondedness, and acyclicity. -/
theorem generated_full_comparison (input : Input)
    (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    Nonempty (GeneratedRuleMajorFullComparisonData input center) := by
  let target := generatedTarget input center
  let descriptorMap := generatedDescriptorMap input
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
  have widthBound (index : Fin 4) : (stages index).widthBound ≤ W := by
    fin_cases index <;> simp [W]
  have depthBound (index : Fin 4) : (stages index).depthBound ≤ D := by
    fin_cases index <;> simp [D]
  have built (index : Fin 4) : input.certified.buildActualRuleMajorCompoundRule45Key? target
      (input.certified.localizedDependencyView (referenceState input) target)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center index) = some (compounds index) :=
    compoundsBuilt index
  have execBuilt (index : Fin 4) :
      input.certified.buildActualRuleMajorCompoundRule45KeyExec? target
        (input.certified.localizedDependencyView (referenceState input) target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center index) = some (compounds index) := by
    rw [input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact compoundsBuilt index
  have builtAtMolecularView (index : Fin 4) :
      input.certified.buildActualRuleMajorCompoundRule45Key? target
        (input.certified.molecularView descriptorMap target)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
        (input.certified.localizedLigandRootCursor center index) = some (compounds index) := by
    change input.certified.buildActualRuleMajorCompoundRule45Key? target
      (input.certified.molecularView
        (LocalizedRuleMajorReference.descriptorMap input) target)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center index) = some (compounds index)
    rw [molecularView_eq_generatedView input singleBonded acyclic target]
    exact built index
  have actualOrdering (left right : Fin 4) :
      (input.certified.compareLocalizedRerootCompoundThroughRule5
        (compounds left) (compounds right)).ordering =
        compare
          (completeLigandRule5KeyAt input.certified.moleculeGraph descriptorMap
            (input.certified.topUnit center) (stages left).graph W D)
          (completeLigandRule5KeyAt input.certified.moleculeGraph descriptorMap
            (input.certified.topUnit center) (stages right).graph W D) := by
    exact Rule4aTableBridge.actual_ruleMajor_full_ordering descriptorMap
      (descriptorMap_tetrahedral input) target
      (ActualReaderPhysicalBranchInverse.topTarget_root input center)
      (ActualReaderPhysicalBranchInverse.topTarget_address input center)
      singleBonded acyclic (stages left) (stages right)
      (widthBound left) (depthBound left) (widthBound right) (depthBound right)
      (builtAtMolecularView left) (builtAtMolecularView right)
  have pseudoFlag (left right : Fin 4) :
      (input.certified.compareLocalizedRerootCompoundThroughRule5
        (compounds left) (compounds right)).pseudo = true ↔
        ReferenceSensitiveRule5PairAt input.certified.moleculeGraph descriptorMap
          (input.certified.topUnit center) (stages left).graph (stages right).graph W D := by
    exact Rule4aTableBridge.actual_ruleMajor_pseudo_iff_referenceSensitive descriptorMap
      (descriptorMap_tetrahedral input) target
      (ActualReaderPhysicalBranchInverse.topTarget_root input center)
      (ActualReaderPhysicalBranchInverse.topTarget_address input center)
      singleBonded acyclic (stages left) (stages right)
      (widthBound left) (depthBound left) (widthBound right) (depthBound right)
      (builtAtMolecularView left) (builtAtMolecularView right)
  exact ⟨{
    stages := stages
    compounds := compounds
    W := W
    D := D
    widthBound := widthBound
    depthBound := depthBound
    built := built
    execBuilt := execBuilt
    actualOrdering := actualOrdering
    pseudoFlag := pseudoFlag }⟩

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.generatedTarget
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.generatedDescriptorMap
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.fullKey
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.rank
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.rank_eq_count
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.actualOrdering_eq_rankCompare
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.actualOrdering_lt_iff_fullKey_lt
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.actualOrdering_eq_iff_fullKey_eq
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.rank_lt_iff_fullKey_lt
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.rank_eq_iff_fullKey_eq
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_full_comparison
