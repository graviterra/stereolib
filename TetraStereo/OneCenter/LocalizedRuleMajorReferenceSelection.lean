import TetraStereo.OneCenter.LocalizedRuleMajorCompoundBuilder
import TetraStereo.OneCenter.LocalizedActualReferenceSelectionBridge
import TetraStereo.OneCenter.LocalizedActualArmReadback
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Connect the Rule-4a key retained by the actual rule-major compound builder to the independent
P-92 reference selection, for arbitrary tetrahedral descriptor maps on finite acyclic
single-bond inputs. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

theorem buildRuleMajorCompoundRule45KeyWith?_references_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor = some compound)
    (rule4aKey : input.LocalizedRerootCumulativeRule45Key)
    (rule4aBuilt : compileStage .rule4a cursor = some rule4aKey) :
    compound.prior.references =
      localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels := by
  unfold buildRuleMajorCompoundRule45KeyWith? at built
  simp only [Option.bind_eq_bind, rule4aBuilt, Option.bind_some] at built
  obtain ⟨readings, hreadings, tail⟩ := Option.bind_eq_some_iff.mp built
  obtain ⟨rule5Readings, hrule5, result⟩ := Option.bind_eq_some_iff.mp tail
  cases Option.some.inj result
  rfl

end CertifiedLocalizedCIPInput

namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP

noncomputable section
open scoped Classical

/-- Build the ordinary Rule-4a readback from whole-tree observation and an arbitrary tetrahedral
descriptor-map premise. -/
theorem armReadback_of_treeLike_of_tetrahedralMap
    (input : LocalizedUniversalReference.Input)
    {center : input.certified.TetrahedralCenter} {index : Fin 4}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (arm : input.certified.OriginalRootArm center index .rule4a
      (input.certified.molecularReader descriptorMap target)) :
    ArmReadback arm descriptorMap (input.certified.topUnit center) := by
  have readback := molecularReader_arm_observations descriptorMap target arm
    targetRoot targetAddress singleBonded acyclic
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro node actual lookup
    obtain ⟨actual', lookup', label, _⟩ := readback node
    rw [decoratedSubtreeAt?_eq_subtreeAt?] at lookup
    cases Option.some.inj (lookup.symm.trans lookup')
    exact label
  · intro node
    exact occurrenceReading_tetrahedral_of_map _ _ _ _ tetrahedralMap node
  · intro node
    obtain ⟨_, _, _, available⟩ := readback node
    exact available
  · exact rule4aOnly_rankEvidence_of_simpleBonded singleBonded _ _ _

/-- For an arbitrary tetrahedral descriptor map, the original Rule-4a arm's selected references
are exactly the independent molecular reference selection. No rigidity or nearest-reference-count
premise is used. -/
theorem originalArm_references_eq_referenceSelection_of_treeLike
    (input : LocalizedUniversalReference.Input)
    {center : input.certified.TetrahedralCenter} {index : Fin 4}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (arm : input.certified.OriginalRootArm center index .rule4a
      (input.certified.molecularReader descriptorMap target)) :
    localizedRule4bReferencesFromRankedLabels arm.key.rankedLabels =
      toReferenceList (referenceSelection input.certified.moleculeGraph descriptorMap
        (input.certified.topUnit center) (armGraph arm)) :=
  arm_references_eq_referenceSelection descriptorMap target arm
    (input.certified.topUnit center)
    (armReadback_of_treeLike_of_tetrahedralMap input descriptorMap tetrahedralMap target
      targetRoot targetAddress singleBonded acyclic arm)

/-- The compound builder's retained Rule-4a selection equals the independent P-92 selection for
an arbitrary tetrahedral descriptor map on a finite acyclic single-bond input. Compound success
is derived at the actual carrier bound; the original Rule-4a arm is chosen at the same cursor and
its key is identified with the compound's Rule-4a key. -/
theorem actualRuleMajorCompound_references_eq_referenceSelection
    (input : LocalizedUniversalReference.Input)
    {center : input.certified.TetrahedralCenter} {index : Fin 4}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    ∃ (arm : input.certified.OriginalRootArm center index .rule4a
        (input.certified.molecularReader descriptorMap target))
      (compound : input.certified.LocalizedRerootCompoundRule45Key),
      input.certified.buildActualRuleMajorCompoundRule45Key?
          target (input.certified.molecularView descriptorMap target)
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center index) = some compound ∧
        compound.prior.references =
          toReferenceList (referenceSelection input.certified.moleculeGraph descriptorMap
            (input.certified.topUnit center) (armGraph arm)) := by
  let cursor := input.certified.localizedLigandRootCursor center index
  let read := input.certified.molecularReader descriptorMap target
  have incoming :=
    input.certified.localizedLigandRootCursor_incoming center index
  have valid : input.certified.LocalizedRerootCursorValid cursor :=
    input.certified.localizedRerootCursorValid_of_incoming cursor incoming
  let arm := Classical.choice (input.certified.exists_originalRootArm center index .rule4a read)
  obtain ⟨compound, compoundBuilt⟩ :=
    input.certified.exists_buildActualRuleMajorCompoundRule45Key_at_twice
      target (input.certified.molecularView descriptorMap target) cursor valid
  have readerEq : read = fun position =>
      input.certified.localizedDependencyLabel target
        (input.certified.molecularView descriptorMap target) position := by
    funext position
    rfl
  have rule4aBuilt :
      (input.certified.ruleMajorCompoundStageCompiler target
        (input.certified.molecularView descriptorMap target) read
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)))
          .rule4a cursor = some arm.key := by
    dsimp [CertifiedLocalizedCIPInput.ruleMajorCompoundStageCompiler, cursor, arm]
    calc
      input.certified.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target (input.certified.molecularView descriptorMap target)
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor =
        input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a (fun position => input.certified.localizedDependencyLabel target
            (input.certified.molecularView descriptorMap target) position)
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor :=
        (input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
          .rule4a target (input.certified.molecularView descriptorMap target)
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor).symm
      _ = input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a read (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor := by
        rw [readerEq]
      _ = some arm.key := arm.built
  have references :=
    CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyWith?_references_eq
      input.certified
      (input.certified.ruleMajorCompoundStageCompiler target
        (input.certified.molecularView descriptorMap target) read
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)))
      cursor (by
        change input.certified.buildRuleMajorCompoundRule45KeyWith?
          (input.certified.ruleMajorCompoundStageCompiler target
            (input.certified.molecularView descriptorMap target) read
            (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))) cursor =
          some compound
        simpa [CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45Key?,
          CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45Key?] using compoundBuilt)
      arm.key rule4aBuilt
  have selected := originalArm_references_eq_referenceSelection_of_treeLike
    input descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic arm
  refine ⟨arm, compound, compoundBuilt, ?_⟩
  rw [references]
  exact selected

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyWith?_references_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.armReadback_of_treeLike_of_tetrahedralMap
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.originalArm_references_eq_referenceSelection_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actualRuleMajorCompound_references_eq_referenceSelection
