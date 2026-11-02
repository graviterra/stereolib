import TetraStereo.OneCenter.LocalizedRuleMajorReferencePipeline
import TetraStereo.OneCenter.LocalizedRuleMajorActualEvidenceRefinement
import TetraStereo.OneCenter.LocalizedRuleMajorReferenceSelection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The revised evaluator's own generated descriptor map and exact molecular reader.
No labels are transferred from the old evaluator. On a simple acyclic input every carrier
occurrence is real, actual units identify it uniquely, and noncandidates are refused by the
new descriptor callback itself. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open DeclarativeCIP CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree
noncomputable section
open scoped Classical

def descriptorMap (input : Input) : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph) :=
  fun unit => (actualReferenceOccurrenceOf input unit.1).bind fun occurrence =>
    (referenceState input occurrence).map localizedAuxiliaryDescriptor

theorem descriptorMap_tetrahedral (input : Input)
    (unit : DetectedOccurrence input.certified.moleculeGraph) (value : Descriptor)
    (observed : descriptorMap input unit = some value) : value.IsTetrahedral := by
  unfold descriptorMap at observed
  obtain ⟨occurrence, _, mapped⟩ := Option.bind_eq_some_iff.1 observed
  obtain ⟨label, _, rfl⟩ := Option.map_eq_some_iff.1 mapped
  cases label with
  | chiral rs => cases rs <;> trivial
  | pseudoasymmetric ps => cases ps <;> trivial

theorem descriptorMap_readback (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (unit : DetectedOccurrence input.certified.moleculeGraph) (occurrence : Occurrence input)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1) :
    (descriptorMap input unit).bind Descriptor.toLocalizedLabel = referenceState input occurrence := by
  have mapped := (actualReferenceOccurrenceOf_eq_some_iff input singleBonded acyclic unit.1 occurrence).2 unitEq
  unfold descriptorMap
  rw [mapped]
  exact option_map_localizedAuxiliaryDescriptor_bind _

theorem reference_none_of_noncandidate (input : Input) (target : Occurrence input)
    (noncandidate : ActualPhysicalNoncandidate input target) : referenceState input target = none := by
  obtain ⟨atom, current, notMem⟩ := noncandidate
  rw [← reference_fixed input target]
  exact input.certified.ruleMajorDescriptor?_eq_none_of_no_center target _
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
      target atom current notMem)

theorem molecularReader_eq_generatedReader
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1)) :
    input.certified.molecularReader (descriptorMap input) target =
      input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (referenceState input) target) := by
  funext cursor
  unfold CertifiedLocalizedCIPInput.molecularReader
  by_cases dependency : input.certified.LocalizedDepthDependency cursor.occurrence target
  · unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
    simp only [CertifiedLocalizedCIPInput.molecularView,
      CertifiedLocalizedCIPInput.localizedDependencyView]
    simp only [dif_pos dependency]
    by_cases hreal : cursor.occurrence.1.node.provenance = .realAtom
    · rw [if_pos hreal]
      by_cases hcenter : IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit cursor.occurrence.1).atom
      · rw [dif_pos hcenter]
        exact descriptorMap_readback input singleBonded acyclic
          ⟨input.certified.molecularFrameUnit cursor.occurrence.1, hcenter⟩
          cursor.occurrence rfl
      · rw [dif_neg hcenter]
        have hnone : referenceState input cursor.occurrence = none := by
          apply reference_none_of_noncandidate input cursor.occurrence
          obtain ⟨current, _path, observed, head, _provenance, _simple, _support,
            _penultimate⟩ :=
            input.certified.carrierOccurrence_realPath singleBonded acyclic cursor.occurrence
          have last : cursor.occurrence.1.node.history.getLast? =
              some cursor.occurrence.1.root :=
            input.certified.realPathNode_history_getLast
              (input.certified.carrierOccurrence_realPath singleBonded acyclic cursor.occurrence)
          have frameAtom : (input.certified.molecularFrameUnit cursor.occurrence.1).atom = current :=
            input.certified.molecularFrameUnit_atom_eq_current cursor.occurrence.1 head last
          refine ⟨current, observed, ?_⟩
          intro hmem
          have htet : input.certified.moleculeGraph.IsTetrahedralCenter current := by
            simpa [CertifiedLocalizedCIPInput.tetrahedralCenterSet] using hmem
          rw [MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card] at htet
          exact hcenter (by rw [frameAtom]; exact htet)
        exact hnone.symm
    · obtain ⟨_current, _path, _observed, _head, provenance, _simple, _support,
        _penultimate⟩ :=
        input.certified.carrierOccurrence_realPath singleBonded acyclic cursor.occurrence
      exact absurd provenance hreal
  · unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
    simp only [dif_neg dependency]

theorem molecularView_eq_generatedView (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) (target : Occurrence input) :
    input.certified.molecularView (descriptorMap input) target =
      input.certified.localizedDependencyView (referenceState input) target := by
  funext source dependency
  have observed := congrFun (molecularReader_eq_generatedReader input singleBonded acyclic target)
    (⟨source, none⟩ : input.certified.LocalizedRerootCursor (carrierFuel input))
  simpa only [molecularReader, localizedDependencyLabel, dif_pos dependency] using observed

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.descriptorMap_tetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.descriptorMap_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.reference_none_of_noncandidate
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.molecularReader_eq_generatedReader
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.molecularView_eq_generatedView
