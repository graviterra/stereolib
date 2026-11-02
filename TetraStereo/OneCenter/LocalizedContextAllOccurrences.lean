import TetraStereo.OneCenter.LocalizedContextGeneratedDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! All occurrences of the generated acyclic single-bond state: detected centers satisfy the
independent retained-context descriptor judgment on every faithful ligand expansion; other
atoms receive no descriptor. This is a pointwise semantic model theorem for the specified
rule-major profile, not a claim about rings or physical graph-enantiomorphism completeness. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section

theorem referenceState_none_of_not_detected
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : Occurrence input)
    (notDetected : ¬ IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom) :
    referenceState input target = none := by
  apply reference_none_of_noncandidate input target
  obtain ⟨current, _path, observed, head, _provenance, _simple, _support, _penultimate⟩ :=
    input.certified.carrierOccurrence_realPath singleBonded acyclic target
  have last : target.1.node.history.getLast? = some target.1.root :=
    input.certified.realPathNode_history_getLast
      (input.certified.carrierOccurrence_realPath singleBonded acyclic target)
  have frameAtom : (input.certified.molecularFrameUnit target.1).atom = current :=
    input.certified.molecularFrameUnit_atom_eq_current target.1 head last
  refine ⟨current, observed, ?_⟩
  intro member
  have tetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter current := by
    simpa [CertifiedLocalizedCIPInput.tetrahedralCenterSet] using member
  rw [MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card] at tetrahedral
  exact notDetected (by rw [frameAtom]; exact tetrahedral)

namespace ContextFrameCompilation
variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

theorem referenceState_outcome_on_faithful
    (frames : ContextFrameCompilation input target unit targetUnit)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (other : Fin 4 → RootedDigraph input.certified.Atom)
    (faithful : ∀ slot, RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph
      unit.1.atom (frames.ligandAtoms slot) (other slot)) :
    ContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
      other frames.W frames.D frames.coordinates (referenceState input target) := by
  cases result : referenceState input target with
  | none =>
      exact (frames.referenceState_none_iff_no_faithfulJudgment singleBonded acyclic
        other faithful).mp result
  | some descriptor =>
      exact (frames.referenceState_some_iff_faithfulJudgment singleBonded acyclic
        other faithful descriptor).mp result

end ContextFrameCompilation

/-- Every carrier occurrence is accounted for. For a detected center, the actual four-arm
construction supplies a finite adequate layout and inhabited faithful expansions; every other
faithful expansion has the same independent outcome. No label correctness, comparison,
reference selection, strictness, sort success, or coordinate availability is a premise. -/
theorem all_auxiliary_occurrences_correct
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    ∀ target : Occurrence input,
      (¬ IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit target.1).atom →
        referenceState input target = none) ∧
      (∀ detected : IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit target.1).atom,
        let unit : DetectedOccurrence input.certified.moleculeGraph :=
          ⟨input.certified.molecularFrameUnit target.1, detected⟩
        let frames := generatedContextFrameCompilation input singleBonded acyclic target unit rfl
        (∀ slot, RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph
          unit.1.atom (frames.ligandAtoms slot) (frames.graphs slot)) ∧
        (∀ other : Fin 4 → RootedDigraph input.certified.Atom,
          (∀ slot, RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph
            unit.1.atom (frames.ligandAtoms slot) (other slot)) →
          ContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
            other frames.W frames.D frames.coordinates (referenceState input target))) := by
  intro target
  refine ⟨referenceState_none_of_not_detected input singleBonded acyclic target, ?_⟩
  intro detected
  let unit : DetectedOccurrence input.certified.moleculeGraph :=
    ⟨input.certified.molecularFrameUnit target.1, detected⟩
  let frames := generatedContextFrameCompilation input singleBonded acyclic target unit rfl
  exact ⟨frames.graphs_faithful singleBonded acyclic,
    frames.referenceState_outcome_on_faithful singleBonded acyclic⟩

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_none_of_not_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_outcome_on_faithful
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.all_auxiliary_occurrences_correct
