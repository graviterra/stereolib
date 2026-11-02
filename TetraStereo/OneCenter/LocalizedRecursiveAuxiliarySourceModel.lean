import TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The source retained model

`SourceRetainedModel input singleBonded state` states the retained Rules-1–5 equations for an
arbitrary candidate state from the molecular input and the retained occurrence alone:

* non-real occurrences (terminal ring duplicates) and real non-centers carry `none`;
* at a real detected occurrence, for its source four-ligand frame (the reroot-child enumeration
  of the target cursor), `state target` is the retained outcome
  (`RetainedContextualOutcomeAt`) on the **source cuts** (`sourceCutGraphs`), with
  * auxiliary labels read from the candidate (`stateMap input state`),
  * the native structural window (`familyWidth`, `familyHeight` of those cuts),
  * the source coordinates (`sourceCoordinates`).

Its definition does not mention the generated reference state, the actual descriptor map, any
frame skeleton or compilation, stage build, sorted runtime key or compilation window. This is
checked by `assert_closure_excludes` over the full transitive closure, with negative controls on
the compiled cuts.

Connection (proofs may use the accepted compilation):

* `nativeWindow_iff_source`: equivalent to `NativeWindowRetainedModel` (hence to the accepted
  `IndependentRetainedModel`). Compiled cuts equal source cuts, compiled coordinates equal source
  coordinates, and the compiled frame is the source frame.
* `referenceState_sourceRetainedModel`, `sourceRetainedModel_unique`,
  `existsUnique_sourceRetainedModel`: the actual generated state is the unique model.
* `mem_analyze_iff_sourceRetainedModel`: the actual detected-center report, refusals
  included, reads any source model at the final occurrences.
* `sourceFrame_exists`, `sourceCutAdmissible_at_sourceFrame` (in
  `LocalizedRetainedSourceCutFrames`, with stage-free proof closures): the frame clause is never
  vacuous and the admissible branch is used at every slot.

Not claimed: physical completeness, chemical sufficiency of Rules 1–5 (e.g. the hidden-parity /
in–out cage), or a Rule-6 extension.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open LocalizedRecursiveAuxiliaryIndependentSemantics LocalizedRecursiveAuxiliarySourceWindows
open LocalizedRetainedSourceCutFrames
open scoped Classical

noncomputable section

variable {input : Input}

/-- **Source retained model.** The retained ordinary-rule equations of a candidate state, stated
from the molecular input, the retained occurrence and its source frame. -/
def SourceRetainedModel (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (state : Occurrence input → Option LocalizedAuxiliaryLabel) : Prop :=
  ∀ target : Occurrence input,
    (target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom → state target = none) ∧
    (∀ _real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom,
      ¬ IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit target.1).atom → state target = none) ∧
    (∀ (_real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
      (detected : IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit target.1).atom)
      (frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)),
      sourceFrame? target = some frame →
      let unit : DetectedOccurrence input.certified.moleculeGraph :=
        ⟨input.certified.molecularFrameUnit target.1, detected⟩
      let cuts := sourceCutGraphs singleBonded target frame
      RetainedContextualOutcomeAt input.certified.moleculeGraph (stateMap input state) unit
        cuts (familyWidth cuts) (familyHeight cuts) (sourceCoordinates frame) (state target))

/-- **The source model is the native-window model.** -/
theorem nativeWindow_iff_source (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (state : Occurrence input → Option LocalizedAuxiliaryLabel) :
    NativeWindowRetainedModel input singleBonded state ↔
      SourceRetainedModel input singleBonded state := by
  unfold NativeWindowRetainedModel SourceRetainedModel
  refine forall_congr' fun target => and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro native real detected frame computed
    have frameEq := frame_eq_of_sourceFrame (cyclicContextFrameCompilation input singleBonded
      target real ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl) computed
    subst frameEq
    have holds := native real detected
    dsimp only at holds ⊢
    rw [canonicalCutGraphs_eq_source, actualCoordinates_eq_sourceCoordinates] at holds
    exact holds
  · intro source real detected
    have holds := source real detected _ (cyclicContextFrameCompilation input singleBonded
      target real ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl).frameComputed
    dsimp only at holds ⊢
    rw [canonicalCutGraphs_eq_source, actualCoordinates_eq_sourceCoordinates]
    exact holds

theorem independentRetainedModel_iff_source
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (state : Occurrence input → Option LocalizedAuxiliaryLabel) :
    IndependentRetainedModel input singleBonded state ↔
      SourceRetainedModel input singleBonded state :=
  (independentRetainedModel_iff_nativeWindow singleBonded state).trans
    (nativeWindow_iff_source singleBonded state)

/-- The actual generated state is a source model. -/
theorem referenceState_sourceRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    SourceRetainedModel input singleBonded (referenceState input) :=
  (independentRetainedModel_iff_source singleBonded _).mp
    (referenceState_independentRetainedModel singleBonded)

/-- **Uniqueness of the source model.** -/
theorem sourceRetainedModel_unique
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {state : Occurrence input → Option LocalizedAuxiliaryLabel}
    (model : SourceRetainedModel input singleBonded state) :
    state = referenceState input :=
  independentRetainedModel_unique singleBonded
    ((independentRetainedModel_iff_source singleBonded state).mpr model)

theorem existsUnique_sourceRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    ∃! state : Occurrence input → Option LocalizedAuxiliaryLabel,
      SourceRetainedModel input singleBonded state :=
  ⟨referenceState input, referenceState_sourceRetainedModel singleBonded,
    fun _ model => sourceRetainedModel_unique singleBonded model⟩

/-- **The actual report reads the source model**, at every detected center, refusals included. -/
theorem mem_analyze_iff_sourceRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {state : Occurrence input → Option LocalizedAuxiliaryLabel}
    (model : SourceRetainedModel input singleBonded state)
    (atom : Nat) (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ analyze input ↔
      ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
        state (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
          outcome :=
  mem_analyze_iff_independentRetainedModel singleBonded
    ((independentRetainedModel_iff_source singleBonded state).mpr model) atom outcome

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel.nativeWindow_iff_source
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel.independentRetainedModel_iff_source
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel.referenceState_sourceRetainedModel
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel.sourceRetainedModel_unique
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel.existsUnique_sourceRetainedModel
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel.mem_analyze_iff_sourceRetainedModel

/-! ## Dependency-closure receipts -/

assert_closure_excludes TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceModel.SourceRetainedModel
  [TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.descriptorMap,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameSkeleton,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.cyclicContextFrameCompilation,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.contextOccurrenceView,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.contextOccurrenceRead,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalCutGraphs,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.actualCoordinates,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.runtimeSemantics,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceFacts,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyView,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyLabel,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorOccurrenceExecAt?,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45KeyExec?,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm]

/-- error: TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalCutGraphs depends on TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation -/
#guard_msgs in
assert_closure_excludes
  TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalCutGraphs
  [TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation]

/-- error: TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalCutGraphs depends on TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState -/
#guard_msgs in
assert_closure_excludes
  TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalCutGraphs
  [TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState]
