import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryIndependentSemantics
import TetraStereo.OneCenter.DeclarativeCIPRetainedWindowIndependence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Retained equations without compilation-selected windows

`IndependentRetainedModel` (accepted, frozen) states each occurrence's retained equation at the
window `frames.W, frames.D` of its frame compilation: sups of the generated stage graphs' widths and
heights. This module removes that numeric borrowing.

* `canonicalCutGraphs_windowCovers`: the compilation window **covers** each canonical cut graph.
  The cut is isomorphic to the actual stage-`a` graph (`CanonicalLigandCut.faithful`); width
  (node count) and height (maximal depth) are isomorphism invariants, and `frames.W/D` bound the
  stage graph (`a_width_le`, `a_depth_le`, `widthBound`, `depthBound`).
* `familyWidth` / `familyHeight`: the native window of a four-cut family, the maximum width and
  height of the cut graphs themselves. These are structural facts of the finite cut graphs.
* `NativeWindowRetainedModel`: the same equations at the native cut window.
  `independentRetainedModel_iff_nativeWindow` (by `retainedContextualOutcomeAt_window`) gives
  existence and uniqueness of its solution, the actual generated state.
* `referenceState_outcome_of_covering_window`: the generated state satisfies its retained
  equation at **every** window covering the canonical cuts.

Not removed: the canonical cuts and coordinates are still those named by the frame compilation's
cursors (`frames.frame.cursorAt`, `actualCoordinates`). This module does not prove those are
independent of alternate frame compilations. Chemical fidelity and physical completeness of the
retained equations are separate claims.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open LocalizedRecursiveAuxiliaryPhysicalDomain LocalizedRecursiveAuxiliaryIndependentSemantics
open scoped Classical

noncomputable section

/-! ## Width and height are isomorphism invariants -/

theorem width_eq_of_iso {Atom : Type*} {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) : left.width = right.width := by
  letI : Fintype left.Node := left.nodeFintype
  letI : Fintype right.Node := right.nodeFintype
  unfold RootedDigraph.width
  exact Fintype.card_congr iso.toEquiv

theorem height_le_of_iso {Atom : Type*} {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) : left.height ≤ right.height := by
  apply Finset.sup_le
  intro node _
  rw [iso.map_depth node]
  exact right.depth_le_height _

theorem windowCovers_of_iso {Atom : Type*} {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) {W D : ℕ} (cover : WindowCovers right W D) :
    WindowCovers left W D :=
  ⟨(width_eq_of_iso iso).le.trans cover.1, (height_le_of_iso iso).trans cover.2⟩

/-! ## Native windows of a cut family -/

/-- Maximum node count over four cut graphs. -/
def familyWidth {Atom : Type*} (graphs : Fin 4 → RootedDigraph Atom) : ℕ :=
  Finset.univ.sup fun slot => (graphs slot).width

/-- Maximum height over four cut graphs. -/
def familyHeight {Atom : Type*} (graphs : Fin 4 → RootedDigraph Atom) : ℕ :=
  Finset.univ.sup fun slot => (graphs slot).height

theorem familyWindow_covers {Atom : Type*} (graphs : Fin 4 → RootedDigraph Atom) (slot : Fin 4) :
    WindowCovers (graphs slot) (familyWidth graphs) (familyHeight graphs) :=
  ⟨Finset.le_sup (f := fun slot => (graphs slot).width) (Finset.mem_univ slot),
    Finset.le_sup (f := fun slot => (graphs slot).height) (Finset.mem_univ slot)⟩

/-! ## The compilation window covers the canonical cuts -/

/-- **Sufficiency of the compilation window for the canonical cuts.** -/
theorem canonicalCutGraphs_windowCovers {input : Input} {target : Occurrence input}
    {unit : DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation input target unit targetUnit)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (slot : Fin 4) :
    WindowCovers (frames.canonicalCutGraphs singleBonded slot) frames.W frames.D :=
  windowCovers_of_iso (Classical.choice (frames.canonicalLigandCut singleBonded slot).faithful)
    ⟨((frames.stages slot).a_width_le).trans (frames.widthBound slot),
      ((frames.stages slot).a_depth_le).trans (frames.depthBound slot)⟩

/-- The compiled and native windows give the same retained outcome on the canonical cuts. -/
theorem canonicalCut_outcome_native_iff {input : Input} {target : Occurrence input}
    {unit : DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation input target unit targetUnit)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (outcome : Option LocalizedAuxiliaryLabel) :
    RetainedContextualOutcomeAt input.certified.moleculeGraph descriptorMap unit
        (frames.canonicalCutGraphs singleBonded) frames.W frames.D frames.actualCoordinates
        outcome ↔
      RetainedContextualOutcomeAt input.certified.moleculeGraph descriptorMap unit
        (frames.canonicalCutGraphs singleBonded)
        (familyWidth (frames.canonicalCutGraphs singleBonded))
        (familyHeight (frames.canonicalCutGraphs singleBonded)) frames.actualCoordinates
        outcome :=
  retainedContextualOutcomeAt_window input.certified.moleculeGraph descriptorMap unit
    (frames.canonicalCutGraphs singleBonded) (canonicalCutGraphs_windowCovers frames singleBonded)
    (familyWindow_covers _) frames.actualCoordinates outcome

/-! ## The retained equations at native windows -/

variable {input : Input}

/-- `IndependentRetainedModel` with each equation at the native window of its own canonical cuts
instead of the compilation-selected window. -/
def NativeWindowRetainedModel (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (state : Occurrence input → Option LocalizedAuxiliaryLabel) : Prop :=
  ∀ target : Occurrence input,
    (target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom → state target = none) ∧
    (∀ _real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom,
      ¬ IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit target.1).atom → state target = none) ∧
    (∀ (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
      (detected : IsDetectedCenter input.certified.moleculeGraph
        (input.certified.molecularFrameUnit target.1).atom),
      let unit : DetectedOccurrence input.certified.moleculeGraph :=
        ⟨input.certified.molecularFrameUnit target.1, detected⟩
      let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
      let cuts := frames.canonicalCutGraphs singleBonded
      RetainedContextualOutcomeAt input.certified.moleculeGraph (stateMap input state) unit
        cuts (familyWidth cuts) (familyHeight cuts) frames.actualCoordinates (state target))

theorem independentRetainedModel_iff_nativeWindow
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (state : Occurrence input → Option LocalizedAuxiliaryLabel) :
    IndependentRetainedModel input singleBonded state ↔
      NativeWindowRetainedModel input singleBonded state := by
  unfold IndependentRetainedModel NativeWindowRetainedModel
  refine forall_congr' fun target => and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine forall_congr' fun real => forall_congr' fun detected => ?_
  exact canonicalCut_outcome_native_iff
    (cyclicContextFrameCompilation input singleBonded target real
      ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl)
    singleBonded (stateMap input state) (state target)

/-- The generated state is a native-window model. -/
theorem referenceState_nativeWindowRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    NativeWindowRetainedModel input singleBonded (referenceState input) :=
  (independentRetainedModel_iff_nativeWindow singleBonded _).mp
    (referenceState_independentRetainedModel singleBonded)

/-- **Uniqueness without compilation-selected windows.** -/
theorem nativeWindowRetainedModel_unique
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {state : Occurrence input → Option LocalizedAuxiliaryLabel}
    (model : NativeWindowRetainedModel input singleBonded state) :
    state = referenceState input :=
  independentRetainedModel_unique singleBonded
    ((independentRetainedModel_iff_nativeWindow singleBonded state).mpr model)

theorem existsUnique_nativeWindowRetainedModel
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    ∃! state : Occurrence input → Option LocalizedAuxiliaryLabel,
      NativeWindowRetainedModel input singleBonded state :=
  ⟨referenceState input, referenceState_nativeWindowRetainedModel singleBonded,
    fun _ model => nativeWindowRetainedModel_unique singleBonded model⟩

/-- **Every covering window.** At a real detected occurrence the generated state is the retained
outcome on its canonical cuts at any window bounding their widths and heights. -/
theorem referenceState_outcome_of_covering_window
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom)
    {W D : ℕ}
    (covers : ∀ slot, WindowCovers
      ((cyclicContextFrameCompilation input singleBonded target real
        ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl).canonicalCutGraphs
          singleBonded slot) W D) :
    RetainedContextualOutcomeAt input.certified.moleculeGraph
      (stateMap input (referenceState input))
      ⟨input.certified.molecularFrameUnit target.1, detected⟩
      ((cyclicContextFrameCompilation input singleBonded target real
        ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl).canonicalCutGraphs
          singleBonded) W D
      (cyclicContextFrameCompilation input singleBonded target real
        ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl).actualCoordinates
      (referenceState input target) :=
  (retainedContextualOutcomeAt_window _ _ _ _
    (canonicalCutGraphs_windowCovers _ singleBonded) covers _ _).mp
    ((referenceState_independentRetainedModel singleBonded target).2.2 real detected)

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows.width_eq_of_iso
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows.height_le_of_iso
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows.canonicalCutGraphs_windowCovers
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows.canonicalCut_outcome_native_iff
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows.independentRetainedModel_iff_nativeWindow
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows.nativeWindowRetainedModel_unique
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows.existsUnique_nativeWindowRetainedModel
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows.referenceState_outcome_of_covering_window
