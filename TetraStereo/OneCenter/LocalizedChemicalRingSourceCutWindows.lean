import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A common molecular window for every predecessor cut, at every rerooted parent.

The finite maxima use only the molecular retained carriers and their source cut graphs.
They do not use a compiled tree, candidate labels, chosen stereocenter, or comparison result.
Every admitted source cut is covered. Thus internal priorities can share this window without
assuming any bound from the evaluator, even when their parent is not a detected center.
These are observation bounds for the ordinary prior, not bounds for the joint marker layout.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows

open DeclarativeCIP DeclarativeCIP.RetainedOccurrenceCarrier
open LocalizedRetainedSourceCutFrames

noncomputable section
open scoped Classical
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)

/-- Common bounds over every pair of valid carrier nodes at a fixed molecular root. -/
def rootCutWidth (root : Atom) : Nat :=
  letI : Fintype (Nodes molecule root) := (retainedCarrier molecule root).nodeFintype
  Finset.univ.sup fun pair : Nodes molecule root × Nodes molecule root =>
    (sourceCutArm molecule root pair.1.1 pair.2.1).width

def rootCutDepth (root : Atom) : Nat :=
  letI : Fintype (Nodes molecule root) := (retainedCarrier molecule root).nodeFintype
  Finset.univ.sup fun pair : Nodes molecule root × Nodes molecule root =>
    (sourceCutArm molecule root pair.1.1 pair.2.1).height

/-- One source-only window for the entire finite molecular input. -/
def allCutWidth : Nat := Finset.univ.sup (rootCutWidth molecule)

def allCutDepth : Nat := Finset.univ.sup (rootCutDepth molecule)

theorem rootCutWindow_covers (root : Atom) (focus incoming : Nodes molecule root) :
    WindowCovers (sourceCutArm molecule root focus.1 incoming.1)
      (rootCutWidth molecule root) (rootCutDepth molecule root) := by
  letI : Fintype (Nodes molecule root) := (retainedCarrier molecule root).nodeFintype
  exact ⟨Finset.le_sup (f := fun pair : Nodes molecule root × Nodes molecule root =>
      (sourceCutArm molecule root pair.1.1 pair.2.1).width) (Finset.mem_univ (focus, incoming)),
    Finset.le_sup (f := fun pair : Nodes molecule root × Nodes molecule root =>
      (sourceCutArm molecule root pair.1.1 pair.2.1).height) (Finset.mem_univ (focus, incoming))⟩

/-- The global source window covers every admitted cut, including ring-terminal cuts. -/
theorem allCutWindow_covers (root : Atom) (focus incoming : CarrierNode Atom)
    (admitted : SourceCutAdmissible molecule root focus incoming) :
    WindowCovers (sourceCutArm molecule root focus incoming)
      (allCutWidth molecule) (allCutDepth molecule) := by
  obtain ⟨validFocus, validIncoming, _⟩ := admitted
  have localCover := rootCutWindow_covers molecule root
    ⟨focus, validFocus⟩ ⟨incoming, validIncoming⟩
  exact ⟨localCover.1.trans (Finset.le_sup (Finset.mem_univ root)),
    localCover.2.trans (Finset.le_sup (Finset.mem_univ root))⟩

/-- Any two admitted source cuts can be compared at the same molecular window.
The parent occurrence is arbitrary and need not be a stereocenter. -/
theorem prior_orderAgrees_allCutWindow
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule)) (unit : OccurrenceUnit Atom)
    (leftRoot rightRoot : Atom) (leftFocus leftIncoming rightFocus rightIncoming : CarrierNode Atom)
    (leftAdmitted : SourceCutAdmissible molecule leftRoot leftFocus leftIncoming)
    (rightAdmitted : SourceCutAdmissible molecule rightRoot rightFocus rightIncoming)
    {W D : Nat}
    (leftCover : WindowCovers (sourceCutArm molecule leftRoot leftFocus leftIncoming) W D)
    (rightCover : WindowCovers (sourceCutArm molecule rightRoot rightFocus rightIncoming) W D) :
    OrderAgrees
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
        (sourceCutArm molecule leftRoot leftFocus leftIncoming) W D)
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
        (sourceCutArm molecule rightRoot rightFocus rightIncoming) W D)
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
        (sourceCutArm molecule leftRoot leftFocus leftIncoming)
        (allCutWidth molecule) (allCutDepth molecule))
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
        (sourceCutArm molecule rightRoot rightFocus rightIncoming)
        (allCutWidth molecule) (allCutDepth molecule)) :=
  (LocalizedChemicalRingAnyParentWindowIndependence.retainedCompleteLigandRule5KeyAt_orderAgrees_window
    molecule descriptorMap unit leftCover
    (allCutWindow_covers molecule leftRoot leftFocus leftIncoming leftAdmitted)
    rightCover (allCutWindow_covers molecule rightRoot rightFocus rightIncoming rightAdmitted)).1

end
end TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows.rootCutWindow_covers
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows.allCutWindow_covers
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows.prior_orderAgrees_allCutWindow

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows.allCutWidth
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?]
assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows.allCutDepth
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?]
