import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
import TetraStereo.OneCenter.LocalizedRetainedContextAllOccurrences
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Physical setup at the evaluator's own cyclic final root

The physical domain of the general cyclic root theorem, and the actual data derived from it at
`localizedFinalOccurrenceExecutable`, the occurrence the final report reads for a detected
center.

**Physical input** (`CyclicRootPhysicalDomain`):
* a finite simple-bonded certified input of constant formal charge (rings allowed);
* one physical configuration of the automatically detected multi-center molecule;
* the general-rigid physical domain at the root: the physical graph is the certified graph, and
  every non-root center is a physical terminal twin or a calibrated general-rigid center;
* pairwise physical proper distinguishability of the four root ligand branches;
* physical root geometry: certified coordinates of the four root ligands in the physical ligand
  enumeration, nonzero oriented volume, and orientation equal to the physical configuration sign.

**Derived here** from the actual compiled final-root frame:
* its center, its slot-to-ligand alignment `detectedLigandPermutation` and the cursor atoms;
* the actual coordinates at every slot and their nonzero volume;
* the actual compound builds and the current generated view;
* the retained keys on the canonical predecessor cuts, which equal the keys on the actual stage
  graphs.

No acyclicity, immediate-`Z` separation, unique nearest reference, fixed depth, reference count,
supplied label, strictness, sort success or output is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup

open CertifiedLocalizedCIPInput
open LocalizedRuleMajorReference
open DeclarativeCIP
open RootedTetrahedralBranchSymmetry
open LocalizedCyclicMatchedReadingPhysicalTransport

noncomputable section

/-- **Physical root geometry.** The certified coordinates of the four root ligands, in the
physical molecule's own ligand enumeration, exist and are not coplanar, and their orientation is
the physical configuration sign at the root. This is physical input, not a runtime result. -/
def RootPhysicalGeometry (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (cfg : m.Configuration) (root : m.Center) : Prop :=
  ∃ pointAt : Fin 4 → CartesianPoint3,
    (∀ i, input.spatialPointAt? (m.ligandAtomAt root i) = some (pointAt i)) ∧
      CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0 ∧
      rationalVolumeSign
          (CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
        m.configurationSign cfg root

/-- **The physical domain of the general cyclic root theorem**, at one detected center of the
certified input and one physical configuration of the detected molecule. -/
structure CyclicRootPhysicalDomain (input : LocalizedRuleMajorReference.Input)
    (center : input.certified.TetrahedralCenter)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) : Prop where
  singleBonded : input.certified.moleculeGraph.SimpleBonded
  charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph
  domain : ActualGeneralRigidPhysicalDomain input.certified
    input.certified.detectedMultiCenterMolecule cfg center
  properDistinct : MultiCenterMolecule.PairwiseProperDistinguishable
    input.certified.detectedMultiCenterMolecule cfg center
  geometry : RootPhysicalGeometry input.certified
    input.certified.detectedMultiCenterMolecule cfg center

/-- The occurrence the final report reads for `center`: its own root, at the empty address. -/
abbrev finalTarget (input : LocalizedRuleMajorReference.Input)
    (center : input.certified.TetrahedralCenter) : Occurrence input :=
  input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center

theorem finalTarget_root (input : LocalizedRuleMajorReference.Input)
    (center : input.certified.TetrahedralCenter) :
    (finalTarget input center).1.root = center.1 :=
  input.certified.localizedFinalOccurrenceExecutable_root (carrierFuel input) center

theorem finalTarget_address (input : LocalizedRuleMajorReference.Input)
    (center : input.certified.TetrahedralCenter) :
    (finalTarget input center).1.address = [] :=
  input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center

theorem finalTarget_real (input : LocalizedRuleMajorReference.Input)
    (center : input.certified.TetrahedralCenter) :
    (finalTarget input center).1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real input center

section Frame

variable {input : LocalizedRuleMajorReference.Input}
  (singleBonded : input.certified.moleculeGraph.SimpleBonded)
  (center : input.certified.TetrahedralCenter)

/-- The compiled frame's center is the reported center. -/
theorem frames_center : (finalRootFrames input singleBonded center).center = center :=
  finalRootFrames_center input singleBonded center

/-- Each compiled slot is the detected ligand named by `detectedLigandPermutation`. -/
theorem frames_ligandAtom (slot : Fin 4) :
    (finalRootFrames input singleBonded center).actualLigandAtoms slot =
      input.certified.detectedMultiCenterMolecule.ligandAtomAt center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation slot) := by
  show input.certified.detectedMultiCenterMolecule.ligandAtomAt
      (finalRootFrames input singleBonded center).center
      ((finalRootFrames input singleBonded center).detectedLigandPermutation slot) = _
  rw [frames_center singleBonded center]

/-- Each compiled cursor's current atom is that detected ligand. -/
theorem frames_cursor_current (slot : Fin 4) :
    ((finalRootFrames input singleBonded center).frame.cursorAt slot).occurrence.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.ligandAtomAt center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation slot)) := by
  have current := (finalRootFrames input singleBonded center).ligandAt slot
  rw [frames_center singleBonded center] at current
  exact current

/-- Every compiled compound is the actual production compound build at its slot. -/
theorem frames_compoundBuilt (slot : Fin 4) :
    input.certified.buildActualRuleMajorCompoundRule45KeyExec? (finalTarget input center)
        (contextOccurrenceView input (finalTarget input center))
        (2 * (carrierFuel input + 1))
        ((finalRootFrames input singleBonded center).frame.cursorAt slot) =
      some ((finalRootFrames input singleBonded center).compounds slot) :=
  (finalRootFrames input singleBonded center).compoundBuilt slot

include singleBonded in
/-- The current generated view at the root is the dependency view of the generated states. -/
theorem finalTarget_generatedView :
    input.certified.molecularView (descriptorMap input) (finalTarget input center) =
      input.certified.localizedDependencyView (referenceState input) (finalTarget input center) :=
  molecularView_eq_generatedView_of_simpleBonded input singleBonded (finalTarget input center)

/-- The retained keys on the canonical predecessor cuts are the retained keys on the actual stage
graphs. -/
theorem canonicalCutKeys_eq_retainedKeys :
    retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
        (finalCenterUnit input center)
        ((finalRootFrames input singleBonded center).canonicalCutGraphs singleBonded)
        (finalRootFrames input singleBonded center).W
        (finalRootFrames input singleBonded center).D =
      (finalRootFrames input singleBonded center).retainedKeys :=
  retainedContextualFrameKeysAt_iso input.certified.moleculeGraph (descriptorMap input)
    (finalCenterUnit input center) (finalRootFrames input singleBonded center).actualArmGraphs
    ((finalRootFrames input singleBonded center).canonicalCutGraphs singleBonded)
    (fun slot => (Classical.choice
      ((finalRootFrames input singleBonded center).canonicalLigandCut singleBonded
        slot).faithful).symm)
    (finalRootFrames input singleBonded center).W (finalRootFrames input singleBonded center).D

/-- The physical root coordinates are the actual frame coordinates, slot by slot, and stay
non-coplanar in the frame enumeration. -/
theorem frames_coordinates
    {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
    (geometry : RootPhysicalGeometry input.certified
      input.certified.detectedMultiCenterMolecule cfg center) :
    ∃ pointAt : Fin 4 → CartesianPoint3,
      (∀ i, input.certified.spatialPointAt?
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt center i) = some (pointAt i)) ∧
      CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0 ∧
      rationalVolumeSign
          (CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
        input.certified.detectedMultiCenterMolecule.configurationSign cfg center ∧
      (∀ slot, (finalRootFrames input singleBonded center).actualCoordinates slot =
        some (pointAt ((finalRootFrames input singleBonded center).detectedLigandPermutation
          slot))) ∧
      CartesianPoint3.orientedVolume
          (pointAt ((finalRootFrames input singleBonded center).detectedLigandPermutation 0))
          (pointAt ((finalRootFrames input singleBonded center).detectedLigandPermutation 1))
          (pointAt ((finalRootFrames input singleBonded center).detectedLigandPermutation 2))
          (pointAt ((finalRootFrames input singleBonded center).detectedLigandPermutation 3)) ≠
        0 := by
  obtain ⟨pointAt, observed, nonzero, sign⟩ := geometry
  refine ⟨pointAt, observed, nonzero, sign, ?_,
    cartesianOrientedVolume_perm_ne_zero pointAt _ nonzero⟩
  intro slot
  show input.certified.spatialPointAt?
      ((finalRootFrames input singleBonded center).actualLigandAtoms slot) = _
  rw [frames_ligandAtom singleBonded center slot]
  exact observed _

/-- Physical proper distinguishability, read through the frame alignment. -/
theorem properDistinct_slots
    {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
    (properDistinct : MultiCenterMolecule.PairwiseProperDistinguishable
      input.certified.detectedMultiCenterMolecule cfg center) :
    ∀ i j : Fin 4, i ≠ j →
      ¬ ProperTransport input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input singleBonded center).detectedLigandPermutation j) :=
  fun i j distinct =>
    properDistinct ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
      ((finalRootFrames input singleBonded center).detectedLigandPermutation j) fun same =>
        distinct ((finalRootFrames input singleBonded center).detectedLigandPermutation.injective
          same)

end Frame

end

end TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.RootPhysicalGeometry
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.CyclicRootPhysicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.finalTarget
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.finalTarget_root
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.finalTarget_address
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.finalTarget_real
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.frames_center
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.frames_ligandAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.frames_cursor_current
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.frames_compoundBuilt
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.finalTarget_generatedView
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.canonicalCutKeys_eq_retainedKeys
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.frames_coordinates
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup.properDistinct_slots
