import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Spatial reflection of the prepared evaluator, retaining the incoming state and the
entire reference context. Each side still generates its own child facts. The reflection law
comes from exchanging the two calls of the descriptor constructor, not from an assumed
chemical covariance. It transfers optional fact matches on the mirrored snapshot back to
the original snapshot; physical properness remains a separate obligation. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingDescriptorSpatialMirror
open LocalizedChemicalRingReferenceConsensusReflection
open LocalizedChemicalRingReferenceConsensusCorrectionWitness (labels_of_mirror)
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedGenericMarkedRecalculation (Geometry mirror factOf flatMap_congr_mem)
open LocalizedChemicalRingOrientationInduction (mirror_mirror)

theorem descriptorWithPrepared_spatialMirror (step : PreparedStep) (mol : RawMolecule)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (sub : Geometry → OccurrenceAuxState → MarkContext → Node → OccurrenceAuxState) :
    descriptorWithPrepared step mol (mirror geom) state M node sub =
      (descriptorWithPrepared step mol geom state M node sub).map spatialMirror := by
  unfold descriptorWithPrepared
  rw [mirror_mirror]
  exact caseFromMirror_swapped _ _

theorem descriptorOfStep_spatialMirror (step : PreparedStep) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext)
    (node : Node) :
    descriptorOfStep step mol depth (mirror geom) state M node =
      (descriptorOfStep step mol depth geom state M node).map spatialMirror :=
  descriptorWithPrepared_spatialMirror step mol geom state M node _

theorem factsOfStep_mirror (step : PreparedStep) (mol : RawMolecule) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    factsOfStep step mol depth (mirror geom) state M node =
      (factsOfStep step mol depth geom state M node).map mirrorFact := by
  induction depth generalizing node with
  | zero => rfl
  | succ depth ih =>
      rw [factsOfStep_succ, factsOfStep_succ, descriptorOfStep_spatialMirror,
        List.map_append, List.map_flatMap]
      congr 1
      · cases descriptorOfStep step mol depth geom state M node with
        | none => rfl
        | some label => simp [factOf_spatialMirror]
      · exact flatMap_congr_mem _ _ _ fun child _ => ih child

theorem childrenUnder_mirror (step : PreparedStep) (mol : RawMolecule) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node) :
    childrenUnder mol (factsOfStep step mol depth) (mirror geom) state node M =
      (childrenUnder mol (factsOfStep step mol depth) geom state node M).map mirrorFact := by
  unfold childrenUnder
  rw [List.map_flatMap]
  exact flatMap_congr_mem _ _ _ fun child _ =>
    factsOfStep_mirror step mol depth geom state M child

theorem generated_mirror (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (node : Node) (references : List input.Atom) :
    generated input mol depth (mirror geom) node references =
      (generated input mol depth geom node references).map mirrorFact :=
  childrenUnder_mirror (rawStepPrepared? (jointOperations input mol)) mol depth geom []
    (references.map Fin.val) node

/-- Optional label equality in the actual reflected snapshot implies the same equality
in the actual original snapshot, including absent labels. -/
theorem generated_labels_of_mirror (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (node x y : Node) (references : List input.Atom)
    (same : ((generated input mol depth (mirror geom) node references).factAt? x).map factLabel =
      ((generated input mol depth (mirror geom) node references).factAt? y).map factLabel) :
    ((generated input mol depth geom node references).factAt? x).map factLabel =
      ((generated input mol depth geom node references).factAt? y).map factLabel := by
  rw [generated_mirror] at same
  exact labels_of_mirror _ x y same

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection.descriptorWithPrepared_spatialMirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection.descriptorOfStep_spatialMirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection.factsOfStep_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection.childrenUnder_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection.generated_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection.generated_labels_of_mirror
