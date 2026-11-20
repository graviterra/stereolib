import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation
import TetraStereo.OneCenter.LocalizedChemicalRingDescriptorSpatialMirror
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Covered-path orientation decoding also holds for the actual reflected geometry.
Reflection of the mirror-paired descriptor is an involution, so equal successful
reflected executions give equal successful original executions. The accepted physical
decoder then applies with the original coordinate calibration and configuration.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorOrientation

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingCoveredPathOrientation LocalizedChemicalRingDescriptorSpatialMirror
open LocalizedChemicalRingBoundaryWitnessOrientation LocalizedChemicalRingBoundaryWitnessExecution
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingWitnessExecution LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationReadback (StepFlip)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedOperationEvaluator (Operations)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? mirror)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

private theorem unmirror_some (step : Step) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : descriptorWith step mol ops depth (mirror geom) state ctx node = some label) :
    descriptorWith step mol ops depth geom state ctx node = some (spatialMirror label) := by
  rw [descriptorWith_spatialMirror] at observed
  have mapped := congrArg (Option.map spatialMirror) observed
  have cancel (x : Option LocalizedTetrahedralRSPseudoDescriptor) :
      (x.map spatialMirror).map spatialMirror = x := by
    cases x with
    | none => rfl
    | some value => exact congrArg some (spatialMirror_involutive value)
  rw [cancel, Option.map_some] at mapped
  exact mapped

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement admissible supported single in
theorem relativeSign_of_covered_mirror_executions
    (d : input.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (imageCalibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg
      (input.detectedMultiCenterMolecule.centerPerm e d))
    (node : RawMolecule.CanonicalBranchNode) (atomEq : node.atom = d.1.val)
    (reached : Reached mol node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (covered : ∀ c : input.detectedMultiCenterMolecule.Center, c.1.val ∈ node.history)
    (ops : Operations) (step : Step) (stepCongr : StepCongr step mol ops)
    (stepFlip : StepFlip mol ops step) (depth : Nat) (state : OccurrenceAuxState) (ctx : Option Nat)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (original : descriptorWith step mol ops depth (mirror (inputGeometry input)) state ctx node = some label)
    (pulled : descriptorWith step mol ops depth
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (mirror (inputGeometry input)))
      state ctx node = some label) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have original' := unmirror_some step mol ops depth (inputGeometry input) state ctx node label original
  rw [← mirror_pullback] at pulled
  have pulled' := unmirror_some step mol ops depth _ state ctx node label pulled
  exact relativeSign_of_covered_executions input mol agreement admissible supported single cfg e d
    calibrated imageCalibrated node atomEq reached atoms frame covered ops step stepCongr stepFlip
    depth state ctx (spatialMirror label) original' pulled'

include agreement admissible supported single in
/-- Actual matches in the reflected snapshot force the same proper physical sign.
No reflected descriptor label or reflected coordinate calibration is supplied. -/
theorem relativeSign_of_covered_mirror_snapshot (step : Step)
    (stepMap : StepMap step mol (sparseOperations input mol)
      (relabelOf input (e : Equiv.Perm input.Atom)))
    (stepCongr : StepCongr step mol (sparseOperations input mol))
    (stepFlip : StepFlip mol (sparseOperations input mol) step)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (reference entry : input.Atom)
    (fixedBoundary : ∀ atom ∈ target.1.node.history.reverse, (e : Equiv.Perm input.Atom) atom = atom)
    (fixedReference : (e : Equiv.Perm input.Atom) reference = reference)
    (path : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph target.1.node.history.reverse entry path)
    (d : input.detectedMultiCenterMolecule.Center) (terminal : pathTerminal path valid.nonempty = d.1)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (imageCalibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg
      (input.detectedMultiCenterMolecule.centerPerm e d))
    (covered : ∀ c : input.detectedMultiCenterMolecule.Center,
      c.1.val ∈ (rawPathNode target.1.root (boundaryPath target path)).history)
    (depth : Nat) (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (matched : ((snapshotWith step input mol depth (mirror (inputGeometry input)) source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel =
      ((snapshotWith step input mol depth (mirror (inputGeometry input)) source reference.val).factAt?
        (rawPathNode target.1.root
          (boundaryPath target (path.map (e : Equiv.Perm input.Atom))))).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshotWith step input mol depth (mirror (inputGeometry input)) source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel = some label) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  obtain ⟨original, pulled⟩ := snapshot_boundary_matched_pullback input mol agreement admissible
    supported single e step stepMap target reference fixedBoundary fixedReference path depth
    (mirror (inputGeometry input)) source sourceReached matched label observed
  have reached := snapshot_path_reached target.1.root (boundaryPath target path) step
    mol (sparseOperations input mol) depth (mirror (inputGeometry input)) [] source sourceReached
    reference.val label observed
  have atomEq := (witness_boundary input single target entry path valid).1
  rw [terminal] at atomEq
  have frame := LocalizedMarkedDetectedFrames.detected_frame mol input agreement admissible
    supported single d _ reached rfl atomEq.symm
  exact relativeSign_of_covered_mirror_executions input mol agreement admissible supported single cfg e d
    calibrated imageCalibrated _ atomEq.symm reached _ frame covered _ step stepCongr stepFlip
    _ [] (some reference.val) label original pulled

end TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorOrientation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorOrientation.relativeSign_of_covered_mirror_executions
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorOrientation.relativeSign_of_covered_mirror_snapshot
