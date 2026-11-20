import TetraStereo.OneCenter.LocalizedChemicalRingWitnessPhysicalExecution
import TetraStereo.OneCenter.LocalizedMarkedDetectedFrames
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The successful-label case of the ranked physical induction, with the executions,
frame and raw-history premises derived from the actual generated snapshot. The path-label
correspondence is the one delivered by the actual-key reconstruction; a successful label
and proper signs at the other residual centres remain explicit. This does not settle
missing labels, nor assert calibration for terminal-twin configurations. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingWitnessOrientation

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingWitnessExecution
open LocalizedChemicalRingWitnessLabelMatch LocalizedChemicalRingWitnessPhysicalExecution
open LocalizedChemicalRingRawResidualDescendants LocalizedChemicalRingResidualOrientationStep
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel rawStateReader)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (frameAtomsOf)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported single calibrated in
/-- One successful actual snapshot observation and its reconstructed optional match force
the current physical sign, assuming the physical induction hypothesis only at other centres
in the residual component. Both successful executions and the frame are conclusions. -/
theorem relativeSign_of_snapshot_match (root reference entry : input.Atom)
    (fixedRoot : (e : Equiv.Perm input.Atom) root = root)
    (fixedReference : (e : Equiv.Perm input.Atom) reference = reference)
    (path : List input.Atom) (valid : ResidualObsPath input.moleculeGraph [root] entry path)
    (d : input.detectedMultiCenterMolecule.Center) (terminal : pathTerminal path valid.nonempty = d.1)
    (depth : Nat) (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (matched : ((snapshot input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode root path)).map factLabel =
      ((snapshot input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode root (path.map (e : Equiv.Perm input.Atom)))).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshot input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode root path)).map factLabel = some label)
    (proper : ∀ c : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph ([root] ++ path.dropLast) d.1 c.1 → c.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg e c = 1) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  obtain ⟨original, pulled⟩ := snapshot_matched_pullback input mol agreement admissible supported
    single e root reference fixedRoot fixedReference path depth (inputGeometry input)
    source sourceReached matched label observed
  have reached := snapshot_path_reached root path LocalizedPhysicalMarkedDistantReference.rawStep?
    mol (sparseOperations input mol) depth (inputGeometry input) [] source sourceReached reference.val
    label observed
  obtain ⟨atomEq, outside, carried⟩ := witness_boundary input root entry path valid
  rw [terminal] at atomEq outside
  have frame := LocalizedMarkedDetectedFrames.detected_frame mol input agreement admissible
    supported single d (rawPathNode root path) reached rfl atomEq.symm
  exact relativeSign_eq_one_of_residual_signs input mol agreement admissible supported single cfg e
    calibrated ([root] ++ path.dropLast) (rawPathNode root path) d.1 atomEq outside carried reached
    proper (sparseOperations input mol) LocalizedPhysicalMarkedDistantReference.rawStep?
    (distantStep_congr_geom (mol := mol) (ops := sparseOperations input mol))
    (distantStep_flip mol (sparseOperations input mol)) d atomEq.symm _ frame
    (depth + source.history.length - (path.length + 1)) [] (some reference.val) label original pulled

include agreement admissible supported single calibrated in
/-- Direct consumer of the path-label correspondence produced by actual comparison keys.
No optional fact match, second observation, successful execution or frame is assumed. -/
theorem relativeSign_of_path_labels {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (rootAddress : target.1.address = [])
    (reference entry : input.Atom)
    (fixedRoot : (e : Equiv.Perm input.Atom) target.1.root = target.1.root)
    (fixedReference : (e : Equiv.Perm input.Atom) reference = reference)
    (path : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph [target.1.root] entry path)
    (d : input.detectedMultiCenterMolecule.Center) (terminal : pathTerminal path valid.nonempty = d.1)
    (depth : Nat) (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (matched : PathLabelsAgree treeL treeR
      (rawStateReader input (snapshot input mol depth (inputGeometry input) source reference.val) target)
      (rawStateReader input (snapshot input mol depth (inputGeometry input) source reference.val) target)
      [target.1.root] path (path.map (e : Equiv.Perm input.Atom)))
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshot input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode target.1.root path)).map factLabel = some label)
    (proper : ∀ c : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph ([target.1.root] ++ path.dropLast) d.1 c.1 → c.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg e c = 1) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have detected (c : input.detectedMultiCenterMolecule.Center) :
      IsDetectedCenter input.moleculeGraph c.1 :=
    (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card c.1).mp
      ((input.moleculeGraph.mem_tetrahedralCenterSet c.1).mp c.2)
  have nonempty : path.map (e : Equiv.Perm input.Atom) ≠ [] := by
    simpa using valid.nonempty
  have imageTerminal : pathTerminal (path.map (e : Equiv.Perm input.Atom)) nonempty =
      (e : Equiv.Perm input.Atom) d.1 := by
    simp only [pathTerminal, List.getLast_map]
    exact congrArg (e : Equiv.Perm input.Atom) terminal
  have facts := fact_labels_eq_of_pathLabelsAgree single
    (snapshot input mol depth (inputGeometry input) source reference.val) target rootAddress
    treeL treeR path (path.map (e : Equiv.Perm input.Atom)) valid.nonempty nonempty
    (by rw [terminal]; exact detected d)
    (by rw [imageTerminal]; exact detected (input.detectedMultiCenterMolecule.centerPerm e d)) matched
  exact relativeSign_of_snapshot_match input mol agreement admissible supported single cfg e
    calibrated target.1.root reference entry fixedRoot fixedReference path valid d terminal
    depth source sourceReached facts label observed proper

end TetraStereo.OneCenter.LocalizedChemicalRingWitnessOrientation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessOrientation.relativeSign_of_snapshot_match
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessOrientation.relativeSign_of_path_labels
