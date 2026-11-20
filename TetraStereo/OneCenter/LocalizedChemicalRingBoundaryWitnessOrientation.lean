import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution
import TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep
import TetraStereo.OneCenter.LocalizedMarkedDetectedFrames
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
The successful-label orientation step at an arbitrary actual comparison target. The raw
query retains the entire original history: it is not replaced by a newly rooted query.
Actual optional label matches supply both executions; the residual physical induction
hypothesis supplies the required descendant agreement. The step is generic, so the same
proof applies to the isolated inherited-reference fallback with its proved contracts.

A successful observed label and proper signs at the other residual centres remain explicit.
This module does not infer properness from an absent label or settle the refusal case.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingBoundaryWitnessExecution
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingWitnessExecution
open LocalizedChemicalRingWitnessLabelMatch LocalizedChemicalRingRawResidualDescendants
open LocalizedChemicalRingResidualOrientationStep LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationReadback
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel rawStateReader)
open LocalizedMarkedReachableConfigurations (Reached)
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

include single in
/-- Every deleted boundary atom is already carried in the actual full query history, and
the terminal atom lies outside that boundary. These are consequences of the residual path. -/
theorem witness_boundary {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (entry : input.Atom)
    (path : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph target.1.node.history.reverse entry path) :
    (pathTerminal path valid.nonempty).val =
        (rawPathNode target.1.root (boundaryPath target path)).atom ∧
      pathTerminal path valid.nonempty ∉ target.1.node.history.reverse ++ path.dropLast ∧
      (∀ atom ∈ target.1.node.history.reverse ++ path.dropLast,
        atom.val ∈ (rawPathNode target.1.root (boundaryPath target path)).history) := by
  have split : path.dropLast ++ [pathTerminal path valid.nonempty] = path :=
    List.dropLast_append_getLast valid.nonempty
  have nodup : (path.dropLast ++ [pathTerminal path valid.nonempty]).Nodup := by
    rw [split]
    exact valid.nodup
  refine ⟨?_, ?_, ?_⟩
  · simp only [rawPathNode, boundaryPath,
      List.getLast?_append_of_ne_nil _ valid.nonempty, pathTerminal,
      List.getLast?_eq_some_getLast valid.nonempty, Option.getD_some]
  · intro member
    rcases List.mem_append.mp member with boundary | earlier
    · exact valid.outside _ (List.getLast_mem valid.nonempty) boundary
    · exact (List.nodup_append.mp nodup).2.2 _ earlier _ (by simp) rfl
  · intro atom member
    rw [boundaryPath_raw_history single target path]
    apply List.mem_map.mpr
    refine ⟨atom, ?_, rfl⟩
    rcases List.mem_append.mp member with boundary | earlier
    · exact List.mem_append.mpr (Or.inr (List.mem_reverse.mp boundary))
    · exact List.mem_append.mpr (Or.inl
        (List.mem_reverse.mpr ((List.dropLast_sublist path).mem earlier)))

include agreement admissible supported single calibrated in
/-- Successful actual boundary facts decode to a proper physical sign under the residual
induction hypothesis. The frame and both executions are derived, with their exact budget. -/
theorem relativeSign_of_snapshot_match (step : Step)
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
    (depth : Nat) (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (matched : ((snapshotWith step input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel =
      ((snapshotWith step input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode target.1.root
          (boundaryPath target (path.map (e : Equiv.Perm input.Atom))))).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshotWith step input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel = some label)
    (proper : ∀ c : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (target.1.node.history.reverse ++ path.dropLast) d.1 c.1 →
        c.1 ≠ d.1 → relativeSign input.detectedMultiCenterMolecule cfg e c = 1) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  obtain ⟨original, pulled⟩ := snapshot_boundary_matched_pullback input mol agreement admissible
    supported single e step stepMap target reference fixedBoundary fixedReference path depth
    (inputGeometry input) source sourceReached matched label observed
  have reached := snapshot_path_reached target.1.root (boundaryPath target path) step
    mol (sparseOperations input mol) depth (inputGeometry input) [] source sourceReached
    reference.val label observed
  obtain ⟨atomEq, outside, carried⟩ := witness_boundary input single target entry path valid
  rw [terminal] at atomEq outside
  have frame := LocalizedMarkedDetectedFrames.detected_frame mol input agreement admissible
    supported single d (rawPathNode target.1.root (boundaryPath target path)) reached rfl atomEq.symm
  exact relativeSign_eq_one_of_residual_signs input mol agreement admissible supported single cfg e
    calibrated (target.1.node.history.reverse ++ path.dropLast)
    (rawPathNode target.1.root (boundaryPath target path)) d.1 atomEq outside carried reached proper
    (sparseOperations input mol) step stepCongr stepFlip d atomEq.symm _ frame
    (depth + source.history.length - ((boundaryPath target path).length + 1)) []
    (some reference.val) label original pulled

include agreement admissible supported single calibrated in
/-- The path-label match returned by actual-key reconstruction directly supplies the
orientation step below an arbitrary target. No optional fact equality is an extra premise. -/
theorem relativeSign_of_path_labels (step : Step)
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
    (depth : Nat) (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (matched : PathLabelsAgree treeL treeR
      (rawStateReader input (snapshotWith step input mol depth (inputGeometry input) source reference.val) target)
      (rawStateReader input (snapshotWith step input mol depth (inputGeometry input) source reference.val) target)
      target.1.node.history.reverse path (path.map (e : Equiv.Perm input.Atom)))
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshotWith step input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel = some label)
    (proper : ∀ c : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (target.1.node.history.reverse ++ path.dropLast) d.1 c.1 →
        c.1 ≠ d.1 → relativeSign input.detectedMultiCenterMolecule cfg e c = 1) :
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
  have facts := fact_labels_eq_of_boundary_pathLabelsAgree single
    (snapshotWith step input mol depth (inputGeometry input) source reference.val) target
    treeL treeR path (path.map (e : Equiv.Perm input.Atom)) valid.nonempty nonempty
    (by rw [terminal]; exact detected d)
    (by rw [imageTerminal]; exact detected (input.detectedMultiCenterMolecule.centerPerm e d)) matched
  exact relativeSign_of_snapshot_match input mol agreement admissible supported single cfg e
    calibrated step stepMap stepCongr stepFlip target reference entry fixedBoundary fixedReference
    path valid d terminal depth source sourceReached facts label observed proper

end TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation.witness_boundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation.relativeSign_of_snapshot_match
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation.relativeSign_of_path_labels
