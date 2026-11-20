import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Matched actual snapshot labels remain execution evidence when the witnessing automorphism
moves the inherited reference. Covariance then uses the INVERSE-image reference in the
pulled-back execution. The residual physical induction hypothesis identifies its ordinary
execution as the observed descriptor flipped by the current physical relative sign.

No equality between the two reference contexts is assumed. The properness criterion below
states exactly the finite two-reference agreement still needed at this witness query.
The two-port specialization keeps the same query, original geometry, and exact depth.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingShiftedReferenceWitness

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingBoundaryWitnessExecution LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingBoundaryWitnessOrientation LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingWitnessExecution LocalizedChemicalRingWitnessPhysicalExecution
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingResidualOrientationStep
open LocalizedChemicalRingSemanticSymmetry (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingCompletenessPermutationTransport (descriptorWith_map)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (Geometry)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

private theorem flip_twice (s : ℝ) (x : Option LocalizedTetrahedralRSPseudoDescriptor) :
    flipDescriptorBy s (flipDescriptorBy s x) = x := by
  classical
  by_cases one : s = 1
  · simp only [flipDescriptorBy, one, if_pos]
  · cases x with
    | none => simp only [flipDescriptorBy, if_neg one, Option.map_none]
    | some label =>
        simp only [flipDescriptorBy, if_neg one, Option.map_some]
        cases label with
        | chiral letter => cases letter <;> rfl
        | pseudoasymmetric letter => cases letter <;> rfl

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement admissible supported single in
/-- Both successful executions are derived from the actual snapshot. Reference fixation
is replaced by its precise inverse-image context, not by a reference-independence premise. -/
theorem snapshot_inverse_reference_execution (step : Step)
    (stepMap : StepMap step mol (sparseOperations input mol)
      (relabelOf input (e : Equiv.Perm input.Atom)))
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (reference : input.Atom)
    (fixedBoundary : ∀ atom ∈ target.1.node.history.reverse, (e : Equiv.Perm input.Atom) atom = atom)
    (path : List input.Atom) (depth : Nat) (geom : Geometry)
    (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (matched : ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel =
      ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root
          (boundaryPath target (path.map (e : Equiv.Perm input.Atom))))).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel = some label) :
    let remaining := depth + source.history.length - ((boundaryPath target path).length + 1)
    descriptorWith step mol (sparseOperations input mol) remaining geom [] (some reference.val)
        (rawPathNode target.1.root (boundaryPath target path)) = some label ∧
      descriptorWith step mol (sparseOperations input mol) remaining
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) []
        (some ((e : Equiv.Perm input.Atom).symm reference).val)
        (rawPathNode target.1.root (boundaryPath target path)) = some label := by
  have matchedFull : ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel =
      ((snapshotWith step input mol depth geom source reference.val).factAt?
        (rawPathNode target.1.root
          ((boundaryPath target path).map (e : Equiv.Perm input.Atom)))).map factLabel := by
    rw [boundaryPath_map target (e : Equiv.Perm input.Atom) fixedBoundary path]
    exact matched
  obtain ⟨original, image⟩ := matched_paths_execute target.1.root (boundaryPath target path)
    ((boundaryPath target path).map (e : Equiv.Perm input.Atom)) (by simp)
    step mol (sparseOperations input mol) depth geom [] source sourceReached reference.val
    matchedFull label observed
  refine ⟨original, ?_⟩
  have reached := snapshot_path_reached target.1.root (boundaryPath target path) step mol
    (sparseOperations input mol) depth geom [] source sourceReached reference.val label observed
  have fixedRoot := root_fixed_of_boundary single target (e : Equiv.Perm input.Atom) fixedBoundary
  have nodeMap : mapNode (relabelOf input (e : Equiv.Perm input.Atom))
      (rawPathNode target.1.root (boundaryPath target path)) =
      rawPathNode target.1.root ((boundaryPath target path).map (e : Equiv.Perm input.Atom)) := by
    simpa only [fixedRoot] using rawPathNode_map input (e : Equiv.Perm input.Atom)
      target.1.root (boundaryPath target path)
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e
  have cov := actual_covariant input mol agreement admissible supported single e
  have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
  have transport := descriptorWith_map sym admissible.1.1 admissible.1.2 rawSingle cov step stepMap
    (depth + source.history.length - ((boundaryPath target path).length + 1)) geom
    (some ((e : Equiv.Perm input.Atom).symm reference).val)
    (rawPathNode target.1.root (boundaryPath target path)) reached
  simp only [Option.map_some, relabelOf_val, Equiv.apply_symm_apply, nodeMap] at transport
  exact transport.symm.trans image

section Physical

variable (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (step : Step)
  (stepMap : StepMap step mol (sparseOperations input mol)
    (relabelOf input (e : Equiv.Perm input.Atom)))
  (stepCongr : StepCongr step mol (sparseOperations input mol))
  (stepFlip : StepFlip mol (sparseOperations input mol) step)
  {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
  (reference entry : input.Atom)
  (fixedBoundary : ∀ atom ∈ target.1.node.history.reverse, (e : Equiv.Perm input.Atom) atom = atom)
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
      c.1 ≠ d.1 → relativeSign input.detectedMultiCenterMolecule cfg e c = 1)

include agreement admissible supported single calibrated stepMap stepCongr stepFlip
  fixedBoundary sourceReached matched observed proper terminal in
/-- Exact finite reference-change equation. The inverse-reference descriptor is derived,
including its existence and case, from actual observations and the residual physical IH. -/
theorem shifted_descriptor_of_snapshot_match :
    let remaining := depth + source.history.length - ((boundaryPath target path).length + 1)
    let query := rawPathNode target.1.root (boundaryPath target path)
    descriptorWith step mol (sparseOperations input mol) remaining (inputGeometry input) []
        (some reference.val) query = some label ∧
      descriptorWith step mol (sparseOperations input mol) remaining (inputGeometry input) []
        (some ((e : Equiv.Perm input.Atom).symm reference).val) query =
          flipDescriptorBy (relativeSign input.detectedMultiCenterMolecule cfg e d) (some label) := by
  obtain ⟨original, pulled⟩ := snapshot_inverse_reference_execution input mol agreement admissible
    supported single e step stepMap target reference fixedBoundary path depth (inputGeometry input)
    source sourceReached matched label observed
  have reached := snapshot_path_reached target.1.root (boundaryPath target path) step mol
    (sparseOperations input mol) depth (inputGeometry input) [] source sourceReached reference.val
    label observed
  obtain ⟨atomEq, outside, carried⟩ := witness_boundary input single target entry path valid
  rw [terminal] at atomEq outside
  have frame := LocalizedMarkedDetectedFrames.detected_frame mol input agreement admissible
    supported single d (rawPathNode target.1.root (boundaryPath target path)) reached rfl atomEq.symm
  have below := underWith_eq_of_residual_signs input mol agreement admissible supported single
    cfg e calibrated (target.1.node.history.reverse ++ path.dropLast)
    (rawPathNode target.1.root (boundaryPath target path)) d.1 atomEq outside carried reached proper
    (sparseOperations input mol) step stepCongr
    (depth + source.history.length - ((boundaryPath target path).length + 1)) []
  have flip := descriptorWith_pullback input mol agreement admissible supported single cfg e
    calibrated d (rawPathNode target.1.root (boundaryPath target path)) atomEq.symm reached _ frame
    (sparseOperations input mol) step stepFlip
    (depth + source.history.length - ((boundaryPath target path).length + 1)) []
    (some ((e : Equiv.Perm input.Atom).symm reference).val)
    (fun mark => (below mark).1) (fun mark => (below mark).2)
  rw [pulled] at flip
  have inverted := congrArg
    (flipDescriptorBy (relativeSign input.detectedMultiCenterMolecule cfg e d)) flip
  rw [flip_twice] at inverted
  exact ⟨original, inverted.symm⟩

include agreement admissible supported single calibrated stepMap stepCongr stepFlip
  fixedBoundary sourceReached matched observed proper terminal in
/-- The exact remaining obligation is equality at these TWO reference contexts and this
one actual witness query. No all-context or all-depth equality is introduced. -/
theorem proper_iff_reference_agreement :
    let remaining := depth + source.history.length - ((boundaryPath target path).length + 1)
    let query := rawPathNode target.1.root (boundaryPath target path)
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 ↔
      descriptorWith step mol (sparseOperations input mol) remaining (inputGeometry input) []
        (some ((e : Equiv.Perm input.Atom).symm reference).val) query =
      descriptorWith step mol (sparseOperations input mol) remaining (inputGeometry input) []
        (some reference.val) query := by
  obtain ⟨original, shifted⟩ := shifted_descriptor_of_snapshot_match input mol agreement admissible
    supported single e cfg calibrated step stepMap stepCongr stepFlip target reference entry
    fixedBoundary path valid d terminal depth source sourceReached matched label observed proper
  dsimp only
  rw [original, shifted]
  constructor
  · intro sign
    simp only [flipDescriptorBy, sign, if_pos]
  · exact flipDescriptorBy_some_eq _ (relativeSign_eq_one_or_neg_one _ _ _ _) label

/-- The inverse-image context of a reference-fixed map followed on the right by a
two-port swap is exactly the other port. -/
theorem inverse_reference_two_port {V : Type*} (first correction : Equiv.Perm V)
    (reference other : V) (firstFixed : first reference = reference)
    (swappedBack : correction other = reference) :
    (first * correction).symm reference = other := by
  apply (first * correction).injective
  simp only [Equiv.apply_symm_apply, Equiv.Perm.mul_apply, swappedBack, firstFixed]

include agreement admissible supported single calibrated stepMap stepCongr stepFlip
  fixedBoundary sourceReached matched observed proper terminal in
/-- Specialization to the corrected map `first * correction`: the actual descriptor at
the other port is determined, but equality with the original port is not presumed. -/
theorem two_port_descriptor_of_snapshot_match
    (first correction : input.detectedMultiCenterMolecule.Aut)
    (action : e = first * correction) (other : input.Atom)
    (firstFixed : (first : Equiv.Perm input.Atom) reference = reference)
    (swapped : (correction : Equiv.Perm input.Atom) reference = other ∧
      (correction : Equiv.Perm input.Atom) other = reference) :
    let remaining := depth + source.history.length - ((boundaryPath target path).length + 1)
    let query := rawPathNode target.1.root (boundaryPath target path)
    descriptorWith step mol (sparseOperations input mol) remaining (inputGeometry input) []
        (some reference.val) query = some label ∧
      descriptorWith step mol (sparseOperations input mol) remaining (inputGeometry input) []
        (some other.val) query =
          flipDescriptorBy (relativeSign input.detectedMultiCenterMolecule cfg e d) (some label) := by
  have inverse : (e : Equiv.Perm input.Atom).symm reference = other := by
    rw [action]
    exact inverse_reference_two_port (first : Equiv.Perm input.Atom)
      (correction : Equiv.Perm input.Atom) reference other firstFixed swapped.2
  have result := shifted_descriptor_of_snapshot_match input mol agreement admissible supported
    single e cfg calibrated step stepMap stepCongr stepFlip target reference entry fixedBoundary
    path valid d terminal depth source sourceReached matched label observed proper
  simpa only [inverse] using result

end Physical
end TetraStereo.OneCenter.LocalizedChemicalRingShiftedReferenceWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingShiftedReferenceWitness.snapshot_inverse_reference_execution
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingShiftedReferenceWitness.shifted_descriptor_of_snapshot_match
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingShiftedReferenceWitness.proper_iff_reference_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingShiftedReferenceWitness.inverse_reference_two_port
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingShiftedReferenceWitness.two_port_descriptor_of_snapshot_match
