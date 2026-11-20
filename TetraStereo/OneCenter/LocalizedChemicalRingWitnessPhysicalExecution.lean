import TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep
import TetraStereo.OneCenter.LocalizedChemicalRingRankedWitnessLabels
import TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Matching recorded witness labels give matching actual executions under the original
and pulled-back geometries. The permutation acts on the whole raw node, including parent
and history, and fixes the inherited reference. This removes an execution-match premise
from the residual physical induction step. It does not infer a label from an absent fact. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingWitnessPhysicalExecution

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingWitnessExecution
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingResidualOrientationStep
open LocalizedChemicalRingSemanticSymmetry (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingCompletenessPermutationTransport (descriptorWith_map)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel rawStateReader)
open LocalizedMarkedOperationEvaluator (underWith)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms?)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

theorem rawPathNode_map (input : CertifiedLocalizedCIPInput) (π : Equiv.Perm input.Atom)
    (root : input.Atom) (path : List input.Atom) :
    mapNode (relabelOf input π) (rawPathNode root path) = rawPathNode (π root) (path.map π) := by
  have last (xs : List input.Atom) :
      relabelOf input π (xs.getLast?.getD root).val = ((xs.map π).getLast?.getD (π root)).val := by
    rw [List.getLast?_map]
    cases found : xs.getLast? <;> simp only [Option.map_none, Option.map_some,
      Option.getD_none, Option.getD_some, relabelOf_val]
  simp only [mapNode, rawPathNode]
  congr 1
  · exact last path
  · rw [DeclarativeCIP.dropLast_map]
    exact last path.dropLast
  · rw [← List.map_cons, ← List.map_reverse, List.map_map, List.map_map]
    apply List.map_congr_left
    intro atom _
    exact relabelOf_val input π atom

/-- The generated snapshot actually supplied to promotion, using the distant-reference step
and empty initial auxiliary state. -/
abbrev snapshot (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) (depth : Nat)
    (geom : Geometry) (source : RawMolecule.CanonicalBranchNode) (mark : Nat) : OccurrenceAuxState :=
  underWith mol (sparseOperations input mol) geom [] source
    (factsWith LocalizedPhysicalMarkedDistantReference.rawStep? mol (sparseOperations input mol) depth) mark

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement admissible supported single in
/-- Snapshot-label matches are actual successful executions under the original and
pulled-back geometries at the same budget, state and reference. Reachability is derived
from the snapshot, and the actual callbacks supply covariance. -/
theorem snapshot_matched_pullback (root reference : input.Atom)
    (fixedRoot : (e : Equiv.Perm input.Atom) root = root)
    (fixedReference : (e : Equiv.Perm input.Atom) reference = reference)
    (path : List input.Atom) (depth : Nat) (geom : Geometry)
    (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (matched : ((snapshot input mol depth geom source reference.val).factAt? (rawPathNode root path)).map factLabel =
      ((snapshot input mol depth geom source reference.val).factAt?
        (rawPathNode root (path.map (e : Equiv.Perm input.Atom)))).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshot input mol depth geom source reference.val).factAt? (rawPathNode root path)).map
      factLabel = some label) :
    let remaining := depth + source.history.length - (path.length + 1)
    descriptorWith LocalizedPhysicalMarkedDistantReference.rawStep? mol (sparseOperations input mol)
        remaining geom [] (some reference.val) (rawPathNode root path) = some label ∧
    descriptorWith LocalizedPhysicalMarkedDistantReference.rawStep? mol (sparseOperations input mol)
        remaining (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) []
        (some reference.val) (rawPathNode root path) = some label := by
  obtain ⟨original, image⟩ := matched_paths_execute root path (path.map (e : Equiv.Perm input.Atom))
    (by simp) LocalizedPhysicalMarkedDistantReference.rawStep? mol (sparseOperations input mol)
    depth geom [] source sourceReached reference.val matched label observed
  refine ⟨original, ?_⟩
  have reached := snapshot_path_reached root path LocalizedPhysicalMarkedDistantReference.rawStep?
    mol (sparseOperations input mol) depth geom [] source sourceReached reference.val label observed
  have nodeMap : mapNode (relabelOf input (e : Equiv.Perm input.Atom)) (rawPathNode root path) =
      rawPathNode root (path.map (e : Equiv.Perm input.Atom)) := by
    simpa only [fixedRoot] using rawPathNode_map input (e : Equiv.Perm input.Atom) root path
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e
  have cov := actual_covariant input mol agreement admissible supported single e
  have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
  have transport := descriptorWith_map sym admissible.1.1 admissible.1.2 rawSingle cov
    LocalizedPhysicalMarkedDistantReference.rawStep?
    (distantStep_map sym admissible.1.1 admissible.1.2 rawSingle cov)
    (depth + source.history.length - (path.length + 1)) geom (some reference.val)
    (rawPathNode root path) reached
  simp only [Option.map_some, relabelOf_val, fixedReference, nodeMap] at transport
  exact transport.symm.trans image

end TetraStereo.OneCenter.LocalizedChemicalRingWitnessPhysicalExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessPhysicalExecution.rawPathNode_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessPhysicalExecution.snapshot_matched_pullback
