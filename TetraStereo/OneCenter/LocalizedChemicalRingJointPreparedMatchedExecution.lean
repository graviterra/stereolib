import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionWitness
import TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Matched observations in an actual prepared snapshot give equal successful descriptor
executions at the source query under original and pulled-back geometry. The image query's
reachability and execution are derived; all retained references are fixed by the same map.
This connects the reconstruction witness to the geometric sign decoder without assuming
physical properness, desired descriptors or equality of entire generated states. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMatchedExecution

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointPreparedLabelExecution (snapshot_label_execution)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointOperationTransportExecution (actual_preparedDescriptor_map)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant descendant_reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (Geometry)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement admissible supported single in
theorem snapshot_matched_pullback (depth : Nat) (geom : Geometry)
    (source query : RawMolecule.CanonicalBranchNode)
    (sourceReached : Reached mol source) (queryReached : Reached mol query)
    (references : List input.Atom)
    (fixedReferences : ∀ reference ∈ references, (e : Equiv.Perm input.Atom) reference = reference)
    (matched : ((generated input mol depth geom source references).factAt? query).map factLabel =
      ((generated input mol depth geom source references).factAt?
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) query)).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((generated input mol depth geom source references).factAt? query).map factLabel =
      some label) :
    let remaining := depth + source.history.length - query.history.length
    preparedDescriptor? mol (jointOperations input mol) remaining geom []
        (references.map Fin.val) query = some label ∧
      preparedDescriptor? mol (jointOperations input mol) remaining
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) geom) []
        (references.map Fin.val) query = some label := by
  dsimp only
  let σ := relabelOf input (e : Equiv.Perm input.Atom)
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e
  have imageReached := reached_map sym admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single) query queryReached
  have original := snapshot_label_execution (rawStepPrepared? (jointOperations input mol)) mol
    depth geom [] source sourceReached (references.map Fin.val) query queryReached label observed
  have image := snapshot_label_execution (rawStepPrepared? (jointOperations input mol)) mol
    depth geom [] source sourceReached (references.map Fin.val) (mapNode σ query)
    imageReached label (matched.symm.trans observed)
  have imageLength : (mapNode σ query).history.length = query.history.length := by
    simp only [mapNode_history, List.length_map]
  rw [imageLength] at image
  let graphAut : input.moleculeGraph.Aut :=
    ⟨(e : Equiv.Perm input.Atom),
      MultiCenterMolecule.Aut.mem_molAut (m := input.detectedMultiCenterMolecule) e⟩
  have transported := actual_preparedDescriptor_map input mol agreement admissible supported single
    graphAut sym (depth + source.history.length - query.history.length) geom
    (references.map Fin.val) query queryReached
  have fixedRaw : (references.map Fin.val).map σ = references.map Fin.val := by
    rw [List.map_map]
    apply List.map_congr_left
    intro reference member
    exact (relabelOf_val input (e : Equiv.Perm input.Atom) reference).trans
      (congrArg Fin.val (fixedReferences reference member))
  change preparedDescriptor? mol (jointOperations input mol)
      (depth + source.history.length - query.history.length) geom []
      ((references.map Fin.val).map σ) (mapNode σ query) = _ at transported
  rw [fixedRaw] at transported
  exact ⟨original, transported.symm.trans image⟩

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMatchedExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMatchedExecution.snapshot_matched_pullback
