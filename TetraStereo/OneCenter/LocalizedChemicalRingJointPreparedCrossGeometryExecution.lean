import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMatchedExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Optional label matches between two actual geometry snapshots identify executions at the
same source query. The second geometry is pulled back along the reconstructed molecular map.
In the mirror application this normalizes the image execution before physical sign decoding;
no successful label, physical sense, or equality of whole generated states is inferred here. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryExecution

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointPreparedLabelExecution (snapshot_label_execution)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointOperationTransportExecution (actual_preparedDescriptor_map)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (Geometry)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement admissible supported single in
/-- A successful matched observation on two geometry sides gives the two exact smaller
descriptor calls. All retained references and the recursive budget are preserved. -/
theorem snapshot_cross_matched_pullback (depth : Nat) (first second : Geometry)
    (source query : RawMolecule.CanonicalBranchNode)
    (sourceReached : Reached mol source) (queryReached : Reached mol query)
    (references : List input.Atom)
    (fixedReferences : ∀ reference ∈ references, (e : Equiv.Perm input.Atom) reference = reference)
    (matched : ((generated input mol depth first source references).factAt? query).map factLabel =
      ((generated input mol depth second source references).factAt?
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) query)).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((generated input mol depth first source references).factAt? query).map factLabel =
      some label) :
    let remaining := depth + source.history.length - query.history.length
    preparedDescriptor? mol (jointOperations input mol) remaining first []
        (references.map Fin.val) query = some label ∧
      preparedDescriptor? mol (jointOperations input mol) remaining
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) second) []
        (references.map Fin.val) query = some label := by
  dsimp only
  let σ := relabelOf input (e : Equiv.Perm input.Atom)
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e
  have imageReached := reached_map sym admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single) query queryReached
  have original := snapshot_label_execution (rawStepPrepared? (jointOperations input mol)) mol
    depth first [] source sourceReached (references.map Fin.val) query queryReached label observed
  have image := snapshot_label_execution (rawStepPrepared? (jointOperations input mol)) mol
    depth second [] source sourceReached (references.map Fin.val) (mapNode σ query)
    imageReached label (matched.symm.trans observed)
  have imageLength : (mapNode σ query).history.length = query.history.length := by
    simp only [mapNode_history, List.length_map]
  rw [imageLength] at image
  let graphAut : input.moleculeGraph.Aut :=
    ⟨(e : Equiv.Perm input.Atom),
      MultiCenterMolecule.Aut.mem_molAut (m := input.detectedMultiCenterMolecule) e⟩
  have transported := actual_preparedDescriptor_map input mol agreement admissible supported single
    graphAut sym (depth + source.history.length - query.history.length) second
    (references.map Fin.val) query queryReached
  have fixedRaw : (references.map Fin.val).map σ = references.map Fin.val := by
    rw [List.map_map]
    apply List.map_congr_left
    intro reference member
    exact (relabelOf_val input (e : Equiv.Perm input.Atom) reference).trans
      (congrArg Fin.val (fixedReferences reference member))
  change preparedDescriptor? mol (jointOperations input mol)
      (depth + source.history.length - query.history.length) second []
      ((references.map Fin.val).map σ) (mapNode σ query) = _ at transported
  rw [fixedRaw] at transported
  exact ⟨original, transported.symm.trans image⟩

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryExecution.snapshot_cross_matched_pullback
