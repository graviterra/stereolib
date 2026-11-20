import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A global physical mirror symmetry fixing the root forces any returned descriptor to be
lowercase. Combined with the closed root success theorem this derives an actual lowercase
assignment. This is a sufficient symmetry criterion, not the general physical pair-count iff. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorSymmetry

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingJointPreparedRootInput (root_data root_reached)
open LocalizedChemicalRingJointPreparedGeometryCongruence (preparedFacts_congr)
open LocalizedChemicalRingJointPreparedGeometryFlip (preparedDescriptor_flip)
open LocalizedChemicalRingJointOperationTransportExecution (actual_preparedDescriptor_map)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut)
open LocalizedChemicalRingJointPreparedReflection (descriptorOfStep_spatialMirror)
open LocalizedChemicalRingDescriptorSpatialMirror (spatialMirror)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedGenericMarkedRecalculation
  (Geometry mirror readback? readback_mirror flatMap_congr_mem structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (c : input.detectedMultiCenterMolecule.Center)
  (e : input.detectedMultiCenterMolecule.Aut)
  (fixed : (e : Equiv.Perm input.Atom) c.1 = c.1)
  (negative : ∀ d : input.detectedMultiCenterMolecule.Center,
    relativeSign input.detectedMultiCenterMolecule cfg e d = -1)

include agreement admissible supported single calibrated fixed negative in
/-- The actual root output is fixed by descriptor reflection under an independent physical
mirror symmetry. Calibration and all generated child states are derived at both geometries. -/
theorem assignCenter_spatialMirror_fixed :
    preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val =
      (preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val).map
        spatialMirror := by
  obtain ⟨data, _⟩ := root_data input mol agreement admissible supported single c
  let root := canonicalCenterRoot c.1.val
  let σ := relabelOf input (e : Equiv.Perm input.Atom)
  let pulled := pullback σ (inputGeometry input)
  let depth := structuralDepth mol root
  have reached := root_reached input mol agreement c
  have agree := agreeOn_of_mirror mol input agreement admissible.1.1 admissible.1.2 supported
    single cfg e c.1.val (LocalizedMarkedCertifiedTerminalRefusal.raw_atom_bound mol input agreement c.1)
    calibrated (fun _ _ _ _ d _ => negative d)
  have children : ∀ first second : Geometry, AgreeOn (Below mol root) mol first second →
      ∀ M, childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) first [] root M =
        childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) second [] root M := by
    intro first second same M
    unfold childrenUnder
    exact flatMap_congr_mem _ _ _ fun child edge =>
      preparedFacts_congr mol (jointOperations input mol) (Below mol root)
        (fun parent child below edge => below_child root parent child below edge)
        depth first second same [] M child (below_of_child root child edge)
  have rootAgree : ∀ L : List Nat, (∀ x ∈ L, x ∈ data.atoms) →
      readback? pulled L = flipBy 1 (readback? (mirror (inputGeometry input)) L) := by
    intro L subset
    have h := readback_pullback_frame input mol agreement admissible supported single cfg e
      calibrated c root rfl reached data.atoms data.rawFrame L subset
    rw [negative c, flipBy_eq_swap (-1) (by norm_num)] at h
    simpa only [flipBy_eq_id 1 rfl, id_eq, readback_mirror] using h
  have geomEq := preparedDescriptor_flip mol (jointOperations input mol) 1 pulled
    (mirror (inputGeometry input)) depth root data.atoms data.rawFrame rootAgree [] []
    (children _ _ agree) (children _ _ agree.mirror)
  simp only [flipDescriptorBy] at geomEq
  let graphAut : input.moleculeGraph.Aut :=
    ⟨e, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule e⟩
  have mapped := actual_preparedDescriptor_map input mol agreement admissible supported single
    graphAut (structuralSymmetry_of_aut input mol agreement admissible supported e)
    depth (inputGeometry input) [] root reached
  have rawFixed : σ c.1.val = c.1.val :=
    (relabelOf_val input (e : Equiv.Perm input.Atom) c.1).trans (congrArg Fin.val fixed)
  have rootFixed : mapNode σ root = root := by
    simp only [root, mapNode, canonicalCenterRoot, List.map_singleton, rawFixed]
  change preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) []
    ([].map σ) (mapNode σ root) = preparedDescriptor? mol (jointOperations input mol) depth
      pulled [] [] root at mapped
  rw [List.map_nil, rootFixed] at mapped
  exact mapped.trans (geomEq.trans (descriptorOfStep_spatialMirror
    (rawStepPrepared? (jointOperations input mol)) mol depth (inputGeometry input) [] [] root))

include agreement admissible supported single calibrated fixed negative in
/-- A physically properly distinguishable root with global mirror symmetry receives an
actual pseudoasymmetric descriptor. No desired output or successful execution is assumed. -/
theorem assignCenter_pseudo
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (properDistinct : input.detectedMultiCenterMolecule.PairwiseProperDistinguishable cfg c) :
    ∃ raw, preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val =
      some (.pseudoasymmetric raw) := by
  obtain ⟨label, returned⟩ := LocalizedChemicalRingJointPreparedRootSuccess.assignCenter_success
    input mol agreement admissible supported single charge cfg calibrated c properDistinct
  have invariant := assignCenter_spatialMirror_fixed input mol agreement admissible supported
    single cfg calibrated c e fixed negative
  rw [returned] at invariant
  cases label with
  | chiral raw => cases raw <;> cases invariant
  | pseudoasymmetric raw => exact ⟨raw, returned⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorSymmetry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorSymmetry.assignCenter_spatialMirror_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorSymmetry.assignCenter_pseudo
