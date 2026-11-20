import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder
import TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution
import TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Physical mirror signs on one root-deleted component determine the actual descriptor
execution at every detected occurrence inside it. The residual boundary is carried by the
query history and includes the root. No equality of generated labels or successful result
is assumed; optional descriptor equality includes refusal and keeps all reference lists. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorBranchExecution

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry RootedTetrahedralBranchSymmetry
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointPreparedSignedResidualDecoder
open LocalizedChemicalRingRankedReconstruction (component_weaken)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_iff)
open LocalizedCyclicMatchedReadingPhysicalTransport (inComponent_implies_ligandBranchReaches)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (mirror frameAtoms?)
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
  (root : input.detectedMultiCenterMolecule.Center) (ligand : Fin 4)
  (physical : ∀ d : input.detectedMultiCenterMolecule.Center,
    LigandBranchReaches input.detectedMultiCenterMolecule root ligand d.1 →
      input.detectedMultiCenterMolecule.configurationSign cfg d *
        permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e d) =
      (-1 : ℝ) * input.detectedMultiCenterMolecule.configurationSign cfg
        (input.detectedMultiCenterMolecule.centerPerm e d))

include physical in
theorem negative_of_component (d : input.detectedMultiCenterMolecule.Center)
    (component : InComponent input.moleculeGraph [root.1]
      (input.detectedMultiCenterMolecule.ligandAtomAt root ligand) d.1) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = -1 :=
  (relativeSign_eq_iff input.detectedMultiCenterMolecule cfg e d (-1)).mpr
    (physical d (inComponent_implies_ligandBranchReaches
      input.detectedMultiCenterMolecule root ligand d.1 component))

include agreement admissible supported single calibrated physical in
theorem descriptor_map_mirror_eq
    (B : List input.Atom) (rootInBoundary : root.1 ∈ B)
    (query : RawMolecule.CanonicalBranchNode) (reached : Reached mol query)
    (d : input.detectedMultiCenterMolecule.Center) (atomEq : query.atom = d.1.val)
    (outside : d.1 ∉ B) (carried : ∀ atom ∈ B, atom.val ∈ query.history)
    (component : InComponent input.moleculeGraph [root.1]
      (input.detectedMultiCenterMolecule.ligandAtomAt root ligand) d.1)
    (atoms : List Nat) (frame : frameAtoms? mol query = some atoms)
    (depth : Nat) (references : List Nat) :
    preparedDescriptor? mol (jointOperations input mol) depth (mirror (inputGeometry input)) []
        (references.map (relabelOf input (e : Equiv.Perm input.Atom)))
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) query) =
      preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) []
        references query := by
  have negative := negative_of_component input cfg e root ligand physical d component
  have residual : ∀ other : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph B d.1 other.1 → other.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg e other = -1 := by
    intro other connected _
    have weakened : InComponent input.moleculeGraph [root.1] d.1 other.1 :=
      component_weaken (by
        intro atom member
        have equal : atom = root.1 := List.mem_singleton.mp member
        exact equal ▸ rootInBoundary) connected
    exact negative_of_component input cfg e root ligand physical other
      ⟨component.1, component.2.trans weakened.2⟩
  have decoded := descriptor_flip_of_residual_mirror_signs input mol agreement admissible
    supported single cfg e calibrated B query d.1 atomEq.symm outside carried reached residual
    (jointOperations input mol) d atomEq atoms frame depth [] references
  rw [negative] at decoded
  norm_num only [neg_neg] at decoded
  simp only [LocalizedChemicalRingOrientationReadback.flipDescriptorBy] at decoded
  let graphAut : input.moleculeGraph.Aut :=
    ⟨(e : Equiv.Perm input.Atom),
      MultiCenterMolecule.Aut.mem_molAut (m := input.detectedMultiCenterMolecule) e⟩
  have transported :=
    LocalizedChemicalRingJointOperationTransportExecution.actual_preparedDescriptor_map
      input mol agreement admissible supported single graphAut
      (LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
        input mol agreement admissible supported e)
      depth (mirror (inputGeometry input)) references query reached
  exact transported.trans decoded

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorBranchExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorBranchExecution.negative_of_component
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorBranchExecution.descriptor_map_mirror_eq
