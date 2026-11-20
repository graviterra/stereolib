import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyRelabel
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessPhysicalExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! The exact generated optional-label covariance, read as the actual molecular descriptor
map at a complete detected occurrence. Missing facts and lowercase facts are preserved. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorPathReadback

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointPreparedRootBranchSelector (boundaryPath_of_root)
open LocalizedChemicalRingJointPreparedPhysicalMirrorKeys (generated_label_eq_of_physicalMirror)
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedChemicalRingWitnessPhysicalExecution (rawPathNode_map)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open RetainedCoherentSymmetry (ResidualObsPath)
open RootedTetrahedralBranchSymmetry (LigandBranchReaches)

noncomputable section
open scoped Classical

abbrev graphAut (input : CertifiedLocalizedCIPInput)
    (e : input.detectedMultiCenterMolecule.Aut) : input.moleculeGraph.Aut := ⟨e.1, e.2.1⟩

private theorem descriptor_of_factLabel (fact : OccurrenceAuxFact) :
    localizedAuxiliaryDescriptor (factLabel fact) = factDescriptor fact := by
  cases h : fact.uppercase <;> cases r : fact.descriptor <;>
    simp [factLabel, factDescriptor, h, r, pseudoRSOfRS, localizedAuxiliaryDescriptor]

private theorem map_label_eq_map_descriptor (facts : Option OccurrenceAuxFact) :
    (facts.map factLabel).map localizedAuxiliaryDescriptor = facts.map factDescriptor := by
  cases facts with
  | none => rfl
  | some f => simp [descriptor_of_factLabel]

theorem descriptorMap_eq_of_path
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
    (rootAddress : data.target.1.address = [])
    (left : Fin 4) (e : input.detectedMultiCenterMolecule.Aut)
    (centerFixed : input.detectedMultiCenterMolecule.centerPerm e c = c)
    (physical : ∀ other : input.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.detectedMultiCenterMolecule c (data.ligandOf left) other.1 →
        input.detectedMultiCenterMolecule.configurationSign cfg other *
          permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e other) =
        (-1 : ℝ) * input.detectedMultiCenterMolecule.configurationSign cfg
          (input.detectedMultiCenterMolecule.centerPerm e other))
    (occ : DetectedOccurrence input.moleculeGraph)
    (rootEq : occ.1.root = data.target.1.root)
    (valid : ResidualObsPath input.moleculeGraph [c.1]
      (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) occ.1.path) :
    rawStateDescriptorMap input
      (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] true)
      (mapDetected input.moleculeGraph (graphAut input e) occ) =
    rawStateDescriptorMap input
      (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false) occ := by
  let d : input.detectedMultiCenterMolecule.Center := ⟨occ.1.atom, by
    exact (input.moleculeGraph.mem_tetrahedralCenterSet _).mpr
      ((input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mpr occ.2)⟩
  have last : occ.1.path.getLast? = some d.1 := by
    simp only [d, OccurrenceUnit.atom, List.getLast?_eq_some_getLast valid.nonempty,
      Option.getD_some]
  have labels := generated_label_eq_of_physicalMirror input mol agreement admissible supported
    single cfg c calibrated data rootAddress left e centerFixed physical [] occ.1.path d valid last
  rw [boundaryPath_of_root input data.target rootAddress] at labels
  rw [rawPathNode_map] at labels
  have descriptors := congrArg (Option.map localizedAuxiliaryDescriptor) labels
  rw [map_label_eq_map_descriptor, map_label_eq_map_descriptor] at descriptors
  simpa only [sideState, Bool.false_eq_true, ↓reduceIte, List.map_nil,
    rawStateDescriptorMap, rawStateFact?, OccurrenceAuxState.factAt?, canonicalOccurrenceKey,
    rawPathNode, rawOccurrenceKey, mapDetected, mapOccurrence, graphAut, rootEq] using descriptors.symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorPathReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorPathReadback.descriptorMap_eq_of_path
