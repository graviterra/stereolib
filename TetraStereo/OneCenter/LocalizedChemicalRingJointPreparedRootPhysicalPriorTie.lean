import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmResidualPath
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorPathReadback
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Independent physical mirror transport implies an actual original root prior tie.
All actual semantic reads, generated labels, structural cursor transport and key comparison
are derived. Rings and stereochemically dependent non-root centers are admitted. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPriorTie

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointPreparedRootArmLocality (rootFrame)
open LocalizedChemicalRingJointPreparedRootKeyRelabel (rawState_priorTie_of_reflected_reads)
open LocalizedChemicalRingJointPreparedMirrorPathReadback (graphAut descriptorMap_eq_of_path)
open LocalizedChemicalRingJointPreparedActualArmResidualPath (arm_read_residual)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open RootedTetrahedralBranchSymmetry (MirrorTransport LigandBranchReaches)
open LocalizedChemicalRingReferenceConsensusReflection (mirrorFact rawStateDescriptorMap_mirror)
open LocalizedGenericMarkedRecalculation (structuralDepth)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (c : input.detectedMultiCenterMolecule.Center)
  (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
  (rootAddress : data.target.1.address = [])

include agreement admissible supported calibrated rootAddress in
theorem actual_readsAgree_of_physicalMirror
    (left : Fin 4) (e : input.detectedMultiCenterMolecule.Aut)
    (centerFixed : input.detectedMultiCenterMolecule.centerPerm e c = c)
    (physical : ∀ other : input.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.detectedMultiCenterMolecule c (data.ligandOf left) other.1 →
        input.detectedMultiCenterMolecule.configurationSign cfg other *
          permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e other) =
        (-1 : ℝ) * input.detectedMultiCenterMolecule.configurationSign cfg
          (input.detectedMultiCenterMolecule.centerPerm e other)) :
    ReadsAgree input.moleculeGraph (graphAut input e)
      (rawStateDescriptorMap input
        (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] true))
      (rawStateDescriptorMap input
        (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false))
      (input.molecularFrameUnit data.target.1)
      ((rootFrame input mol single c (canonicalCenterRoot c.1.val) data
        (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false)).actualArmGraphs left) := by
  intro node steps occ real ancestors context
  obtain ⟨rootEq, valid⟩ := arm_read_residual input mol single c (canonicalCenterRoot c.1.val) data
    (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false)
    left rootAddress rfl node steps occ real ancestors context
  exact descriptorMap_eq_of_path input mol agreement admissible supported single cfg c
    calibrated data rootAddress left e centerFixed physical occ rootEq valid

include agreement admissible supported calibrated rootAddress in
theorem priorTie_of_mirrorTransport (left right : Fin 4)
    (transport : MirrorTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right)) :
    (ofLex (rawStateKeys input single
      (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false)
      data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left)).1 =
    (ofLex (rawStateKeys input single
      (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false)
      data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl right)).1 := by
  obtain ⟨e, centerFixed, ligandSent, physical⟩ := transport
  have reads := actual_readsAgree_of_physicalMirror input mol agreement admissible supported single
    cfg calibrated c data rootAddress left e centerFixed (by simpa using physical)
  let state0 := sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false
  let state1 := sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] true
  have reflected : state1 = state0.map mirrorFact := by
    simpa [state0, state1, sideState] using
      (LocalizedChemicalRingJointPreparedReflection.generated_mirror input mol
        (structuralDepth mol (canonicalCenterRoot c.1.val)) (inputGeometry input)
        (canonicalCenterRoot c.1.val) [])
  change ReadsAgree input.moleculeGraph (graphAut input e)
    (rawStateDescriptorMap input state1) (rawStateDescriptorMap input state0)
    (input.molecularFrameUnit data.target.1)
    ((rootFrame input mol single c (canonicalCenterRoot c.1.val) data state0).actualArmGraphs left) at reads
  rw [reflected, rawStateDescriptorMap_mirror] at reads
  have fixed : (graphAut input e : Equiv.Perm input.Atom) c.1 = c.1 :=
    congrArg Subtype.val centerFixed
  have sent : (graphAut input e : Equiv.Perm input.Atom)
      (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) =
      referenceAt input mol c (canonicalCenterRoot c.1.val) data right := by
    have moved := input.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt e c (data.ligandOf left)
    rw [centerFixed, ligandSent] at moved
    exact moved.symm
  exact rawState_priorTie_of_reflected_reads input mol single c (canonicalCenterRoot c.1.val)
    data state0 rootAddress rfl (graphAut input e) left right fixed sent reads

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPriorTie

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPriorTie.actual_readsAgree_of_physicalMirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPriorTie.priorTie_of_mirrorTransport
