import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Root execution from physical tie reconstruction. The assembly lemmas below consume the
root source-proper reconstruction, derive strictness, and give the actual two-geometry reading.
The letter formula refers to the actual independent-key ranks; an independent chemical
interpretation of the generated auxiliary letters is a separate refinement obligation. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootAssignment

open CertifiedLocalizedCIPInput
open MultiCenterMolecule (PairwiseProperDistinguishable)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt rank observedGeometry)
open LocalizedChemicalRingJointPreparedOccurrenceCorrection (SourceProper)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (properTransport_of_sourceProper)
open LocalizedChemicalRingJointPreparedExecution
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingPhysicalSense (inputGeometry letterOfSign)
open LocalizedChemicalRingCompletenessMarked (readback_enum)
open LocalizedGenericMarkedRecalculation (structuralDepth caseFromMirror? readback_mirror)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)
  (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
  (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c)
  (references : List input.Atom)

/-- The actual ranks on each geometry, named without supplying a desired order. -/
def geometryRank (reflected : Bool) : Equiv.Perm (Fin 4) :=
  rank input mol c node data (slotKeys input mol single c node data
    (sideState input mol node (inputGeometry input) references reflected) references)

variable (physicalTies : ∀ (reflected : Bool) (left right : Fin 4), left ≠ right →
  slotKeys input mol single c node data
      (sideState input mol node (inputGeometry input) references reflected) references left =
    slotKeys input mol single c node data
      (sideState input mol node (inputGeometry input) references reflected) references right →
  SourceProper input cfg data.target references
    (referenceAt input mol c node data left) (referenceAt input mol c node data right))

include rootAddress current properDistinct physicalTies in
theorem keys_injective (reflected : Bool) :
    Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references) := by
  intro left right tie
  by_contra different
  have transport := properTransport_of_sourceProper input mol c node data cfg rootAddress current
    references left right (physicalTies reflected left right different tie)
  exact properDistinct _ _ (fun same => different (data.ligandOf.injective same)) transport

include agreement admissible supported rootAddress current properDistinct physicalTies in
/-- All operational failures are eliminated; each side reads the actual sorted coordinates. -/
theorem descriptor_eq_readings :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node =
      caseFromMirror?
        (LocalizedGenericMarkedRecalculation.readback? (inputGeometry input)
          (LocalizedChemicalRingCompletenessMarked.enumeration input c
            (geometryRank input mol single c node data references false)))
        (LocalizedGenericMarkedRecalculation.readback? (LocalizedGenericMarkedRecalculation.mirror
            (inputGeometry input))
          (LocalizedChemicalRingCompletenessMarked.enumeration input c
            (geometryRank input mol single c node data references true))) := by
  rw [descriptor_eq]
  have first := step_eq input mol agreement admissible supported single c node data
    (structuralDepth mol node) (inputGeometry input) references
  have second := step_eq input mol agreement admissible supported single c node data
    (structuralDepth mol node) (LocalizedGenericMarkedRecalculation.mirror (inputGeometry input))
    references
  have firstInj := keys_injective input mol single cfg c node data rootAddress current properDistinct
    references physicalTies false
  have secondInj := keys_injective input mol single cfg c node data rootAddress current properDistinct
    references physicalTies true
  change Function.Injective (keys input mol single c node data (structuralDepth mol node)
    (inputGeometry input) references) at firstInj
  change Function.Injective (keys input mol single c node data (structuralDepth mol node)
    (LocalizedGenericMarkedRecalculation.mirror (inputGeometry input)) references) at secondInj
  rw [if_pos firstInj] at first
  rw [if_pos secondInj] at second
  rw [first, second]
  rfl

include agreement admissible supported rootAddress current properDistinct physicalTies in
/-- Explicit coordinate/configuration formula for the successful actual descriptor. -/
theorem descriptor_eq_signs
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node =
      caseFromMirror?
        (some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
          permHandedness (geometryRank input mol single c node data references false))))
        (some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
          permHandedness (geometryRank input mol single c node data references true))).swap) := by
  rw [descriptor_eq_readings input mol agreement admissible supported single cfg c node data
    rootAddress current properDistinct references physicalTies, readback_mirror,
    readback_enum input cfg c calibrated, readback_enum input cfg c calibrated]
  rfl

include agreement admissible supported rootAddress current properDistinct physicalTies in
theorem descriptor_success
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c) :
    ∃ label, preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = some label := by
  rw [descriptor_eq_signs input mol agreement admissible supported single cfg c node data
    rootAddress current properDistinct references physicalTies calibrated]
  exact ⟨_, rfl⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootAssignment

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootAssignment.keys_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootAssignment.descriptor_eq_readings
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootAssignment.descriptor_eq_signs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootAssignment.descriptor_success
