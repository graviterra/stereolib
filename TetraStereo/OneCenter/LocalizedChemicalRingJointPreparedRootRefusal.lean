import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootInput
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! An independently specified odd physical root symmetry forces the actual root assigner
to refuse. This is a one-way refusal theorem, not a claim that every root refusal is such
a symmetry. No auxiliary rigidity, root branch disjointness, or acyclicity is required. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootRefusal

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedRootInput (root_data root_reached)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingJointPreparedRefusalCharacterization
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter?)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
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

include agreement admissible supported single calibrated in
theorem assignCenter_none_of_oddBoundary
    (obstruction : OddBoundarySymmetry input cfg c [] []) :
    preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val = none := by
  obtain ⟨data, rootAddress⟩ := root_data input mol agreement admissible supported single c
  have history := root_history input mol c (canonicalCenterRoot c.1.val) data rootAddress rfl
  exact refusal_of_oddBoundary input mol agreement admissible supported single cfg calibrated
    c (canonicalCenterRoot c.1.val) data (root_reached input mol agreement c) rfl [] []
    (by simp only [history, List.reverse_singleton, List.nil_append]) (by simp) obstruction

include agreement admissible supported single calibrated in
/-- A molecular automorphism reverses this center while preserving every other center's
physical configuration. All operational inputs are constructed from the actual detected center. -/
theorem assignCenter_none_of_oddSymmetry
    (e : input.detectedMultiCenterMolecule.Aut)
    (fixed : (e : Equiv.Perm input.Atom) c.1 = c.1)
    (odd : relativeSign input.detectedMultiCenterMolecule cfg e c = -1)
    (proper : ∀ d : input.detectedMultiCenterMolecule.Center, d ≠ c →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1) :
    preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val = none := by
  apply assignCenter_none_of_oddBoundary input mol agreement admissible supported single cfg
    calibrated c
  refine ⟨e, ?_, ?_, odd, ?_⟩
  · intro atom member
    have same : atom = c.1 := by simpa only [List.nil_append, List.mem_singleton] using member
    simpa only [same] using fixed
  · intro atom member
    cases member
  · intro d outside
    apply proper d
    intro same
    subst d
    exact outside (by simp)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootRefusal.assignCenter_none_of_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootRefusal.assignCenter_none_of_oddSymmetry
