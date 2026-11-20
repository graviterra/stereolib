import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootAssignment
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Every actually detected center supplies the occurrence data used by the root proof.
No caller supplies a frame, successful lookup, or root-address correspondence. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootInput

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData occurrenceData_exists)
open LocalizedMarkedReachableConfigurations (Reached reached_root)
open LocalizedMarkedCertifiedTerminalRefusal (raw_atom_bound)

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center)

include agreement in
theorem root_reached : Reached mol (canonicalCenterRoot c.1.val) :=
  reached_root mol c.1.val (raw_atom_bound mol input agreement c.1)

include agreement admissible supported single in
theorem root_data : ∃ data : OccurrenceData input mol c (canonicalCenterRoot c.1.val),
    data.target.1.address = [] := by
  obtain ⟨data⟩ := occurrenceData_exists input mol agreement admissible supported single c
    (canonicalCenterRoot c.1.val) (root_reached input mol agreement c) rfl rfl
  refine ⟨data, ?_⟩
  have history : data.target.1.node.history = [c.1] := by
    apply List.map_injective_iff.mpr Fin.val_injective
    exact (LocalizedMarkedCarrierLookup.lookup?_sound input _ _ data.found).history
  have address := (input.legitimateOccurrence_transport single 1
    (input.carrierOccurrence_legitimate single data.target)).sourceAddress
  rw [address]
  simp [CertifiedLocalizedCIPInput.canonicalAddress, history]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootInput

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootInput.root_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootInput.root_data
