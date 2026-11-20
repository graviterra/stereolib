import TetraStereo.OneCenter.LocalizedChemicalRingActualCovariance
import TetraStereo.KernelOnly
set_option autoImplicit false

/-!
# Physical symmetry consequences for the actual sparse ring evaluator

The callback-covariance premise of the earlier physical theorem is discharged for the actual
retained operations and their equal sparse implementation. A calibrated proper transposition
forces refusal; a calibrated mirror transposition excludes uppercase output. These statements
apply to both immediate-frame and distant-reference recursion. They do not assert that every
physically distinguishable centre succeeds, or that every mirror case produces a lowercase letter.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense
open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingActualCovariance
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedGenericMarkedRecalculation (frameAtoms?)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (involutive : ∀ a, (e : Equiv.Perm input.Atom) ((e : Equiv.Perm input.Atom) a) = a)
  (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)

include agreement admissible supported single involutive atomsPres in
/-- The contract now follows from the molecular automorphism and actual code. -/
theorem actual_covariant :
    Covariant mol (sparseOperations input mol) (relabelOf input (e : Equiv.Perm input.Atom)) :=
  sparseOperations_covariant input mol agreement admissible supported single
    ⟨(e : Equiv.Perm input.Atom), MultiCenterMolecule.Aut.mem_molAut (m := input.detectedMultiCenterMolecule) e⟩
    (symmetry_of_aut mol input agreement admissible supported e involutive atomsPres)

variable (c : input.detectedMultiCenterMolecule.Center)
  (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c)
  {i j : Fin 4} (ne : i ≠ j)
  (swapEq : input.detectedMultiCenterMolecule.ligandPermAt e c = Equiv.swap i j)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- Physical proper symmetry forces refusal by the actual sparse evaluator. -/
theorem assignCenter_none_of_proper
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = 1) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val = none :=
  assignCenter_none_of_physical_proper mol input agreement admissible supported single cfg e
    involutive atomsPres (actual_covariant input mol agreement admissible supported single e
      involutive atomsPres) c fixed ne swapEq calibrated proper

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- Physical mirror symmetry excludes an uppercase descriptor from the actual sparse evaluator. -/
theorem assignCenter_not_chiral_of_mirror
    (sense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = -1) (v : RS) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val ≠ some (.chiral v) :=
  assignCenter_not_chiral_of_physical_mirror mol input agreement admissible supported single cfg e
    involutive atomsPres (actual_covariant input mol agreement admissible supported single e
      involutive atomsPres) c fixed ne swapEq calibrated sense v

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- The distant-reference recursion also refuses under physical proper symmetry. -/
theorem distant_assignCenter_none_of_proper
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = 1) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val = none :=
  distant_assignCenter_none_of_physical_proper mol input agreement admissible supported single cfg e
    involutive atomsPres (actual_covariant input mol agreement admissible supported single e
      involutive atomsPres) c fixed ne swapEq calibrated proper

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- The distant-reference recursion also excludes uppercase output under physical mirror symmetry. -/
theorem distant_assignCenter_not_chiral_of_mirror
    (sense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = -1) (v : RS) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val ≠ some (.chiral v) :=
  distant_assignCenter_not_chiral_of_physical_mirror mol input agreement admissible supported single cfg e
    involutive atomsPres (actual_covariant input mol agreement admissible supported single e
      involutive atomsPres) c fixed ne swapEq calibrated sense v

end TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense.actual_covariant
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense.assignCenter_none_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense.assignCenter_not_chiral_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense.distant_assignCenter_none_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense.distant_assignCenter_not_chiral_of_mirror
