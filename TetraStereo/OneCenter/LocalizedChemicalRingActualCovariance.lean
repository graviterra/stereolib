import TetraStereo.OneCenter.LocalizedChemicalRingOrdinaryCovariance
import TetraStereo.OneCenter.LocalizedChemicalRingMarkedCovariance
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Covariance of the actual retained and sparse marked operations

This instantiates the operational contract used by the physical ring-symmetry theorems.
The proofs derive lookup, frame alignment, ordinary and promoted comparisons, sorting and
reference-population transport. Neither callback covariance nor successful ordering is a premise.
The raw input is admitted, agrees with the certified molecule, and is localized and single-bonded.
Rings and ring-duplicate occurrences are included. This is symmetry soundness, not completeness.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingActualCovariance
open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrdinaryCovariance LocalizedChemicalRingMarkedCovariance
open LocalizedMarkedRetainedPromotedOperations LocalizedMarkedRetainedSparsePromotedOperations

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
  (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))

include agreement admissible supported single sym

/-- Actual dense retained operations satisfy the full recursion covariance contract. -/
theorem operations_covariant :
    Covariant mol (operations input mol) (relabelOf input (e : Equiv.Perm input.Atom)) where
  ordinary := ordinary_covariant input mol agreement admissible supported single e sym
  marked := marked_covariant input mol agreement admissible supported single e sym

/-- The sparse implementation has the same contract by its proved equality to the dense one. -/
theorem sparseOperations_covariant :
    Covariant mol (sparseOperations input mol) (relabelOf input (e : Equiv.Perm input.Atom)) := by
  rw [sparseOperations_eq]
  exact operations_covariant input mol agreement admissible supported single e sym

end TetraStereo.OneCenter.LocalizedChemicalRingActualCovariance
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualCovariance.operations_covariant
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualCovariance.sparseOperations_covariant
