import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations
import TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-!
# Actual retained-operation input for the symmetric three-center ring

The accepted nine-atom spatial molecule is given an exact raw input and its diagram channel.
Its three detected ring centers are constitutionally nonrigid. No descriptor labels are supplied.
This module states input facts only; executable observations and chemical correctness belong
to separate modules.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput

open LocalizedRecursiveCyclicSymmetricFixture

private def bond (a b : Nat) : RawBond := { source := a, target := b, kind := .single }

def mol : RawMolecule where
  atoms := [.aliphatic .C, .aliphatic .Cl, .aliphatic .C, .aliphatic .Cl, .aliphatic .C,
    .aliphatic .H, .aliphatic .H, .aliphatic .H, .aliphatic .Cl]
  bonds := [bond 0 1, bond 0 2, bond 0 4, bond 0 5, bond 2 3, bond 2 4,
    bond 2 6, bond 4 7, bond 4 8]
  neighborOrder := [[1, 2, 4, 5], [0], [0, 3, 4, 6], [2], [0, 2, 7, 8],
    [0], [2], [4], [4]]

def source : AuthoritativeChemicalInput :=
  { symmetricSource with diagram? := some mol.toDiagramConfiguration }

theorem source_wellFormed : source.structurallyWellFormed? = true := by decide +kernel

def certified : CertifiedLocalizedCIPInput where
  certified :=
    { input := source
      structurallyWellFormed :=
        (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp source_wellFormed }
  graphReady := symmetricCertified.graphReady

theorem structure_agreement : mol.AuthoritativeStructureAgreement source := by
  constructor
  · rfl
  · rfl

theorem admissible : mol.StereochemicalAdmissible :=
  mol.stereochemicalAdmissible?_eq_true_iff.mp (by decide +kernel)

theorem supported : ∀ edge ∈ mol.bonds, edge.kind.IsLocalizedCovalent := by
  intro edge member
  simp only [mol, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨1, rfl⟩

theorem graph_eq : certified.moleculeGraph = symmetricCertified.moleculeGraph := rfl

theorem single_bonded : certified.moleculeGraph.SimpleBonded := simple_bonded

theorem detected_inventory : certified.tetrahedralCenterSet =
    ({0, 2, 4} : Finset (Fin 9)) :=
  LocalizedRecursiveCyclicSymmetricFixture.detected_inventory

def geom : LocalizedGenericMarkedRecalculation.Geometry := fun atom => positions[atom]?

def ops : LocalizedMarkedOperationEvaluator.Operations :=
  LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations certified mol

def root : RawMolecule.CanonicalBranchNode := canonicalCenterRoot 0

def arm2 : RawMolecule.CanonicalBranchNode :=
  { atom := 2, parent := 0, history := [2, 0], provenance := .realAtom }

def arm4 : RawMolecule.CanonicalBranchNode :=
  { atom := 4, parent := 0, history := [4, 0], provenance := .realAtom }

theorem root_children : arm2 ∈ mol.canonicalChildren root ∧ arm4 ∈ mol.canonicalChildren root := by
  decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput.structure_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput.admissible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput.supported
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput.graph_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput.single_bonded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput.detected_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput.root_children
