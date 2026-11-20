import TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture
import TetraStereo.OneCenter.LocalizedMarkedRetainedSparsePromotedOperations
import TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! A detected root with two threefold-symmetric cyclic branches. Its actual raw and certified
input has 25 atoms and centers 0, 3 and 14. The two spatial inputs differ only by exchanging
the coordinates of two neighbors of center 14. No auxiliary labels or comparison keys are
supplied. Structural admission/valence checks do not assert chemical realizability. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input

open CertifiedLocalizedCIPInput CartesianPoint3
private def atom (z : Nat) (positive : 0 < z) (bounded : z ≤ 118) : SemanticAtom :=
  { element := ⟨z, positive, bounded⟩ }
private def bond (a b : Nat) : RawBond := { source := a, target := b, kind := .single }
private def edge (a b : Nat) : SemanticInteraction :=
  { participants := [a, b], kind := .covalent 1 }

def mol : RawMolecule where
  atoms := [
    .aliphatic .C, .aliphatic .H, .aliphatic .Cl, .aliphatic .C,
    .aliphatic .O, .aliphatic .B, .aliphatic .B, .aliphatic .B,
    .aliphatic .O, .aliphatic .O, .aliphatic .O, .aliphatic .S,
    .aliphatic .S, .aliphatic .S, .aliphatic .C, .aliphatic .O,
    .aliphatic .B, .aliphatic .B, .aliphatic .B, .aliphatic .O,
    .aliphatic .O, .aliphatic .O, .aliphatic .S, .aliphatic .S,
    .aliphatic .S]
  bonds := [
    bond 0 1, bond 0 2, bond 0 4, bond 0 15,
    bond 3 4, bond 3 5, bond 3 6, bond 3 7,
    bond 5 8, bond 8 11, bond 11 6, bond 6 9,
    bond 9 12, bond 12 7, bond 7 10, bond 10 13,
    bond 13 5, bond 14 15, bond 14 16, bond 14 17,
    bond 14 18, bond 16 19, bond 19 22, bond 22 17,
    bond 17 20, bond 20 23, bond 23 18, bond 18 21,
    bond 21 24, bond 24 16]
  neighborOrder := [
    [1, 2, 4, 15], [0], [0], [4, 5, 6, 7],
    [0, 3], [3, 8, 13], [3, 11, 9], [3, 12, 10],
    [5, 11], [6, 12], [7, 13], [8, 6],
    [9, 7], [10, 5], [15, 16, 17, 18], [0, 14],
    [14, 19, 24], [14, 22, 20], [14, 23, 21], [16, 22],
    [17, 23], [18, 24], [19, 17], [20, 18],
    [21, 16]]

def point (x y z : ℚ) : CartesianPoint3 := ⟨x, y, z⟩
def positions (opposite : Bool) : List CartesianPoint3 :=
  [point (-1) (-1) (-1), point 0 0 0, point 1 0 0,
   point 1 2 1, point 0 1 0, point 2 1 0, point 0 3 0, point 0 1 2,
   point 3 2 0, point 1 4 0, point 1 2 3, point 4 1 0, point 0 4 1, point 2 1 3,
   point 1 1 3, point 0 0 1, point 3 0 1,
   (if opposite then point 0 0 4 else point 0 3 1),
   (if opposite then point 0 3 1 else point 0 0 4),
   point 8 1 1, point 7 2 3, point 9 3 1, point 10 1 4, point 11 3 3, point 12 0 5]

def source (opposite : Bool) : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [
    atom 6 (by decide) (by decide), atom 1 (by decide) (by decide), atom 17 (by decide) (by decide), atom 6 (by decide) (by decide),
    atom 8 (by decide) (by decide), atom 5 (by decide) (by decide), atom 5 (by decide) (by decide), atom 5 (by decide) (by decide),
    atom 8 (by decide) (by decide), atom 8 (by decide) (by decide), atom 8 (by decide) (by decide), atom 16 (by decide) (by decide),
    atom 16 (by decide) (by decide), atom 16 (by decide) (by decide), atom 6 (by decide) (by decide), atom 8 (by decide) (by decide),
    atom 5 (by decide) (by decide), atom 5 (by decide) (by decide), atom 5 (by decide) (by decide), atom 8 (by decide) (by decide),
    atom 8 (by decide) (by decide), atom 8 (by decide) (by decide), atom 16 (by decide) (by decide), atom 16 (by decide) (by decide),
    atom 16 (by decide) (by decide)]
      interactions := [
    edge 0 1, edge 0 2, edge 0 4, edge 0 15,
    edge 3 4, edge 3 5, edge 3 6, edge 3 7,
    edge 5 8, edge 8 11, edge 11 6, edge 6 9,
    edge 9 12, edge 12 7, edge 7 10, edge 10 13,
    edge 13 5, edge 14 15, edge 14 16, edge 14 17,
    edge 14 18, edge 16 19, edge 19 22, edge 22 17,
    edge 17 20, edge 20 23, edge 23 18, edge 18 21,
    edge 21 24, edge 24 16] }
  spatial? := some ⟨positions opposite⟩
  diagram? := some mol.toDiagramConfiguration

theorem source_wellFormed (opposite : Bool) : (source opposite).structurallyWellFormed? = true := by
  cases opposite <;> decide +kernel
theorem source_ready (opposite : Bool) : (source opposite).molecule.localizedCIPGraphReady? = true := by
  cases opposite <;> decide +kernel

def certified (opposite : Bool) : CertifiedLocalizedCIPInput where
  certified := ⟨source opposite, (source opposite).structurallyWellFormed?_eq_true_iff.mp
    (source_wellFormed opposite)⟩
  graphReady := (source opposite).molecule.localizedCIPGraphReady?_eq_true_iff.mp
    (source_ready opposite)

theorem structure_agreement (opposite : Bool) :
    mol.AuthoritativeStructureAgreement (source opposite) := ⟨rfl, rfl⟩
theorem admissible : mol.StereochemicalAdmissible :=
  mol.stereochemicalAdmissible?_eq_true_iff.mp (by decide +kernel)
theorem valence_table : mol.ValenceOK := mol.valenceOK?_eq_true_iff.mp (by decide +kernel)

theorem supported : ∀ b ∈ mol.bonds, b.kind.IsLocalizedCovalent := by
  intro b member
  simp only [mol, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨1, rfl⟩

abbrev graph : MoleculeGraph (Fin 25) := (certified false).moleculeGraph
noncomputable abbrev physical := (certified false).detectedMultiCenterMolecule
theorem graph_opposite (opposite : Bool) : (certified opposite).moleculeGraph = graph := rfl

theorem single_bonded : graph.SimpleBonded := by
  intro a b adjacent
  fin_cases a <;> fin_cases b <;> first
    | exact absurd adjacent (by decide)
    | decide
theorem constant_charge (a : Fin 25) : graph.formalCharge a = 0 := by fin_cases a <;> rfl
theorem detected_inventory : graph.tetrahedralCenterSet = ({0, 3, 14} : Finset (Fin 25)) := by
  ext a
  fin_cases a <;> decide +kernel

def root : RawMolecule.CanonicalBranchNode := canonicalCenterRoot 0
def leftArm : RawMolecule.CanonicalBranchNode :=
  { atom := 4, parent := 0, history := [4, 0], provenance := .realAtom }
def rightArm : RawMolecule.CanonicalBranchNode :=
  { atom := 15, parent := 0, history := [15, 0], provenance := .realAtom }
def leftCenter : RawMolecule.CanonicalBranchNode :=
  { atom := 3, parent := 4, history := [3, 4, 0], provenance := .realAtom }
def rightCenter : RawMolecule.CanonicalBranchNode :=
  { atom := 14, parent := 15, history := [14, 15, 0], provenance := .realAtom }

theorem actual_children :
    leftArm ∈ mol.canonicalChildren root ∧ rightArm ∈ mol.canonicalChildren root ∧
    leftCenter ∈ mol.canonicalChildren leftArm ∧ rightCenter ∈ mol.canonicalChildren rightArm := by
  decide +kernel
theorem raw_frames :
    LocalizedGenericMarkedRecalculation.frameAtoms? mol root = some [1, 2, 4, 15] ∧
    LocalizedGenericMarkedRecalculation.frameAtoms? mol leftCenter = some [4, 5, 6, 7] ∧
    LocalizedGenericMarkedRecalculation.frameAtoms? mol rightCenter = some [15, 16, 17, 18] := by
  decide +kernel

def geom (opposite : Bool) : LocalizedGenericMarkedRecalculation.Geometry :=
  fun a => (positions opposite)[a]?
def ops (opposite : Bool) : LocalizedMarkedOperationEvaluator.Operations :=
  LocalizedMarkedRetainedSparsePromotedOperations.sparseOperations (certified opposite) mol

end TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.source_wellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.source_ready
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.structure_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.admissible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.valence_table
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.supported
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.graph_opposite
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.single_bonded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.constant_charge
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.detected_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.actual_children
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input.raw_frames
