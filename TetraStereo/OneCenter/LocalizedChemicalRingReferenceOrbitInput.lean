import TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture
import TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-!
A 46-atom graph fixture for the reference-orbit diagnostic. The source JSON is
`s3-cfi-selected-history-natural-masses-46.json`, SHA256
`ec48f8f1551262f827c6bb20fea8a443a64baad5594518aadea95e4972af4eef`.
The exact compact renumbering is old 0 -> 0 and old k -> k-1 for 2 <= k <= 46;
there is no old atom 1. Thus old centers 0,3,4,5,27 become 0,2,3,4,26,
and old references 31,32 become 30,31. All edges have bond order one, charge is
zero, and the only explicit isotopes are B10, B11, O16 and O18.

Coordinates are explicit source data; their orientation calibration is not proved here.
Structural admission and the encoded valence table do not assert physical realizability,
a root key tie, an evaluator output, or a universal chemical counterexample.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput

open CertifiedLocalizedCIPInput
open LocalizedMarkedReachableConfigurations (Reached reached_child reached_root)

private def atom (z mass : Nat) (positive : 0 < z) (bounded : z <= 118) : SemanticAtom :=
  { element := ⟨z, positive, bounded⟩
    isotopeMassNumber? := if mass = 0 then none else some mass }
private def bond (a b : Nat) : RawBond := { source := a, target := b, kind := .single }
private def edge (a b : Nat) : SemanticInteraction :=
  { participants := [a, b], kind := .covalent 1 }

def mol : RawMolecule where
  atoms := [
    .aliphatic .C, .aliphatic .O, .aliphatic .C, .aliphatic .C, .aliphatic .C,
    .aliphatic .B, .aliphatic .B, .aliphatic .B, { element := .B, isotope? := some 10 }, { element := .B, isotope? := some 10 },
    { element := .B, isotope? := some 10 }, { element := .B, isotope? := some 11 }, { element := .B, isotope? := some 11 }, { element := .B, isotope? := some 11 }, .aliphatic .B,
    .aliphatic .B, .aliphatic .B, .aliphatic .B, .aliphatic .B, .aliphatic .B,
    .aliphatic .O, .aliphatic .O, .aliphatic .O, .aliphatic .O, .aliphatic .O,
    .aliphatic .O, .aliphatic .C, .aliphatic .B, { element := .O, isotope? := some 16 }, { element := .O, isotope? := some 16 },
    { element := .O, isotope? := some 18 }, { element := .O, isotope? := some 18 }, .aliphatic .B, .aliphatic .B, .aliphatic .B,
    .aliphatic .B, .aliphatic .B, .aliphatic .B, .aliphatic .B, .aliphatic .B,
    .aliphatic .B, .aliphatic .B, .aliphatic .B, .aliphatic .B, .aliphatic .B,
    .aliphatic .B]
  bonds := [
    bond 0 28, bond 0 29, bond 0 30, bond 0 31, bond 1 2, bond 1 26,
    bond 2 5, bond 2 6, bond 2 7, bond 3 14, bond 3 17, bond 3 18,
    bond 3 40, bond 4 15, bond 4 16, bond 4 19, bond 4 41, bond 5 8,
    bond 5 11, bond 6 9, bond 6 12, bond 7 10, bond 7 13, bond 8 14,
    bond 8 15, bond 9 16, bond 9 17, bond 10 18, bond 10 19, bond 11 22,
    bond 11 24, bond 12 20, bond 12 25, bond 13 21, bond 13 23, bond 14 20,
    bond 15 21, bond 16 22, bond 17 23, bond 18 24, bond 19 25, bond 26 27,
    bond 26 34, bond 26 35, bond 27 32, bond 27 33, bond 28 32, bond 29 33,
    bond 30 34, bond 31 35, bond 32 36, bond 33 37, bond 34 38, bond 35 39,
    bond 36 42, bond 36 43, bond 37 44, bond 37 45, bond 38 42, bond 38 44,
    bond 39 43, bond 39 45, bond 40 42, bond 40 45, bond 41 43, bond 41 44]
  neighborOrder := [
    [28, 29, 30, 31], [2, 26], [1, 5, 6, 7], [14, 17, 18, 40], [15, 16, 19, 41],
    [2, 8, 11], [2, 9, 12], [2, 10, 13], [5, 14, 15], [6, 16, 17],
    [7, 18, 19], [5, 22, 24], [6, 20, 25], [7, 21, 23], [3, 8, 20],
    [4, 8, 21], [4, 9, 22], [3, 9, 23], [3, 10, 24], [4, 10, 25],
    [12, 14], [13, 15], [11, 16], [13, 17], [11, 18],
    [12, 19], [1, 27, 34, 35], [26, 32, 33], [0, 32], [0, 33],
    [0, 34], [0, 35], [27, 28, 36], [27, 29, 37], [26, 30, 38],
    [26, 31, 39], [32, 42, 43], [33, 44, 45], [34, 42, 44], [35, 43, 45],
    [3, 42, 45], [4, 43, 44], [36, 38, 40], [36, 39, 41], [37, 38, 41],
    [37, 39, 40]]

def point (x y z : ℚ) : CartesianPoint3 := ⟨x, y, z⟩
def positions : List CartesianPoint3 := [
    point 100 100 100, point 0 0 0, point 103 109 127, point 104 116 164,
    point 105 125 225, point 1 0 0, point 0 0 1, point 0 1 0,
    point 109 181 829, point 110 200 1100, point 111 221 1431, point 112 244 1828,
    point 113 269 2297, point 114 296 2844, point 10 10 10, point 20 20 20,
    point 21 20 20, point 11 10 10, point 10 10 11, point 20 21 20,
    point 121 541 9361, point 122 584 10748, point 123 629 12267, point 124 676 13924,
    point 125 725 15725, point 126 776 17676, point 127 829 19783, point 2 0 0,
    point 30 30 30, point 31 30 30, point 30 30 31, point 30 31 30,
    point 133 1189 36037, point 134 1256 39404, point 0 0 2, point 0 2 0,
    point 137 1469 50753, point 138 1544 54972, point 139 1621 59419, point 140 1700 64100,
    point 10 11 10, point 20 20 21, point 143 1949 79607, point 144 2036 85284,
    point 145 2125 91225, point 146 2216 97436]

def source : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [
    atom 6 0 (by decide) (by decide), atom 8 0 (by decide) (by decide), atom 6 0 (by decide) (by decide),
    atom 6 0 (by decide) (by decide), atom 6 0 (by decide) (by decide), atom 5 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide), atom 5 10 (by decide) (by decide),
    atom 5 10 (by decide) (by decide), atom 5 10 (by decide) (by decide), atom 5 11 (by decide) (by decide),
    atom 5 11 (by decide) (by decide), atom 5 11 (by decide) (by decide), atom 5 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide), atom 8 0 (by decide) (by decide),
    atom 8 0 (by decide) (by decide), atom 8 0 (by decide) (by decide), atom 8 0 (by decide) (by decide),
    atom 8 0 (by decide) (by decide), atom 8 0 (by decide) (by decide), atom 6 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide), atom 8 16 (by decide) (by decide), atom 8 16 (by decide) (by decide),
    atom 8 18 (by decide) (by decide), atom 8 18 (by decide) (by decide), atom 5 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide), atom 5 0 (by decide) (by decide),
    atom 5 0 (by decide) (by decide)]
      interactions := [
    edge 0 28, edge 0 29, edge 0 30, edge 0 31, edge 1 2, edge 1 26,
    edge 2 5, edge 2 6, edge 2 7, edge 3 14, edge 3 17, edge 3 18,
    edge 3 40, edge 4 15, edge 4 16, edge 4 19, edge 4 41, edge 5 8,
    edge 5 11, edge 6 9, edge 6 12, edge 7 10, edge 7 13, edge 8 14,
    edge 8 15, edge 9 16, edge 9 17, edge 10 18, edge 10 19, edge 11 22,
    edge 11 24, edge 12 20, edge 12 25, edge 13 21, edge 13 23, edge 14 20,
    edge 15 21, edge 16 22, edge 17 23, edge 18 24, edge 19 25, edge 26 27,
    edge 26 34, edge 26 35, edge 27 32, edge 27 33, edge 28 32, edge 29 33,
    edge 30 34, edge 31 35, edge 32 36, edge 33 37, edge 34 38, edge 35 39,
    edge 36 42, edge 36 43, edge 37 44, edge 37 45, edge 38 42, edge 38 44,
    edge 39 43, edge 39 45, edge 40 42, edge 40 45, edge 41 43, edge 41 44] }
  spatial? := some ⟨positions⟩
  diagram? := some mol.toDiagramConfiguration

theorem source_wellFormed : source.structurallyWellFormed? = true := by decide +kernel

theorem source_ready : source.molecule.localizedCIPGraphReady? = true := by decide +kernel

def certified : CertifiedLocalizedCIPInput where
  certified := ⟨source, source.structurallyWellFormed?_eq_true_iff.mp source_wellFormed⟩
  graphReady := source.molecule.localizedCIPGraphReady?_eq_true_iff.mp source_ready

theorem structure_agreement : mol.AuthoritativeStructureAgreement source := ⟨rfl, rfl⟩

theorem admissible : mol.StereochemicalAdmissible :=
  mol.stereochemicalAdmissible?_eq_true_iff.mp (by decide +kernel)

theorem valence_table : mol.ValenceOK := mol.valenceOK?_eq_true_iff.mp (by decide +kernel)

theorem supported : ∀ b ∈ mol.bonds, b.kind.IsLocalizedCovalent := by
  intro b member
  simp only [mol, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨1, rfl⟩

abbrev graph : MoleculeGraph (Fin 46) := certified.moleculeGraph
noncomputable abbrev physical := certified.detectedMultiCenterMolecule

theorem single_bonded : graph.SimpleBonded := by
  intro a
  fin_cases a <;> decide +kernel

theorem constant_charge (a : Fin 46) : graph.formalCharge a = 0 := by fin_cases a <;> rfl

theorem detected_inventory : graph.tetrahedralCenterSet = ({0, 2, 3, 4, 26} : Finset (Fin 46)) := by
  ext a
  rw [graph.mem_tetrahedralCenterSet, graph.isTetrahedralCenter_iff_neighborFinset_card]
  fin_cases a <;> decide +kernel

def originalPath : List (Fin 46) := [0, 28, 32, 27, 26, 1, 2]
def shortcutPath : List (Fin 46) := [0, 28, 32, 27, 26, 34, 38, 42, 40, 3, 14, 8, 5, 2]
def reference : Fin 46 := 30

def nodeOf (path : List Nat) : RawMolecule.CanonicalBranchNode :=
  { atom := path.getLast?.getD 0
    parent := path.dropLast.getLast?.getD 0
    history := path.reverse
    provenance := .realAtom }

def originalNode : RawMolecule.CanonicalBranchNode := nodeOf (originalPath.map Fin.val)
def shortcutNode : RawMolecule.CanonicalBranchNode := nodeOf (shortcutPath.map Fin.val)

private def originalRoute (n : Nat) := nodeOf ((originalPath.map Fin.val).take (n + 1))
private def shortcutRoute (n : Nat) := nodeOf ((shortcutPath.map Fin.val).take (n + 1))

private theorem reached_along (route : Nat → RawMolecule.CanonicalBranchNode) (n : Nat)
    (initial : Reached mol (route 0))
    (edges : ∀ k < n, route (k + 1) ∈ mol.canonicalChildren (route k)) :
    Reached mol (route n) := by
  have all : ∀ k, k <= n → Reached mol (route k) := by
    intro k
    induction k with
    | zero => intro _; exact initial
    | succ k ih =>
        intro bound
        exact reached_child mol (route k) (route (k + 1)) (ih (by omega))
          (edges k (by omega))
  exact all n le_rfl

private theorem original_edges (i : Fin 6) :
    originalRoute (i.val + 1) ∈ mol.canonicalChildren (originalRoute i.val) := by
  fin_cases i <;> decide +kernel

private theorem shortcut_edges (i : Fin 13) :
    shortcutRoute (i.val + 1) ∈ mol.canonicalChildren (shortcutRoute i.val) := by
  fin_cases i <;> decide +kernel

theorem original_reached : Reached mol originalNode :=
  reached_along originalRoute 6 (reached_root mol 0 (by decide))
    (fun k bound => original_edges ⟨k, bound⟩)

theorem shortcut_reached : Reached mol shortcutNode :=
  reached_along shortcutRoute 13 (reached_root mol 0 (by decide))
    (fun k bound => shortcut_edges ⟨k, bound⟩)

theorem raw_histories :
    originalNode.history = (originalPath.map Fin.val).reverse ∧
    shortcutNode.history = (shortcutPath.map Fin.val).reverse ∧
    originalNode.atom = 2 ∧ shortcutNode.atom = 2 ∧
    originalNode.parent = 1 ∧ shortcutNode.parent = 5 := by decide +kernel

theorem path_simple : originalPath.Nodup ∧ shortcutPath.Nodup := by decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.source_wellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.source_ready
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.structure_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.admissible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.valence_table
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.supported
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.single_bonded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.constant_charge
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.detected_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.original_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.shortcut_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.raw_histories
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput.path_simple
