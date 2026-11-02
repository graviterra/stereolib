import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.OneCenter.LocalizedPublicChildEnumeration
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

































































namespace TetraStereo.OneCenter.EarlierRuleRankWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## The concrete periodic elements and atoms -/

/-- A checked element spelling. -/
def periodicElement (atomicNumber : Nat) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

def hydrogenElement : PeriodicElement := periodicElement 1 (by decide) (by decide)
def carbonElement : PeriodicElement := periodicElement 6 (by decide) (by decide)
def fluorineElement : PeriodicElement := periodicElement 9 (by decide) (by decide)

/-- A neutral, unlabelled, closed-shell atom. -/
def neutralAtom (element : PeriodicElement) : SemanticAtom := { element := element }

def hydrogenAtom : SemanticAtom := neutralAtom hydrogenElement
def carbonAtom : SemanticAtom := neutralAtom carbonElement
def fluorineAtom : SemanticAtom := neutralAtom fluorineElement

/-- One ordinary single bond. -/
def singleBond (left right : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent 1 }

/-! ## The 23-atom source molecule -/

def sourceMolecule : SemanticMolecule where
  atoms :=
    [ carbonAtom,      -- 0  central carbon
      carbonAtom,      -- 1  branch A root
      carbonAtom,      -- 2  branch A methyl
      carbonAtom,      -- 3  branch A methyl
      hydrogenAtom,    -- 4  branch A root hydrogen
      hydrogenAtom,    -- 5  methyl 2 hydrogen
      hydrogenAtom,    -- 6  methyl 2 hydrogen
      hydrogenAtom,    -- 7  methyl 2 hydrogen
      hydrogenAtom,    -- 8  methyl 3 hydrogen
      hydrogenAtom,    -- 9  methyl 3 hydrogen
      hydrogenAtom,    -- 10 methyl 3 hydrogen
      carbonAtom,      -- 11 branch B root
      carbonAtom,      -- 12 branch B methyl
      carbonAtom,      -- 13 branch B methyl
      hydrogenAtom,    -- 14 branch B root hydrogen
      hydrogenAtom,    -- 15 methyl 12 hydrogen
      hydrogenAtom,    -- 16 methyl 12 hydrogen
      hydrogenAtom,    -- 17 methyl 12 hydrogen
      hydrogenAtom,    -- 18 methyl 13 hydrogen
      hydrogenAtom,    -- 19 methyl 13 hydrogen
      hydrogenAtom,    -- 20 methyl 13 hydrogen
      hydrogenAtom,    -- 21 central hydrogen
      fluorineAtom ]   -- 22 central fluorine
  interactions :=
    [ singleBond 0 1, singleBond 0 11, singleBond 0 21, singleBond 0 22,
      singleBond 1 2, singleBond 1 3, singleBond 1 4,
      singleBond 2 5, singleBond 2 6, singleBond 2 7,
      singleBond 3 8, singleBond 3 9, singleBond 3 10,
      singleBond 11 12, singleBond 11 13, singleBond 11 14,
      singleBond 12 15, singleBond 12 16, singleBond 12 17,
      singleBond 13 18, singleBond 13 19, singleBond 13 20 ]

def source : AuthoritativeChemicalInput := { molecule := sourceMolecule }

theorem source_structurallyWellFormed : source.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by
    decide +kernel)

theorem source_graphReady : source.molecule.LocalizedCIPGraphReady :=
  (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff source.molecule).mp (by
    decide +kernel)

/-- The actual certified localized input. -/
def input : CertifiedLocalizedCIPInput where
  certified :=
    { input := source
      structurallyWellFormed := source_structurallyWellFormed }
  graphReady := source_graphReady

theorem input_atomCount : input.certified.input.molecule.atomCount = 23 := rfl

/-- Every atom of the input is a literal `Fin 23`. -/
abbrev Atom : Type := Fin 23

def a0 : Atom := ⟨0, by decide⟩
def a1 : Atom := ⟨1, by decide⟩
def a2 : Atom := ⟨2, by decide⟩
def a3 : Atom := ⟨3, by decide⟩
def a4 : Atom := ⟨4, by decide⟩
def a5 : Atom := ⟨5, by decide⟩
def a6 : Atom := ⟨6, by decide⟩
def a7 : Atom := ⟨7, by decide⟩
def a8 : Atom := ⟨8, by decide⟩
def a9 : Atom := ⟨9, by decide⟩
def a10 : Atom := ⟨10, by decide⟩
def a11 : Atom := ⟨11, by decide⟩
def a12 : Atom := ⟨12, by decide⟩
def a13 : Atom := ⟨13, by decide⟩
def a14 : Atom := ⟨14, by decide⟩
def a15 : Atom := ⟨15, by decide⟩
def a16 : Atom := ⟨16, by decide⟩
def a17 : Atom := ⟨17, by decide⟩
def a18 : Atom := ⟨18, by decide⟩
def a19 : Atom := ⟨19, by decide⟩
def a20 : Atom := ⟨20, by decide⟩
def a21 : Atom := ⟨21, by decide⟩
def a22 : Atom := ⟨22, by decide⟩

/-! ## Single bonds -/

theorem simpleBonded : input.moleculeGraph.SimpleBonded := by
  intro u v adjacent
  fin_cases u <;> fin_cases v <;> revert adjacent <;> decide +kernel

/-! ## A height grading and a parent map -/

/-- Distance from the central carbon in the intended tree. -/
def treeHeight (a : Atom) : Nat :=
  match a.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | 10 => 3
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 3
  | 19 => 3
  | 20 => 3
  | _ => 1

/-- The neighbour of one smaller height along the intended tree. -/
def treeParent (a : Atom) : Atom :=
  match a.val with
  | 0 => a0
  | 1 => a0
  | 2 => a1
  | 3 => a1
  | 4 => a1
  | 5 => a2
  | 6 => a2
  | 7 => a2
  | 8 => a3
  | 9 => a3
  | 10 => a3
  | 11 => a0
  | 12 => a11
  | 13 => a11
  | 14 => a11
  | 15 => a12
  | 16 => a12
  | 17 => a12
  | 18 => a13
  | 19 => a13
  | 20 => a13
  | _ => a0

/-- The full finite edge/height table: an adjacent pair either increases the height by one, or the
lower member is exactly the parent of the higher member. -/
theorem adj_height_case {u v : Atom} (h : input.moleculeGraph.Adj u v) :
    treeHeight u + 1 = treeHeight v ∨
      (treeHeight v + 1 = treeHeight u ∧ v = treeParent u) := by
  revert h
  fin_cases u <;> fin_cases v <;> decide +kernel

theorem treeHeight_adj {u v : Atom} (h : input.moleculeGraph.Adj u v) :
    treeHeight u + 1 = treeHeight v ∨ treeHeight v + 1 = treeHeight u := by
  rcases adj_height_case h with forward | ⟨backward, _⟩
  · exact Or.inl forward
  · exact Or.inr backward

theorem eq_treeParent_of_lower {u v : Atom} (h : input.moleculeGraph.Adj u v)
    (step : treeHeight v + 1 = treeHeight u) : v = treeParent u := by
  rcases adj_height_case h with forward | ⟨_, parent⟩
  · omega
  · exact parent

theorem treeHeight_unique_lower (u v w : Atom) (hv : input.moleculeGraph.Adj u v)
    (hw : input.moleculeGraph.Adj u w) (pv : treeHeight v + 1 = treeHeight u)
    (pw : treeHeight w + 1 = treeHeight u) : v = w := by
  rw [eq_treeParent_of_lower hv pv, eq_treeParent_of_lower hw pw]

/-! ## Acyclicity from the height grading -/

/-- A cycle walk based at `u` has two distinct incident edges whose other endpoints occur on the
walk. -/
theorem exists_two_cycle_adjacent {X : Type*} {G : SimpleGraph X} {u : X} {c : G.Walk u u}
    (hc : c.IsCycle) :
    ∃ a b : X, a ≠ b ∧ G.Adj u a ∧ G.Adj u b ∧ a ∈ c.support ∧ b ∈ c.support := by
  have hlen : 3 ≤ c.length := SimpleGraph.Walk.IsCycle.three_le_length hc
  refine ⟨c.getVert 1, c.getVert (c.length - 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro equal
    have h1 : 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
      simp only [Set.mem_setOf_eq]; omega
    have h2 : c.length - 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
      simp only [Set.mem_setOf_eq]; omega
    have same : 1 = c.length - 1 := SimpleGraph.Walk.IsCycle.getVert_injOn hc h1 h2 equal
    omega
  · have step := SimpleGraph.Walk.adj_getVert_succ c (i := 0) (by omega)
    simpa using step
  · have step := SimpleGraph.Walk.adj_getVert_succ c (i := c.length - 1) (by omega)
    have hlast : c.getVert (c.length - 1 + 1) = u := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ c.length)]
      exact SimpleGraph.Walk.getVert_length c
    have backward : G.Adj (c.getVert (c.length - 1)) u := by
      simpa [hlast] using step
    exact G.symm backward
  · exact SimpleGraph.Walk.getVert_mem_support c 1
  · exact SimpleGraph.Walk.getVert_mem_support c (c.length - 1)

/-- If heights change by one along edges and every vertex of positive height has at most one lower
neighbour, there is no cycle: a maximum-height vertex of a cycle would have two distinct lower
cycle-neighbours. -/
theorem isAcyclic_of_height_unique_lower {X : Type*} [DecidableEq X]
    {G : SimpleGraph X} (height : X → Nat)
    (adjStep : ∀ {u v}, G.Adj u v → height u + 1 = height v ∨ height v + 1 = height u)
    (uniqueLower : ∀ u v w, G.Adj u v → G.Adj u w →
      height v + 1 = height u → height w + 1 = height u → v = w) :
    G.IsAcyclic := by
  intro u c hc
  classical
  let s : Finset X := c.support.toFinset
  have hs : s.Nonempty := ⟨u, by simp [s]⟩
  obtain ⟨w, hwmem, hwmax⟩ := Finset.exists_mem_eq_sup s hs height
  have hwSupport : w ∈ c.support := by simpa [s] using hwmem
  have hmax : ∀ x ∈ s, height x ≤ height w := by
    intro x hx
    calc height x ≤ s.sup height := Finset.le_sup hx
      _ = height w := hwmax
  have rotatedCycle : (c.rotate hwSupport).IsCycle := hc.rotate hwSupport
  obtain ⟨a, b, hab, hwa, hwb, haMem, hbMem⟩ :=
    exists_two_cycle_adjacent rotatedCycle
  have haSupport : a ∈ c.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c hwSupport]
    exact haMem
  have hbSupport : b ∈ c.support := by
    rw [← SimpleGraph.Walk.mem_support_rotate_iff c hwSupport]
    exact hbMem
  have haMemS : a ∈ s := by simpa [s] using haSupport
  have hbMemS : b ∈ s := by simpa [s] using hbSupport
  have haLower : height a + 1 = height w := by
    rcases adjStep hwa with up | down
    · have bound := hmax a haMemS
      omega
    · exact down
  have hbLower : height b + 1 = height w := by
    rcases adjStep hwb with up | down
    · have bound := hmax b hbMemS
      omega
    · exact down
  exact hab (uniqueLower w a b hwa hwb haLower hbLower)

theorem acyclic : input.moleculeGraph.Acyclic := by
  unfold MoleculeGraph.Acyclic
  exact isAcyclic_of_height_unique_lower treeHeight
    (fun {u v} h => treeHeight_adj h)
    treeHeight_unique_lower

end TetraStereo.OneCenter.EarlierRuleRankWitness

assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.source
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.source_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.source_graphReady
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.input
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.input_atomCount
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.simpleBonded
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.treeHeight
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.treeParent
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.adj_height_case
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.treeHeight_adj
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.eq_treeParent_of_lower
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.treeHeight_unique_lower
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.exists_two_cycle_adjacent
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.isAcyclic_of_height_unique_lower
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.acyclic

namespace TetraStereo.OneCenter.EarlierRuleRankWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## Exact sorted neighbour lists

`Finset.sort` is `Multiset.sort`, a `Quot.liftOn` that the kernel does not unfold.  Every executable
occurrence enumeration below is therefore rewritten through an explicit sorted list, proved from
the sort-free `List.toFinset_sort` characterisation.  The bond orders themselves are ordinary
finite computations. -/

theorem sort_of_toFinset_eq (a : Atom) (l : List Atom)
    (hset : l.toFinset = input.moleculeGraph.neighborFinset a)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (input.moleculeGraph.neighborFinset a).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- The sorted neighbour list of every atom of the fixture, as a `match` on the atom value so that
it rewrites uniformly inside executable enumeration terms. -/
theorem neighborSort_eq (a : Atom) :
    (input.moleculeGraph.neighborFinset a).sort (· ≤ ·) =
      match a.val with
      | 0 => [a1, a11, a21, a22]
      | 1 => [a0, a2, a3, a4]
      | 2 => [a1, a5, a6, a7]
      | 3 => [a1, a8, a9, a10]
      | 4 => [a1]
      | 5 => [a2]
      | 6 => [a2]
      | 7 => [a2]
      | 8 => [a3]
      | 9 => [a3]
      | 10 => [a3]
      | 11 => [a0, a12, a13, a14]
      | 12 => [a11, a15, a16, a17]
      | 13 => [a11, a18, a19, a20]
      | 14 => [a11]
      | 15 => [a12]
      | 16 => [a12]
      | 17 => [a12]
      | 18 => [a13]
      | 19 => [a13]
      | 20 => [a13]
      | 21 => [a0]
      | _ => [a0] := by
  fin_cases a
  · exact sort_of_toFinset_eq a0 [a1, a11, a21, a22]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a1 [a0, a2, a3, a4]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a2 [a1, a5, a6, a7]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a3 [a1, a8, a9, a10]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a4 [a1]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a5 [a2]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a6 [a2]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a7 [a2]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a8 [a3]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a9 [a3]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a10 [a3]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a11 [a0, a12, a13, a14]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a12 [a11, a15, a16, a17]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a13 [a11, a18, a19, a20]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a14 [a11]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a15 [a12]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a16 [a12]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a17 [a12]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a18 [a13]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a19 [a13]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a20 [a13]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a21 [a0]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq a22 [a0]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)

/-! ## The exact detected degree-four inventory -/

theorem tetrahedralCenterSet_eq :
    (input.tetrahedralCenterSet : Finset Atom) =
      {a0, a1, a2, a3, a11, a12, a13} := by
  decide +kernel

theorem mem_tetrahedralCenterSet_iff (a : Atom) :
    a ∈ input.tetrahedralCenterSet ↔
      a = a0 ∨ a = a1 ∨ a = a2 ∨ a = a3 ∨ a = a11 ∨ a = a12 ∨ a = a13 := by
  fin_cases a <;> decide +kernel

theorem neighborFinset_card_eq_four (a : Atom)
    (detected : a ∈ input.tetrahedralCenterSet) :
    (input.moleculeGraph.neighborFinset a).card = 4 :=
  (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card a).mp
    ((input.moleculeGraph.mem_tetrahedralCenterSet a).mp detected)

/-- The detected central carbon `0`. -/
def center : input.TetrahedralCenter :=
  ⟨a0, by rw [mem_tetrahedralCenterSet_iff]; exact Or.inl rfl⟩

theorem center_val : center.1 = a0 := rfl

/-! ## The canonical ligand enumeration of the central carbon -/

theorem canonicalNeighborList_center :
    input.canonicalNeighborList center = [a1, a11, a21, a22] := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  rw [neighborSort_eq]
  rfl

theorem canonicalLigandAtom_center_zero : input.canonicalLigandAtom center 0 = a1 := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList_center]

theorem canonicalLigandAtom_center_one : input.canonicalLigandAtom center 1 = a11 := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList_center]

theorem canonicalLigandAtom_center_two : input.canonicalLigandAtom center 2 = a21 := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList_center]

theorem canonicalLigandAtom_center_three : input.canonicalLigandAtom center 3 = a22 := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList_center]

/-! ## The official nodes of the two sibling ligand subtrees

`node0` is the top occurrence node at the central carbon `0`.  `node1`/`node11` are its two
carbon children, i.e. exactly the canonical ligand roots `a1` and `a11`.  The remaining nodes are
their methyl and hydrogen descendants. -/

def node0 : OfficialCIPNode Atom := OfficialCIPNode.root a0
def node1 : OfficialCIPNode Atom := node0.extend a1 0
def node2 : OfficialCIPNode Atom := node1.extend a2 0
def node3 : OfficialCIPNode Atom := node1.extend a3 0
def node4 : OfficialCIPNode Atom := node1.extend a4 0
def node5 : OfficialCIPNode Atom := node2.extend a5 0
def node6 : OfficialCIPNode Atom := node2.extend a6 0
def node7 : OfficialCIPNode Atom := node2.extend a7 0
def node8 : OfficialCIPNode Atom := node3.extend a8 0
def node9 : OfficialCIPNode Atom := node3.extend a9 0
def node10 : OfficialCIPNode Atom := node3.extend a10 0
def node11 : OfficialCIPNode Atom := node0.extend a11 0
def node12 : OfficialCIPNode Atom := node11.extend a12 0
def node13 : OfficialCIPNode Atom := node11.extend a13 0
def node14 : OfficialCIPNode Atom := node11.extend a14 0
def node15 : OfficialCIPNode Atom := node12.extend a15 0
def node16 : OfficialCIPNode Atom := node12.extend a16 0
def node17 : OfficialCIPNode Atom := node12.extend a17 0
def node18 : OfficialCIPNode Atom := node13.extend a18 0
def node19 : OfficialCIPNode Atom := node13.extend a19 0
def node20 : OfficialCIPNode Atom := node13.extend a20 0

/-! ## Exact executable child lists -/

theorem children_node0 :
    input.executableOfficialCIPChildren node0 =
      [node1, node11, node0.extend a21 0, node0.extend a22 0] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node1 :
    input.executableOfficialCIPChildren node1 = [node2, node3, node4] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node2 :
    input.executableOfficialCIPChildren node2 = [node5, node6, node7] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node2, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node3 :
    input.executableOfficialCIPChildren node3 = [node8, node9, node10] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node3, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node11 :
    input.executableOfficialCIPChildren node11 = [node12, node13, node14] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node12 :
    input.executableOfficialCIPChildren node12 = [node15, node16, node17] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node12, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node13 :
    input.executableOfficialCIPChildren node13 = [node18, node19, node20] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node13, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node4 : input.executableOfficialCIPChildren node4 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node4, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node5 : input.executableOfficialCIPChildren node5 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node5, node2, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node6 : input.executableOfficialCIPChildren node6 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node6, node2, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node7 : input.executableOfficialCIPChildren node7 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node7, node2, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node8 : input.executableOfficialCIPChildren node8 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node8, node3, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node9 : input.executableOfficialCIPChildren node9 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node9, node3, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node10 : input.executableOfficialCIPChildren node10 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node10, node3, node1, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node14 : input.executableOfficialCIPChildren node14 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node14, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node15 : input.executableOfficialCIPChildren node15 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node15, node12, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node16 : input.executableOfficialCIPChildren node16 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node16, node12, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node17 : input.executableOfficialCIPChildren node17 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node17, node12, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node18 : input.executableOfficialCIPChildren node18 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node18, node13, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node19 : input.executableOfficialCIPChildren node19 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node19, node13, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem children_node20 : input.executableOfficialCIPChildren node20 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node20, node13, node11, node0, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

end TetraStereo.OneCenter.EarlierRuleRankWitness

assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.sort_of_toFinset_eq
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.neighborSort_eq
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.tetrahedralCenterSet_eq
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.mem_tetrahedralCenterSet_iff
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.neighborFinset_card_eq_four
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.center
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.center_val
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.canonicalNeighborList_center
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.canonicalLigandAtom_center_zero
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.canonicalLigandAtom_center_one
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.canonicalLigandAtom_center_two
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.canonicalLigandAtom_center_three
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.node0
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node0
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node1
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node2
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node3
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node4
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node5
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node6
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node7
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node8
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node9
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node10
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node11
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node12
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node13
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node14
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node15
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node16
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node17
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node18
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node19
assert_kernel_only TetraStereo.OneCenter.EarlierRuleRankWitness.children_node20
