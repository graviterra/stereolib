import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceSelection
import TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.LocalizedPhysicalDomainReindexing
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
































































namespace TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.AcyclicCutBranchAutomorphism

/-! ## Elements, atoms, bonds, and the source molecule -/

/-- Checked periodic-table element spelling. -/
def periodicElement (atomicNumber : Nat) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

def carbon : PeriodicElement := periodicElement 6 (by decide) (by decide)
def hydrogen : PeriodicElement := periodicElement 1 (by decide) (by decide)
def fluorine : PeriodicElement := periodicElement 9 (by decide) (by decide)
def chlorine : PeriodicElement := periodicElement 17 (by decide) (by decide)
def bromine : PeriodicElement := periodicElement 35 (by decide) (by decide)
def iodine : PeriodicElement := periodicElement 53 (by decide) (by decide)

/-- A neutral, unlabelled atom of one element. -/
def atom (element : PeriodicElement) : SemanticAtom := { element := element }

/-- One ordinary single bond. -/
def singleBond (left right : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent 1 }

/-- Eleven-atom fixture:

`0` root carbon, `1` and `2` the carbon arms, `3 = H`, `4 = F`, `5 = Cl` on arm `1`,
`6 = H`, `7 = F`, `8 = Cl` on arm `2`, and `9 = Br`, `10 = I` on the root. -/
def source : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [carbon, carbon, carbon, hydrogen, fluorine, chlorine, hydrogen, fluorine,
            chlorine, bromine, iodine].map atom
        interactions :=
          [singleBond 0 1, singleBond 0 2, singleBond 0 9, singleBond 0 10,
            singleBond 1 3, singleBond 1 4, singleBond 1 5,
            singleBond 2 6, singleBond 2 7, singleBond 2 8] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 },
       { x := 1, y := 0, z := 0 },
       { x := -1, y := 0, z := 0 },
       { x := 2, y := 1, z := 0 },
       { x := 2, y := 0, z := 1 },
       { x := 2, y := -1, z := -1 },
       { x := -2, y := 1, z := 0 },
       { x := -2, y := 0, z := 1 },
       { x := -2, y := -1, z := -1 },
       { x := 0, y := 1, z := 1 },
       { x := 0, y := -1, z := 1 }] } }

/-! ## Admission through the actual pipeline -/

theorem source_structurallyWellFormed :
    source.structurallyWellFormed? = true := by
  decide +kernel

theorem source_localizedGraphReady :
    source.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

theorem source_noDoubleTest :
    source.molecule.noLocalizedDoubleBondRecords? = true := by
  decide +kernel

theorem source_noDoubleRecords :
    source.molecule.NoLocalizedDoubleBondRecords :=
  (source.molecule.noLocalizedDoubleBondRecords?_eq_true_iff).mp source_noDoubleTest

def certifiedSource : CertifiedAuthoritativeChemicalInput :=
  { input := source
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
        source_structurallyWellFormed }

def localizedSource : CertifiedLocalizedCIPInput :=
  { certified := certifiedSource
    graphReady :=
      (certifiedSource.input.molecule.localizedCIPGraphReady?_eq_true_iff).mp
        source_localizedGraphReady }

/-- The actual runtime input of the localized universal reference pipeline. -/
def input : LocalizedUniversalReference.Input :=
  { certified := localizedSource }

/-- **Admission.**  The real `admitSource?` pipeline returns exactly the constructed input. -/
theorem admission : LocalizedUniversalReference.admitSource? source = some input := rfl

theorem input_noDoubleRecords :
    input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords := by
  simpa using source_noDoubleRecords

/-! ## The certified graph and its atom indices -/

abbrev Atom : Type := input.certified.Atom

abbrev graph : MoleculeGraph Atom := input.certified.moleculeGraph

def atom0 : Atom := ⟨0, by decide⟩
def atom1 : Atom := ⟨1, by decide⟩
def atom2 : Atom := ⟨2, by decide⟩
def atom3 : Atom := ⟨3, by decide⟩
def atom4 : Atom := ⟨4, by decide⟩
def atom5 : Atom := ⟨5, by decide⟩
def atom6 : Atom := ⟨6, by decide⟩
def atom7 : Atom := ⟨7, by decide⟩
def atom8 : Atom := ⟨8, by decide⟩
def atom9 : Atom := ⟨9, by decide⟩
def atom10 : Atom := ⟨10, by decide⟩

/-- Ligand enumeration at the root (slots: arm 1, arm 2, Br, I). -/
def rootLigand (i : Fin 4) : Atom :=
  match i.val with
  | 0 => atom1
  | 1 => atom2
  | 2 => atom9
  | _ => atom10

/-- Ligand enumeration at the first carbon arm (slots: root, H, F, Cl). -/
def armOneLigand (i : Fin 4) : Atom :=
  match i.val with
  | 0 => atom0
  | 1 => atom3
  | 2 => atom4
  | _ => atom5

/-- Ligand enumeration at the second carbon arm (slots: root, H, F, Cl). -/
def armTwoLigand (i : Fin 4) : Atom :=
  match i.val with
  | 0 => atom0
  | 1 => atom6
  | 2 => atom7
  | _ => atom8

/-- The ligand table of the explicit multi-center molecule.  It ignores its membership proof,
so all concrete computations are independent of proof irrelevance. -/
def ligandAt (c : Atom) (i : Fin 4) : Atom :=
  if c.1 = 0 then rootLigand i
  else if c.1 = 1 then armOneLigand i
  else if c.1 = 2 then armTwoLigand i
  else atom0

/-- The explicit multi-center molecule: the certified graph and exactly the three carbon
candidates, with the ligand tables above. -/
def m : MultiCenterMolecule Atom where
  mol := graph
  centers := {atom0, atom1, atom2}
  ligandAtom := fun c _ i => ligandAt c i
  ligandAtom_adj := by decide +kernel
  ligandAtom_injective := by decide +kernel
  ligandAtom_surjective := by decide +kernel

/-- The physical root. -/
def root : m.Center := ⟨atom0, by decide⟩

/-- The first carbon arm as a center. -/
def armOneCenter : m.Center := ⟨atom1, by decide⟩

/-- The second carbon arm as a center. -/
def armTwoCenter : m.Center := ⟨atom2, by decide⟩

/-- **Exact detected candidates.**  The automatically detected tetrahedral candidates are
precisely the three carbons. -/
theorem tetrahedralCenterSet_eq :
    input.certified.tetrahedralCenterSet = {atom0, atom1, atom2} := by
  decide +kernel

/-- **Coverage.**  The explicit molecule's center inventory is exactly the automatically
detected candidate set. -/
theorem coverage : m.centers = input.certified.tetrahedralCenterSet := by
  rw [tetrahedralCenterSet_eq]
  rfl

/-! ## The exact graph structure -/

/-- Every atom is one of the eleven concrete indices. -/
theorem atom_eq (a : Atom) :
    a = atom0 ∨ a = atom1 ∨ a = atom2 ∨ a = atom3 ∨ a = atom4 ∨ a = atom5 ∨
      a = atom6 ∨ a = atom7 ∨ a = atom8 ∨ a = atom9 ∨ a = atom10 := by
  fin_cases a <;> simp [atom0, atom1, atom2, atom3, atom4, atom5, atom6, atom7, atom8,
    atom9, atom10]

/-- Exact adjacency of the certified graph.  This is the complete symmetric bond table. -/
theorem adj_iff (u v : Atom) :
    graph.Adj u v ↔
      (u = atom0 ∧ (v = atom1 ∨ v = atom2 ∨ v = atom9 ∨ v = atom10)) ∨
      (v = atom0 ∧ (u = atom1 ∨ u = atom2 ∨ u = atom9 ∨ u = atom10)) ∨
      (u = atom1 ∧ (v = atom3 ∨ v = atom4 ∨ v = atom5)) ∨
      (v = atom1 ∧ (u = atom3 ∨ u = atom4 ∨ u = atom5)) ∨
      (u = atom2 ∧ (v = atom6 ∨ v = atom7 ∨ v = atom8)) ∨
      (v = atom2 ∧ (u = atom6 ∨ u = atom7 ∨ u = atom8)) := by
  fin_cases u <;> fin_cases v <;> decide +kernel

/-- The neighbors of the root, exactly. -/
theorem adj_atom0_iff (x : Atom) :
    graph.Adj atom0 x ↔ x = atom1 ∨ x = atom2 ∨ x = atom9 ∨ x = atom10 := by
  fin_cases x <;> decide +kernel

/-- The neighbors of the first arm, exactly. -/
theorem adj_atom1_iff (x : Atom) :
    graph.Adj atom1 x ↔ x = atom0 ∨ x = atom3 ∨ x = atom4 ∨ x = atom5 := by
  fin_cases x <;> decide +kernel

/-- The neighbors of the second arm, exactly. -/
theorem adj_atom2_iff (x : Atom) :
    graph.Adj atom2 x ↔ x = atom0 ∨ x = atom6 ∨ x = atom7 ∨ x = atom8 := by
  fin_cases x <;> decide +kernel

/-- The eight terminal atoms. -/
def leafSet : Finset Atom := {atom3, atom4, atom5, atom6, atom7, atom8, atom9, atom10}

/-- The unique parent of a terminal atom. -/
def leafParent (a : Atom) : Atom :=
  match a.val with
  | 3 | 4 | 5 => atom1
  | 6 | 7 | 8 => atom2
  | _ => atom0

/-- Every terminal atom has exactly the parent named by `leafParent` as neighbor. -/
theorem adj_leaf_unique :
    ∀ (leaf x : Atom), leaf ∈ leafSet → graph.Adj leaf x → x = leafParent leaf := by
  decide +kernel

/-- The non-terminal atoms. -/
def carbonAtoms : Finset Atom := {atom0, atom1, atom2}

theorem leafSet_not_carbon : ∀ a : Atom, a ∈ leafSet → a ∉ carbonAtoms := by
  decide +kernel

/-! ## Atomic numbers and source coordinates -/

/-- Atomic numbers of the eleven atoms. -/
theorem atomZ_eq (a : Atom) :
    graph.atomZ a =
      match a.val with
      | 0 => 6
      | 1 => 6
      | 2 => 6
      | 3 => 1
      | 4 => 9
      | 5 => 17
      | 6 => 1
      | 7 => 9
      | 8 => 17
      | 9 => 35
      | _ => 53 := by
  fin_cases a <;> rfl

@[simp] theorem atomZ_atom0 : graph.atomZ atom0 = 6 := by simpa using atomZ_eq atom0
@[simp] theorem atomZ_atom1 : graph.atomZ atom1 = 6 := by simpa using atomZ_eq atom1
@[simp] theorem atomZ_atom2 : graph.atomZ atom2 = 6 := by simpa using atomZ_eq atom2
@[simp] theorem atomZ_atom3 : graph.atomZ atom3 = 1 := by simpa using atomZ_eq atom3
@[simp] theorem atomZ_atom4 : graph.atomZ atom4 = 9 := by simpa using atomZ_eq atom4
@[simp] theorem atomZ_atom5 : graph.atomZ atom5 = 17 := by simpa using atomZ_eq atom5
@[simp] theorem atomZ_atom6 : graph.atomZ atom6 = 1 := by simpa using atomZ_eq atom6
@[simp] theorem atomZ_atom7 : graph.atomZ atom7 = 9 := by simpa using atomZ_eq atom7
@[simp] theorem atomZ_atom8 : graph.atomZ atom8 = 17 := by simpa using atomZ_eq atom8
@[simp] theorem atomZ_atom9 : graph.atomZ atom9 = 35 := by simpa using atomZ_eq atom9
@[simp] theorem atomZ_atom10 : graph.atomZ atom10 = 53 := by simpa using atomZ_eq atom10

/-- The exact source coordinate of each atom. -/
def pointOfAtom (a : Atom) : CartesianPoint3 :=
  match a.val with
  | 0 => { x := 0, y := 0, z := 0 }
  | 1 => { x := 1, y := 0, z := 0 }
  | 2 => { x := -1, y := 0, z := 0 }
  | 3 => { x := 2, y := 1, z := 0 }
  | 4 => { x := 2, y := 0, z := 1 }
  | 5 => { x := 2, y := -1, z := -1 }
  | 6 => { x := -2, y := 1, z := 0 }
  | 7 => { x := -2, y := 0, z := 1 }
  | 8 => { x := -2, y := -1, z := -1 }
  | 9 => { x := 0, y := 1, z := 1 }
  | _ => { x := 0, y := -1, z := 1 }

@[simp] theorem pointOfAtom_atom0 : pointOfAtom atom0 = { x := 0, y := 0, z := 0 } := rfl
@[simp] theorem pointOfAtom_atom1 : pointOfAtom atom1 = { x := 1, y := 0, z := 0 } := rfl
@[simp] theorem pointOfAtom_atom2 : pointOfAtom atom2 = { x := -1, y := 0, z := 0 } := rfl
@[simp] theorem pointOfAtom_atom3 : pointOfAtom atom3 = { x := 2, y := 1, z := 0 } := rfl
@[simp] theorem pointOfAtom_atom4 : pointOfAtom atom4 = { x := 2, y := 0, z := 1 } := rfl
@[simp] theorem pointOfAtom_atom5 : pointOfAtom atom5 = { x := 2, y := -1, z := -1 } := rfl
@[simp] theorem pointOfAtom_atom6 : pointOfAtom atom6 = { x := -2, y := 1, z := 0 } := rfl
@[simp] theorem pointOfAtom_atom7 : pointOfAtom atom7 = { x := -2, y := 0, z := 1 } := rfl
@[simp] theorem pointOfAtom_atom8 : pointOfAtom atom8 = { x := -2, y := -1, z := -1 } := rfl
@[simp] theorem pointOfAtom_atom9 : pointOfAtom atom9 = { x := 0, y := 1, z := 1 } := rfl
@[simp] theorem pointOfAtom_atom10 : pointOfAtom atom10 = { x := 0, y := -1, z := 1 } := rfl

/-- The actual executable spatial lookup reads the fixture coordinate at every atom. -/
theorem spatialPointAt_atom (a : Atom) :
    input.certified.spatialPointAt? a = some (pointOfAtom a) := by
  fin_cases a <;> decide +kernel

/-! ## Single bonds, constant charge, and acyclicity -/

theorem simpleBonded : graph.SimpleBonded := by
  intro u v h
  rw [adj_iff] at h
  rcases h with
      ⟨rfl, h | h | h | h⟩ | ⟨rfl, h | h | h | h⟩ |
      ⟨rfl, h | h | h⟩ | ⟨rfl, h | h | h⟩ |
      ⟨rfl, h | h | h⟩ | ⟨rfl, h | h | h⟩ <;>
    subst h <;> decide +kernel

theorem constantFormalCharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge graph := by
  refine ⟨0, ?_⟩
  intro a
  fin_cases a <;> decide +kernel

namespace DomainWalk

variable {V : Type*} [DecidableEq V]

/-- On a cycle, every vertex of the support has two distinct neighbors. -/
theorem exists_two_adj_of_isCycle {G : SimpleGraph V} {u : V} {c : G.Walk u u}
    (hc : c.IsCycle) (w : V) (hw : w ∈ c.support) :
    ∃ a b : V, a ≠ b ∧ G.Adj w a ∧ G.Adj w b := by
  let c' := c.rotate hw
  have hc' : c'.IsCycle := hc.rotate hw
  have h3 : 3 ≤ c'.length := hc'.three_le_length
  have h1 : 1 ≤ c'.length - 1 := by omega
  refine ⟨c'.getVert 1, c'.getVert (c'.length - 1), ?_, ?_, ?_⟩
  · intro heq
    have hn : 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c'.length} := by
      simp only [Set.mem_setOf_eq]; omega
    have hm : c'.length - 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c'.length} := by
      simp only [Set.mem_setOf_eq]; omega
    have := hc'.getVert_injOn hn hm heq
    omega
  · have hstep := c'.adj_getVert_succ (i := 0) (by omega)
    simpa using hstep
  · have hstep := c'.adj_getVert_succ (i := c'.length - 1) (by omega)
    have hlast : c'.getVert (c'.length - 1 + 1) = w := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ c'.length)]
      exact c'.getVert_length
    have hbw : G.Adj (c'.getVert (c'.length - 1)) w := by
      simpa [hlast] using hstep
    exact G.symm hbw

/-- A vertex with a unique neighbor cannot lie on a cycle. -/
theorem false_of_isCycle_of_leaf {G : SimpleGraph V} {u leaf parent : V}
    (huniq : ∀ x, G.Adj leaf x → x = parent)
    {c : G.Walk u u} (hc : c.IsCycle) (hmem : leaf ∈ c.support) : False := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_adj_of_isCycle hc leaf hmem
  exact hab ((huniq a ha).trans (huniq b hb).symm)

/-- No three atoms of the carbon set form a triangle. -/
theorem no_three_cycle_all :
    ∀ u a b : Atom, u ∈ carbonAtoms → a ∈ carbonAtoms → b ∈ carbonAtoms →
      ¬ (graph.underlyingSimpleGraph.Adj u a ∧
        graph.underlyingSimpleGraph.Adj a b ∧
        graph.underlyingSimpleGraph.Adj b u) := by
  decide +kernel

/-- Three vertices in the non-terminal set cannot form a triangle. -/
theorem no_three_cycle {u a b : Atom}
    (hu : u ∈ carbonAtoms) (ha : a ∈ carbonAtoms) (hb : b ∈ carbonAtoms)
    (e1 : graph.underlyingSimpleGraph.Adj u a)
    (e2 : graph.underlyingSimpleGraph.Adj a b)
    (e3 : graph.underlyingSimpleGraph.Adj b u) : False :=
  no_three_cycle_all u a b hu ha hb ⟨e1, e2, e3⟩

end DomainWalk

/-- **Every vertex on a cycle is one of the three carbons.**  A terminal atom has a unique
neighbor, hence cannot lie on a cycle. -/
theorem cycle_vertex_mem_carbonAtoms {u : Atom} {c : graph.underlyingSimpleGraph.Walk u u}
    (hc : c.IsCycle) {i : Nat} (hi : 1 ≤ i) (hiL : i ≤ c.length) :
    c.getVert i ∈ carbonAtoms := by
  by_contra hmem
  have hsupp : c.getVert i ∈ c.support := SimpleGraph.Walk.getVert_mem_support c i
  generalize hx : c.getVert i = x at hsupp hmem ⊢
  fin_cases x
  · exfalso
    exact hmem (by decide +kernel)
  · exfalso
    exact hmem (by decide +kernel)
  · exfalso
    exact hmem (by decide +kernel)
  · exfalso
    exact DomainWalk.false_of_isCycle_of_leaf
      (fun y hy => by simpa [leafParent] using
        adj_leaf_unique atom3 y (by decide) hy) hc hsupp
  · exfalso
    exact DomainWalk.false_of_isCycle_of_leaf
      (fun y hy => by simpa [leafParent] using
        adj_leaf_unique atom4 y (by decide) hy) hc hsupp
  · exfalso
    exact DomainWalk.false_of_isCycle_of_leaf
      (fun y hy => by simpa [leafParent] using
        adj_leaf_unique atom5 y (by decide) hy) hc hsupp
  · exfalso
    exact DomainWalk.false_of_isCycle_of_leaf
      (fun y hy => by simpa [leafParent] using
        adj_leaf_unique atom6 y (by decide) hy) hc hsupp
  · exfalso
    exact DomainWalk.false_of_isCycle_of_leaf
      (fun y hy => by simpa [leafParent] using
        adj_leaf_unique atom7 y (by decide) hy) hc hsupp
  · exfalso
    exact DomainWalk.false_of_isCycle_of_leaf
      (fun y hy => by simpa [leafParent] using
        adj_leaf_unique atom8 y (by decide) hy) hc hsupp
  · exfalso
    exact DomainWalk.false_of_isCycle_of_leaf
      (fun y hy => by simpa [leafParent] using
        adj_leaf_unique atom9 y (by decide) hy) hc hsupp
  · exfalso
    exact DomainWalk.false_of_isCycle_of_leaf
      (fun y hy => by simpa [leafParent] using
        adj_leaf_unique atom10 y (by decide) hy) hc hsupp

/-- **The fixture graph is acyclic.**  Every cycle vertex is a carbon, so the cycle has length
at most three; a three-cycle on the three carbons would require the absent edge between the two
arms. -/
theorem acyclic : graph.Acyclic := by
  intro u c hc
  have h3 : 3 ≤ c.length := hc.three_le_length
  have hmemS : ∀ i, 1 ≤ i → i ≤ c.length → c.getVert i ∈ carbonAtoms :=
    fun i hi hiL => cycle_vertex_mem_carbonAtoms hc hi hiL
  have hle : c.length ≤ 3 := by
    let f : Fin c.length → {x : Atom // x ∈ carbonAtoms} := fun k =>
      ⟨c.getVert (k.1 + 1), hmemS (k.1 + 1) (by omega) (by omega)⟩
    have hf : Function.Injective f := by
      intro k l hkl
      apply Fin.ext
      have hk : k.1 + 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
        simp only [Set.mem_setOf_eq]; have := k.2; omega
      have hl : l.1 + 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
        simp only [Set.mem_setOf_eq]; have := l.2; omega
      have := hc.getVert_injOn hk hl (congrArg Subtype.val hkl)
      omega
    have hcard := Fintype.card_le_of_injective f hf
    have hcardS : Fintype.card {x : Atom // x ∈ carbonAtoms} = 3 := by
      decide +kernel
    simpa [hcardS] using hcard
  have hL : c.length = 3 := by omega
  have h30 : c.getVert 3 = c.getVert 0 := by
    rw [show 3 = c.length by omega]
    simp
  have hu : c.getVert 0 ∈ carbonAtoms := by
    rw [← h30]
    exact hmemS 3 (by omega) (by omega)
  have ha : c.getVert 1 ∈ carbonAtoms := hmemS 1 (by omega) (by omega)
  have hb : c.getVert 2 ∈ carbonAtoms := hmemS 2 (by omega) (by omega)
  have hn3 : 3 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
    simp only [Set.mem_setOf_eq]; omega
  have hn1 : 1 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
    simp only [Set.mem_setOf_eq]; omega
  have hn2 : 2 ∈ {i : Nat | 1 ≤ i ∧ i ≤ c.length} := by
    simp only [Set.mem_setOf_eq]; omega
  have hu_ne_a : c.getVert 0 ≠ c.getVert 1 := by
    intro heq
    have h31 : c.getVert 3 = c.getVert 1 := by rw [h30, heq]
    have := hc.getVert_injOn hn3 hn1 h31
    omega
  have ha_ne_b : c.getVert 1 ≠ c.getVert 2 := by
    intro heq
    have := hc.getVert_injOn hn1 hn2 heq
    omega
  have hb_ne_u : c.getVert 2 ≠ c.getVert 0 := by
    intro heq
    have h32 : c.getVert 3 = c.getVert 2 := by rw [h30, heq]
    have := hc.getVert_injOn hn3 hn2 h32
    omega
  have e1 : graph.underlyingSimpleGraph.Adj (c.getVert 0) (c.getVert 1) := by
    have := c.adj_getVert_succ (i := 0) (by omega)
    simpa using this
  have e2 : graph.underlyingSimpleGraph.Adj (c.getVert 1) (c.getVert 2) := by
    have := c.adj_getVert_succ (i := 1) (by omega)
    simpa using this
  have e3 : graph.underlyingSimpleGraph.Adj (c.getVert 2) (c.getVert 0) := by
    have := c.adj_getVert_succ (i := 2) (by omega)
    have h23 : c.getVert (2 + 1) = c.getVert 0 := by
      simpa using h30
    simpa [h23] using this
  exact DomainWalk.no_three_cycle hu ha hb e1 e2 e3

/-! ## The explicit physical configuration and calibration -/

/-- The configuration: mirror frame on the first arm, identity frame elsewhere. -/
def cfg : m.Configuration := fun c =>
  if c.1 = atom1 then MultiCenterMolecule.mirrorFrame else 1

theorem cfg_root : cfg root = 1 := by
  change (if (root.1 = atom1) then MultiCenterMolecule.mirrorFrame else 1) = 1
  rw [if_neg (by decide)]

theorem cfg_armOne : cfg armOneCenter = MultiCenterMolecule.mirrorFrame := by
  change (if (armOneCenter.1 = atom1) then MultiCenterMolecule.mirrorFrame else 1) =
    MultiCenterMolecule.mirrorFrame
  rw [if_pos (by decide)]

theorem cfg_armTwo : cfg armTwoCenter = 1 := by
  change (if (armTwoCenter.1 = atom1) then MultiCenterMolecule.mirrorFrame else 1) = 1
  rw [if_neg (by decide)]

/-- The canonical physical point of each ligand slot at a center. -/
def pointAt (c : m.Center) : Fin 4 → CartesianPoint3 :=
  fun i => pointOfAtom (m.ligandAtomAt c i)

theorem ligandAtomAt_root (i : Fin 4) : m.ligandAtomAt root i = rootLigand i := rfl

theorem rootLigand_zero : rootLigand 0 = atom1 := rfl

theorem rootLigand_one : rootLigand 1 = atom2 := rfl

theorem rootLigand_two : rootLigand 2 = atom9 := rfl

theorem rootLigand_three : rootLigand 3 = atom10 := rfl

theorem ligandAtomAt_armOne (i : Fin 4) :
    m.ligandAtomAt armOneCenter i = armOneLigand i := rfl

theorem ligandAtomAt_armTwo (i : Fin 4) :
    m.ligandAtomAt armTwoCenter i = armTwoLigand i := rfl

def rootPoints : Fin 4 → CartesianPoint3 := fun i => pointOfAtom (rootLigand i)

def armOnePoints : Fin 4 → CartesianPoint3 := fun i => pointOfAtom (armOneLigand i)

def armTwoPoints : Fin 4 → CartesianPoint3 := fun i => pointOfAtom (armTwoLigand i)

theorem pointAt_root : pointAt root = rootPoints := by
  funext i
  simp [pointAt, rootPoints, ligandAtomAt_root]

theorem pointAt_armOne : pointAt armOneCenter = armOnePoints := by
  funext i
  simp [pointAt, armOnePoints, ligandAtomAt_armOne]

theorem pointAt_armTwo : pointAt armTwoCenter = armTwoPoints := by
  funext i
  simp [pointAt, armTwoPoints, ligandAtomAt_armTwo]

/-- The arm-one ligand atomic numbers are injective. -/
theorem armOne_zInjective :
    Function.Injective (fun i => m.mol.atomZ (m.ligandAtomAt armOneCenter i)) := by
  decide +kernel

/-- The arm-two ligand atomic numbers are injective. -/
theorem armTwo_zInjective :
    Function.Injective (fun i => m.mol.atomZ (m.ligandAtomAt armTwoCenter i)) := by
  decide +kernel

/-- The executable source lookup returns the exact arm-one coordinates. -/
theorem armOne_observed :
    ∀ i, input.certified.spatialPointAt? (m.ligandAtomAt armOneCenter i) =
      some (pointAt armOneCenter i) := by
  intro i
  fin_cases i <;>
    simp [pointAt, ligandAtomAt_armOne, armOneLigand, spatialPointAt_atom]

/-- The executable source lookup returns the exact arm-two coordinates. -/
theorem armTwo_observed :
    ∀ i, input.certified.spatialPointAt? (m.ligandAtomAt armTwoCenter i) =
      some (pointAt armTwoCenter i) := by
  intro i
  fin_cases i <;>
    simp [pointAt, ligandAtomAt_armTwo, armTwoLigand, spatialPointAt_atom]

/-- The root ligand tetrahedron is nondegenerate: its oriented volume is `4`. -/
theorem root_volume :
    CartesianPoint3.orientedVolume
        (pointAt root 0) (pointAt root 1)
        (pointAt root 2) (pointAt root 3) = 4 := by
  simp only [pointAt_root, rootPoints, rootLigand_zero, rootLigand_one, rootLigand_two,
    rootLigand_three, pointOfAtom_atom1, pointOfAtom_atom2, pointOfAtom_atom9,
    pointOfAtom_atom10, CartesianPoint3.orientedVolume]
  norm_num

theorem root_volume_ne_zero :
    CartesianPoint3.orientedVolume
        (pointAt root 0) (pointAt root 1)
        (pointAt root 2) (pointAt root 3) ≠ 0 := by
  rw [root_volume]
  norm_num

theorem root_sign :
    rationalVolumeSign
        (CartesianPoint3.orientedVolume
          (pointAt root 0) (pointAt root 1)
          (pointAt root 2) (pointAt root 3)) =
      m.configurationSign cfg root := by
  rw [root_volume]
  change rationalVolumeSign 4 = permHandedness (cfg root)
  rw [cfg_root]
  simp [rationalVolumeSign]

theorem armOne_volume :
    CartesianPoint3.orientedVolume
        (pointAt armOneCenter 0) (pointAt armOneCenter 1)
        (pointAt armOneCenter 2) (pointAt armOneCenter 3) = -6 := by
  simp only [pointAt_armOne, armOnePoints, armOneLigand, pointOfAtom_atom0, pointOfAtom_atom3,
    pointOfAtom_atom4, pointOfAtom_atom5, CartesianPoint3.orientedVolume]
  norm_num

theorem armTwo_volume :
    CartesianPoint3.orientedVolume
        (pointAt armTwoCenter 0) (pointAt armTwoCenter 1)
        (pointAt armTwoCenter 2) (pointAt armTwoCenter 3) = 6 := by
  simp only [pointAt_armTwo, armTwoPoints, armTwoLigand, pointOfAtom_atom0, pointOfAtom_atom6,
    pointOfAtom_atom7, pointOfAtom_atom8, CartesianPoint3.orientedVolume]
  norm_num

theorem armOne_volume_ne_zero :
    CartesianPoint3.orientedVolume
        (pointAt armOneCenter 0) (pointAt armOneCenter 1)
        (pointAt armOneCenter 2) (pointAt armOneCenter 3) ≠ 0 := by
  rw [armOne_volume]
  norm_num

theorem armTwo_volume_ne_zero :
    CartesianPoint3.orientedVolume
        (pointAt armTwoCenter 0) (pointAt armTwoCenter 1)
        (pointAt armTwoCenter 2) (pointAt armTwoCenter 3) ≠ 0 := by
  rw [armTwo_volume]
  norm_num

theorem armOne_sign :
    rationalVolumeSign
        (CartesianPoint3.orientedVolume
          (pointAt armOneCenter 0) (pointAt armOneCenter 1)
          (pointAt armOneCenter 2) (pointAt armOneCenter 3)) =
      m.configurationSign cfg armOneCenter := by
  rw [armOne_volume]
  change rationalVolumeSign (-6) = permHandedness (cfg armOneCenter)
  rw [cfg_armOne]
  simp [rationalVolumeSign, MultiCenterMolecule.mirrorFrame]

theorem armTwo_sign :
    rationalVolumeSign
        (CartesianPoint3.orientedVolume
          (pointAt armTwoCenter 0) (pointAt armTwoCenter 1)
          (pointAt armTwoCenter 2) (pointAt armTwoCenter 3)) =
      m.configurationSign cfg armTwoCenter := by
  rw [armTwo_volume]
  change rationalVolumeSign 6 = permHandedness (cfg armTwoCenter)
  rw [cfg_armTwo]
  simp [rationalVolumeSign]

/-- The two carbon arms are calibrated in the explicit configuration. -/
theorem armOne_calibrated :
    ActualPhysicalCalibratedCenter input.certified m cfg armOneCenter :=
  ⟨pointAt armOneCenter, armOne_zInjective, armOne_observed,
    armOne_volume_ne_zero, armOne_sign⟩

/-- The second carbon arm is calibrated in the explicit configuration. -/
theorem armTwo_calibrated :
    ActualPhysicalCalibratedCenter input.certified m cfg armTwoCenter :=
  ⟨pointAt armTwoCenter, armTwo_zInjective, armTwo_observed,
    armTwo_volume_ne_zero, armTwo_sign⟩

/-- Every center different from the root is one of the two carbon arms. -/
theorem center_eq_of_ne_root {c : m.Center} (hc : c ≠ root) :
    c = armOneCenter ∨ c = armTwoCenter := by
  rcases c with ⟨v, hv⟩
  change v ∈ ({atom0, atom1, atom2} : Finset Atom) at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact absurd (Subtype.ext rfl) hc
  · exact Or.inl rfl
  · exact Or.inr rfl



theorem globalPhysicalDomain :
    ActualGlobalPhysicalCalibratedDomain input.certified m cfg root where
  graphEq := rfl
  centerCase := by
    intro c hc
    rcases center_eq_of_ne_root hc with rfl | rfl
    · exact Or.inr armOne_calibrated
    · exact Or.inr armTwo_calibrated

/-- **Physical-domain inhabitance.**  The certified input carries an actual multi-center molecule,
configuration, and root satisfying the global physical calibrated domain. -/
theorem physicalDomain_inhabited :
    ∃ (cfg : m.Configuration) (root : m.Center),
      ActualGlobalPhysicalCalibratedDomain input.certified m cfg root :=
  ⟨cfg, root, globalPhysicalDomain⟩

/-! ## The carbon-arm swap automorphism

The molecule admits exactly one nontrivial symmetry: swapping the two carbon arms while fixing the
root, bromine and iodine.  The permutation is built from four disjoint atom swaps. -/

/-- Swap the two carbon arms: `1 ↔ 2`, `3 ↔ 6`, `4 ↔ 7`, `5 ↔ 8`; fix `0`, `9`, `10`. -/
def armSwapPerm : Equiv.Perm Atom :=
  Equiv.swap atom1 atom2 * Equiv.swap atom3 atom6 *
    Equiv.swap atom4 atom7 * Equiv.swap atom5 atom8

@[simp] theorem armSwap_apply_atom0 : armSwapPerm atom0 = atom0 := by decide +kernel
@[simp] theorem armSwap_apply_atom1 : armSwapPerm atom1 = atom2 := by decide +kernel
@[simp] theorem armSwap_apply_atom2 : armSwapPerm atom2 = atom1 := by decide +kernel
@[simp] theorem armSwap_apply_atom3 : armSwapPerm atom3 = atom6 := by decide +kernel
@[simp] theorem armSwap_apply_atom4 : armSwapPerm atom4 = atom7 := by decide +kernel
@[simp] theorem armSwap_apply_atom5 : armSwapPerm atom5 = atom8 := by decide +kernel
@[simp] theorem armSwap_apply_atom6 : armSwapPerm atom6 = atom3 := by decide +kernel
@[simp] theorem armSwap_apply_atom7 : armSwapPerm atom7 = atom4 := by decide +kernel
@[simp] theorem armSwap_apply_atom8 : armSwapPerm atom8 = atom5 := by decide +kernel
@[simp] theorem armSwap_apply_atom9 : armSwapPerm atom9 = atom9 := by decide +kernel
@[simp] theorem armSwap_apply_atom10 : armSwapPerm atom10 = atom10 := by decide +kernel

theorem armSwap_atomZ :
    ∀ v : Atom, graph.atomZ (armSwapPerm v) = graph.atomZ v := by
  decide +kernel

theorem armSwap_atomMass :
    ∀ v : Atom, graph.atomMass (armSwapPerm v) = graph.atomMass v := by
  decide +kernel

theorem armSwap_formalCharge :
    ∀ v : Atom, graph.formalCharge (armSwapPerm v) = graph.formalCharge v := by
  decide +kernel

theorem armSwap_bond :
    ∀ u v : Atom, graph.bond (armSwapPerm u) (armSwapPerm v) = graph.bond u v := by
  decide +kernel

theorem armSwap_isAutomorphism : graph.IsAutomorphism armSwapPerm :=
  ⟨armSwap_atomZ, armSwap_atomMass, armSwap_formalCharge, armSwap_bond⟩

theorem armSwap_mem_graphAut : armSwapPerm ∈ graph.Aut := armSwap_isAutomorphism

theorem armSwap_preservesCenters : m.PreservesCenters armSwapPerm := by
  intro c
  change c ∈ ({atom0, atom1, atom2} : Finset Atom) ↔
    armSwapPerm c ∈ ({atom0, atom1, atom2} : Finset Atom)
  fin_cases c <;> decide +kernel

/-- The arm swap as an automorphism of the multi-center molecule. -/
def armSwapAut : m.Aut :=
  ⟨armSwapPerm, ⟨armSwap_mem_graphAut, armSwap_preservesCenters⟩⟩

theorem centerPerm_armSwap_root : m.centerPerm armSwapAut root = root :=
  (centerPerm_eq_iff m armSwapAut root).2 (by
    change armSwapPerm atom0 = atom0
    exact armSwap_apply_atom0)

theorem centerPerm_armSwap_armOne :
    m.centerPerm armSwapAut armOneCenter = armTwoCenter := by
  apply Subtype.ext
  change armSwapPerm atom1 = atom2
  exact armSwap_apply_atom1

theorem centerPerm_armSwap_armTwo :
    m.centerPerm armSwapAut armTwoCenter = armOneCenter := by
  apply Subtype.ext
  change armSwapPerm atom2 = atom1
  exact armSwap_apply_atom2

/-- At the root the arm swap acts as the transposition of the two carbon ligand slots. -/
theorem ligandPermAt_armSwap_root :
    m.ligandPermAt armSwapAut root = Equiv.swap (0 : Fin 4) 1 := by
  apply Equiv.ext
  intro i
  apply m.ligandAtomAt_injective (m.centerPerm armSwapAut root)
  rw [m.ligandAtomAt_ligandPermAt, centerPerm_armSwap_root]
  fin_cases i <;> decide +kernel

/-- At the first arm the arm swap reindexes the ligand slots by the identity. -/
theorem ligandPermAt_armSwap_armOne :
    m.ligandPermAt armSwapAut armOneCenter = 1 := by
  apply Equiv.ext
  intro i
  apply m.ligandAtomAt_injective (m.centerPerm armSwapAut armOneCenter)
  rw [m.ligandAtomAt_ligandPermAt, centerPerm_armSwap_armOne]
  fin_cases i <;> decide +kernel

/-- At the second arm the arm swap reindexes the ligand slots by the identity. -/
theorem ligandPermAt_armSwap_armTwo :
    m.ligandPermAt armSwapAut armTwoCenter = 1 := by
  apply Equiv.ext
  intro i
  apply m.ligandAtomAt_injective (m.centerPerm armSwapAut armTwoCenter)
  rw [m.ligandAtomAt_ligandPermAt, centerPerm_armSwap_armTwo]
  fin_cases i <;> decide +kernel

/-! ## Root automorphisms and their ligand action -/

theorem aut_adj_image (e : m.Aut) {u v : Atom} (h : graph.Adj u v) :
    graph.Adj ((e : Equiv.Perm Atom) u) ((e : Equiv.Perm Atom) v) := by
  let eG : graph.Aut :=
    ⟨(e : Equiv.Perm Atom), MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩
  exact (MoleculeGraph.Aut.adj_iff (m := graph) eG u v).2 h

theorem aut_atomZ_image (e : m.Aut) (v : Atom) :
    graph.atomZ ((e : Equiv.Perm Atom) v) = graph.atomZ v := by
  let eG : graph.Aut :=
    ⟨(e : Equiv.Perm Atom), MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩
  exact MoleculeGraph.Aut.atomZ_eq (m := graph) eG v

theorem aut_root_neighbor_eq (e : m.Aut)
    (he0 : (e : Equiv.Perm Atom) atom0 = atom0) {v : Atom}
    (hadv : graph.Adj atom0 v) :
    (e : Equiv.Perm Atom) v = atom1 ∨ (e : Equiv.Perm Atom) v = atom2 ∨
      (e : Equiv.Perm Atom) v = atom9 ∨ (e : Equiv.Perm Atom) v = atom10 := by
  have h := aut_adj_image e hadv
  rw [he0] at h
  exact (adj_atom0_iff ((e : Equiv.Perm Atom) v)).mp h

theorem aut_atom9_of_fixes_root (e : m.Aut)
    (he0 : (e : Equiv.Perm Atom) atom0 = atom0) :
    (e : Equiv.Perm Atom) atom9 = atom9 := by
  have hcases := aut_root_neighbor_eq e he0 (by decide : graph.Adj atom0 atom9)
  have hz : graph.atomZ ((e : Equiv.Perm Atom) atom9) = 35 := by
    have h := aut_atomZ_image e atom9
    simpa using h
  rcases hcases with h | h | h | h
  · rw [h, atomZ_atom1] at hz
    norm_num at hz
  · rw [h, atomZ_atom2] at hz
    norm_num at hz
  · exact h
  · rw [h, atomZ_atom10] at hz
    norm_num at hz

theorem aut_atom10_of_fixes_root (e : m.Aut)
    (he0 : (e : Equiv.Perm Atom) atom0 = atom0) :
    (e : Equiv.Perm Atom) atom10 = atom10 := by
  have hcases := aut_root_neighbor_eq e he0 (by decide : graph.Adj atom0 atom10)
  have hz : graph.atomZ ((e : Equiv.Perm Atom) atom10) = 53 := by
    have h := aut_atomZ_image e atom10
    simpa using h
  rcases hcases with h | h | h | h
  · rw [h, atomZ_atom1] at hz
    norm_num at hz
  · rw [h, atomZ_atom2] at hz
    norm_num at hz
  · rw [h, atomZ_atom9] at hz
    norm_num at hz
  · exact h

theorem aut_atom1_eq_atom1_or_atom2 (e : m.Aut)
    (he0 : (e : Equiv.Perm Atom) atom0 = atom0) :
    (e : Equiv.Perm Atom) atom1 = atom1 ∨ (e : Equiv.Perm Atom) atom1 = atom2 := by
  have hcases := aut_root_neighbor_eq e he0 (by decide : graph.Adj atom0 atom1)
  have hz : graph.atomZ ((e : Equiv.Perm Atom) atom1) = 6 := by
    have h := aut_atomZ_image e atom1
    simpa using h
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h, atomZ_atom9] at hz
    norm_num at hz
  · rw [h, atomZ_atom10] at hz
    norm_num at hz

theorem aut_atom2_eq_atom1_or_atom2 (e : m.Aut)
    (he0 : (e : Equiv.Perm Atom) atom0 = atom0) :
    (e : Equiv.Perm Atom) atom2 = atom1 ∨ (e : Equiv.Perm Atom) atom2 = atom2 := by
  have hcases := aut_root_neighbor_eq e he0 (by decide : graph.Adj atom0 atom2)
  have hz : graph.atomZ ((e : Equiv.Perm Atom) atom2) = 6 := by
    have h := aut_atomZ_image e atom2
    simpa using h
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h, atomZ_atom9] at hz
    norm_num at hz
  · rw [h, atomZ_atom10] at hz
    norm_num at hz

theorem aut_atom3_of_atom1_to_atom2 (e : m.Aut)
    (h12 : (e : Equiv.Perm Atom) atom1 = atom2) :
    (e : Equiv.Perm Atom) atom3 = atom6 := by
  have hcases : (e : Equiv.Perm Atom) atom3 = atom0 ∨
      (e : Equiv.Perm Atom) atom3 = atom6 ∨
      (e : Equiv.Perm Atom) atom3 = atom7 ∨
      (e : Equiv.Perm Atom) atom3 = atom8 := by
    have h := aut_adj_image e (by decide : graph.Adj atom1 atom3)
    rw [h12] at h
    exact (adj_atom2_iff ((e : Equiv.Perm Atom) atom3)).mp h
  have hz : graph.atomZ ((e : Equiv.Perm Atom) atom3) = 1 := by
    have h := aut_atomZ_image e atom3
    simpa using h
  rcases hcases with h | h | h | h
  · rw [h, atomZ_atom0] at hz
    norm_num at hz
  · exact h
  · rw [h, atomZ_atom7] at hz
    norm_num at hz
  · rw [h, atomZ_atom8] at hz
    norm_num at hz

theorem aut_atom4_of_atom1_to_atom2 (e : m.Aut)
    (h12 : (e : Equiv.Perm Atom) atom1 = atom2) :
    (e : Equiv.Perm Atom) atom4 = atom7 := by
  have hcases : (e : Equiv.Perm Atom) atom4 = atom0 ∨
      (e : Equiv.Perm Atom) atom4 = atom6 ∨
      (e : Equiv.Perm Atom) atom4 = atom7 ∨
      (e : Equiv.Perm Atom) atom4 = atom8 := by
    have h := aut_adj_image e (by decide : graph.Adj atom1 atom4)
    rw [h12] at h
    exact (adj_atom2_iff ((e : Equiv.Perm Atom) atom4)).mp h
  have hz : graph.atomZ ((e : Equiv.Perm Atom) atom4) = 9 := by
    have h := aut_atomZ_image e atom4
    simpa using h
  rcases hcases with h | h | h | h
  · rw [h, atomZ_atom0] at hz
    norm_num at hz
  · rw [h, atomZ_atom6] at hz
    norm_num at hz
  · exact h
  · rw [h, atomZ_atom8] at hz
    norm_num at hz

theorem aut_atom5_of_atom1_to_atom2 (e : m.Aut)
    (h12 : (e : Equiv.Perm Atom) atom1 = atom2) :
    (e : Equiv.Perm Atom) atom5 = atom8 := by
  have hcases : (e : Equiv.Perm Atom) atom5 = atom0 ∨
      (e : Equiv.Perm Atom) atom5 = atom6 ∨
      (e : Equiv.Perm Atom) atom5 = atom7 ∨
      (e : Equiv.Perm Atom) atom5 = atom8 := by
    have h := aut_adj_image e (by decide : graph.Adj atom1 atom5)
    rw [h12] at h
    exact (adj_atom2_iff ((e : Equiv.Perm Atom) atom5)).mp h
  have hz : graph.atomZ ((e : Equiv.Perm Atom) atom5) = 17 := by
    have h := aut_atomZ_image e atom5
    simpa using h
  rcases hcases with h | h | h | h
  · rw [h, atomZ_atom0] at hz
    norm_num at hz
  · rw [h, atomZ_atom6] at hz
    norm_num at hz
  · rw [h, atomZ_atom7] at hz
    norm_num at hz
  · exact h

/-- A root-fixing automorphism acts on the root ligand slots either as the identity or as the
transposition of the two carbon arms. -/
theorem ligandPermAt_root_eq_one_or_swap (e : m.Aut)
    (hroot : m.centerPerm e root = root) :
    m.ligandPermAt e root = 1 ∨
      m.ligandPermAt e root = Equiv.swap (0 : Fin 4) 1 := by
  have he0 : (e : Equiv.Perm Atom) atom0 = atom0 :=
    (centerPerm_eq_iff m e root).mp hroot
  have he9 := aut_atom9_of_fixes_root e he0
  have he10 := aut_atom10_of_fixes_root e he0
  rcases aut_atom1_eq_atom1_or_atom2 e he0 with he1 | he1
  · left
    have he2 : (e : Equiv.Perm Atom) atom2 = atom2 := by
      rcases aut_atom2_eq_atom1_or_atom2 e he0 with h | h
      · exfalso
        exact absurd ((e : Equiv.Perm Atom).injective (h.trans he1.symm)) (by decide)
      · exact h
    apply Equiv.ext
    intro i
    apply m.ligandAtomAt_injective (m.centerPerm e root)
    rw [m.ligandAtomAt_ligandPermAt, hroot]
    simp only [Equiv.Perm.one_apply]
    fin_cases i <;>
      simp [ligandAtomAt_root, rootLigand, he0, he1, he2, he9, he10]
  · right
    have he2 : (e : Equiv.Perm Atom) atom2 = atom1 := by
      rcases aut_atom2_eq_atom1_or_atom2 e he0 with h | h
      · exact h
      · exfalso
        exact absurd ((e : Equiv.Perm Atom).injective (h.trans he1.symm)) (by decide)
    apply Equiv.ext
    intro i
    apply m.ligandAtomAt_injective (m.centerPerm e root)
    rw [m.ligandAtomAt_ligandPermAt, hroot]
    fin_cases i <;>
      simp [ligandAtomAt_root, rootLigand, he0, he1, he2, he9, he10]
    · decide +kernel
    · decide +kernel

/-- At the first arm, any root-fixing automorphism that carries atom `1` to atom `2` acts on the
arm's ligand slots by the identity. -/
theorem ligandPermAt_armOne_eq_one_of_atom1_to_atom2 (e : m.Aut)
    (he0 : (e : Equiv.Perm Atom) atom0 = atom0)
    (h12 : (e : Equiv.Perm Atom) atom1 = atom2) :
    m.ligandPermAt e armOneCenter = 1 := by
  have hcenter : m.centerPerm e armOneCenter = armTwoCenter := by
    apply Subtype.ext
    change (e : Equiv.Perm Atom) atom1 = atom2
    exact h12
  have he3 := aut_atom3_of_atom1_to_atom2 e h12
  have he4 := aut_atom4_of_atom1_to_atom2 e h12
  have he5 := aut_atom5_of_atom1_to_atom2 e h12
  apply Equiv.ext
  intro i
  apply m.ligandAtomAt_injective (m.centerPerm e armOneCenter)
  rw [m.ligandAtomAt_ligandPermAt, hcenter]
  simp only [Equiv.Perm.one_apply]
  fin_cases i <;>
    simp [ligandAtomAt_armOne, ligandAtomAt_armTwo, armOneLigand, armTwoLigand,
      he0, he3, he4, he5]

/-! ## The rooted ligand branches of the physical molecule -/

/-- The root is in none of its own deleted-root ligand branches. -/
theorem root_not_mem_ligandBranch (i : Fin 4) :
    ¬ LigandBranchReaches m root i root.1 := by
  rintro ⟨p, hp⟩
  exact hp (SimpleGraph.Walk.end_mem_support p)

theorem root_not_mem_branch_zero : ¬ LigandBranchReaches m root 0 root.1 :=
  root_not_mem_ligandBranch 0

/-- The first arm belongs to the branch of root ligand slot `0`. -/
theorem armOne_mem_branch_zero : LigandBranchReaches m root 0 armOneCenter.1 := by
  have h : atom1 ∈ CutBranch graph atom0 atom1 :=
    cutBranch_mem_self graph (by decide : graph.Adj atom0 atom1)
  exact h

/-- The second arm belongs to the branch of root ligand slot `1`. -/
theorem armTwo_mem_branch_one : LigandBranchReaches m root 1 armTwoCenter.1 := by
  have h : atom2 ∈ CutBranch graph atom0 atom2 :=
    cutBranch_mem_self graph (by decide : graph.Adj atom0 atom2)
  exact h

/-- Acyclicity separates the two carbon arms: the second arm is not in slot `0`. -/
theorem armTwo_not_mem_branch_zero : ¬ LigandBranchReaches m root 0 armTwoCenter.1 := by
  intro h0
  have hcu : graph.Adj atom0 (m.ligandAtomAt root 0) := by
    simpa [root] using m.ligandAtomAt_adj root 0
  have hcv : graph.Adj atom0 (m.ligandAtomAt root 1) := by
    simpa [root] using m.ligandAtomAt_adj root 1
  have h1 : atom2 ∈ CutBranch graph atom0 atom2 :=
    cutBranch_mem_self graph (by decide : graph.Adj atom0 atom2)
  have hdisj := cutBranch_disjoint_of_acyclic graph acyclic hcu hcv h0 h1
  exact (by decide : atom1 ≠ atom2) hdisj

/-- Acyclicity separates the two carbon arms: the first arm is not in slot `1`. -/
theorem armOne_not_mem_branch_one : ¬ LigandBranchReaches m root 1 armOneCenter.1 := by
  intro h1
  have hcu : graph.Adj atom0 (m.ligandAtomAt root 1) := by
    simpa [root] using m.ligandAtomAt_adj root 1
  have hcv : graph.Adj atom0 (m.ligandAtomAt root 0) := by
    simpa [root] using m.ligandAtomAt_adj root 0
  have h0 : atom1 ∈ CutBranch graph atom0 atom1 :=
    cutBranch_mem_self graph (by decide : graph.Adj atom0 atom1)
  have hdisj := cutBranch_disjoint_of_acyclic graph acyclic hcu hcv h1 h0
  exact (by decide : atom2 ≠ atom1) hdisj

/-- The only detected center in root branch `0` is the first carbon arm. -/
theorem center_eq_armOne_of_branch_zero (d : m.Center)
    (hd : LigandBranchReaches m root 0 d.1) : d = armOneCenter := by
  by_cases hroot : d = root
  · subst hroot
    exact absurd hd root_not_mem_branch_zero
  · rcases center_eq_of_ne_root hroot with h | h
    · exact h
    · subst h
      exact absurd hd armTwo_not_mem_branch_zero

/-- The only detected center in root branch `1` is the second carbon arm. -/
theorem center_eq_armTwo_of_branch_one (d : m.Center)
    (hd : LigandBranchReaches m root 1 d.1) : d = armTwoCenter := by
  by_cases hroot : d = root
  · subst hroot
    exact absurd hd (root_not_mem_ligandBranch 1)
  · rcases center_eq_of_ne_root hroot with h | h
    · subst h
      exact absurd hd armOne_not_mem_branch_one
    · exact h

/-- The root configuration sign is `+1`. -/
theorem configurationSign_cfg_root : m.configurationSign cfg root = 1 := by
  simp [MultiCenterMolecule.configurationSign, cfg_root]

/-- The first arm configuration sign is `-1` (mirror frame). -/
theorem configurationSign_cfg_armOne : m.configurationSign cfg armOneCenter = -1 := by
  simp [MultiCenterMolecule.configurationSign, cfg_armOne, MultiCenterMolecule.mirrorFrame]

/-- The second arm configuration sign is `+1` (identity frame). -/
theorem configurationSign_cfg_armTwo : m.configurationSign cfg armTwoCenter = 1 := by
  simp [MultiCenterMolecule.configurationSign, cfg_armTwo]

/-! ## The physical enantiomorphic pair at the root -/

/-- The arm swap is a mirror transport from root slot `0` to root slot `1`. -/
theorem mirrorTransport_root_zero_one : MirrorTransport m cfg root 0 1 := by
  refine ⟨armSwapAut, centerPerm_armSwap_root, ?_, ?_⟩
  · rw [ligandPermAt_armSwap_root]
    decide +kernel
  · intro d hd
    have hd' : d = armOneCenter := center_eq_armOne_of_branch_zero d hd
    subst hd'
    rw [centerPerm_armSwap_armOne, ligandPermAt_armSwap_armOne,
      configurationSign_cfg_armOne, configurationSign_cfg_armTwo]
    simp

/-- No proper root transport sends slot `0` to slot `1`.  A root-fixing automorphism either fixes
the arm branches or swaps them; the swapping case makes the first-arm frame identity, which turns
the unique local sign equation into `-1 = 1`. -/
theorem noProperTransport_root_zero_one : ¬ ProperTransport m cfg root 0 1 := by
  intro hproper
  have hproper' : ProperTransport m cfg root 0 1 := hproper
  rcases hproper with ⟨e, hroot, hlig, hsign⟩
  have he0 : (e : Equiv.Perm Atom) atom0 = atom0 :=
    (centerPerm_eq_iff m e root).mp hroot
  rcases ligandPermAt_root_eq_one_or_swap e hroot with hp | hp
  · rw [hp] at hlig
    exact (by decide : ¬ ((1 : Equiv.Perm (Fin 4)) 0 = 1)) hlig
  · have h12 : (e : Equiv.Perm Atom) atom1 = atom2 := by
      have h := m.ligandAtomAt_ligandPermAt (e := e) (c := root) (i := 0)
      rw [hroot, hp] at h
      rw [show (Equiv.swap (0 : Fin 4) 1) 0 = 1 by decide] at h
      rw [ligandAtomAt_root] at h
      simpa [rootLigand] using h.symm
    have hamOne : m.ligandPermAt e armOneCenter = 1 :=
      ligandPermAt_armOne_eq_one_of_atom1_to_atom2 e he0 h12
    have hcenter : m.centerPerm e armOneCenter = armTwoCenter := by
      apply Subtype.ext
      change (e : Equiv.Perm Atom) atom1 = atom2
      exact h12
    have hs := hsign armOneCenter armOne_mem_branch_zero
    rw [hcenter, hamOne, configurationSign_cfg_armOne,
      configurationSign_cfg_armTwo] at hs
    norm_num at hs

/-- Closed finite classification: the identity and the `0 1` transposition can only move a slot
to a distinct slot as `0 ↦ 1` or `1 ↦ 0`. -/
theorem root_index_pair_of_root_perm {i j : Fin 4}
    (h : ((1 : Equiv.Perm (Fin 4)) i = j ∨
      (Equiv.swap (0 : Fin 4) 1) i = j)) (hij : i ≠ j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  rcases h with h | h
  · exact absurd (by simpa using h) hij
  · fin_cases i <;> fin_cases j <;> simp_all <;>
      exact absurd h (by decide)

/-- Any distinct root branch transport is one of the two orientations of the carbon-arm pair. -/
theorem root_index_pair_of_branchTransport {i j : Fin 4} {b : Bool}
    (h : BranchTransport m cfg root i j b) (hij : i ≠ j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  rcases h with ⟨e, hroot, hlig, hsign⟩
  have hp := ligandPermAt_root_eq_one_or_swap e hroot
  have hcases : ((1 : Equiv.Perm (Fin 4)) i = j ∨
      (Equiv.swap (0 : Fin 4) 1) i = j) := by
    rcases hp with hp | hp
    · left
      simpa [hp] using hlig
    · right
      simpa [hp] using hlig
  exact root_index_pair_of_root_perm hcases hij

/-- Every distinct pair of root ligand slots is properly distinguishable. -/
theorem noProperTransport_root_distinct :
    ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport m cfg root i j := by
  intro i j hij hproper
  have hproper' : ProperTransport m cfg root i j := hproper
  rcases root_index_pair_of_branchTransport (b := false) hproper hij with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact noProperTransport_root_zero_one hproper'
  · exact noProperTransport_root_zero_one
      (branchTransport_inverse m cfg root hproper')

/-- The two carbon arms are the unique enantiomorphic root pair (orientation `0 → 1`). -/
theorem enantiomorphic_root_zero_one : Enantiomorphic m cfg root 0 1 :=
  ⟨by decide, mirrorTransport_root_zero_one, noProperTransport_root_zero_one⟩

/-- The same unique enantiomorphic root pair in the reverse orientation. -/
theorem enantiomorphic_root_one_zero : Enantiomorphic m cfg root 1 0 :=
  enantiomorphic_symm m cfg root enantiomorphic_root_zero_one

/-- **Exact root Enantiomorphic classification.**  The only ordered enantiomorphic pairs are the
two orientations of the carbon-arm pair. -/
theorem enantiomorphic_root_iff (i j : Fin 4) :
    Enantiomorphic m cfg root i j ↔ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  constructor
  · intro h
    exact root_index_pair_of_branchTransport h.2.1 h.1
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact enantiomorphic_root_zero_one
    · exact enantiomorphic_root_one_zero

/-- Branch `0` has exactly one enantiomorphic partner, slot `1`. -/
theorem existsUnique_enantiomorphicPartner_root_zero :
    ∃! j : Fin 4, Enantiomorphic m cfg root 0 j :=
  existsUnique_enantiomorphicPartner m cfg root 0 noProperTransport_root_distinct
    ⟨1, enantiomorphic_root_zero_one⟩

/-- Branch `1` has exactly one enantiomorphic partner, slot `0`. -/
theorem existsUnique_enantiomorphicPartner_root_one :
    ∃! j : Fin 4, Enantiomorphic m cfg root 1 j :=
  existsUnique_enantiomorphicPartner m cfg root 1 noProperTransport_root_distinct
    ⟨0, enantiomorphic_root_one_zero⟩

/-- The pairwise disjoint-branch domain holds at the root, derived from acyclicity and the exact
root ligand enumeration. -/
theorem pairwiseDisjointLigandBranches_root : PairwiseDisjointLigandBranches m root := by
  intro i j hij v hi hj
  have hcu : graph.Adj atom0 (m.ligandAtomAt root i) := by
    simpa [root] using m.ligandAtomAt_adj root i
  have hcv : graph.Adj atom0 (m.ligandAtomAt root j) := by
    simpa [root] using m.ligandAtomAt_adj root j
  exact hij (m.ligandAtomAt_injective root
    (cutBranch_disjoint_of_acyclic graph acyclic hcu hcv hi hj))

/-! ## The general rigid physical domain -/

/-- Both arms are constitutionally rigid and physically calibrated in the molecule's own ligand
enumeration. -/
theorem armOne_generalRigidCalibrated :
    ActualPhysicalGeneralRigidCalibratedCenter input.certified m cfg armOneCenter :=
  ⟨constitutionallyRigid_of_ligandAtomZ_injective armOne_zInjective,
    pointAt armOneCenter, armOne_observed, armOne_volume_ne_zero, armOne_sign⟩

theorem armTwo_generalRigidCalibrated :
    ActualPhysicalGeneralRigidCalibratedCenter input.certified m cfg armTwoCenter :=
  ⟨constitutionallyRigid_of_ligandAtomZ_injective armTwo_zInjective,
    pointAt armTwoCenter, armTwo_observed, armTwo_volume_ne_zero, armTwo_sign⟩

/-- **The general constitutionally rigid physical domain** is inhabited by the concrete molecule. -/
theorem generalRigidPhysicalDomain :
    ActualGeneralRigidPhysicalDomain input.certified m cfg root where
  graphEq := rfl
  centerCase := by
    intro center hcenter
    rcases center_eq_of_ne_root hcenter with rfl | rfl
    · exact Or.inr armOne_generalRigidCalibrated
    · exact Or.inr armTwo_generalRigidCalibrated

/-- Existence form of the general rigid physical domain. -/
theorem generalRigidPhysicalDomain_inhabited :
    ∃ (cfg : m.Configuration) (root : m.Center),
      ActualGeneralRigidPhysicalDomain input.certified m cfg root :=
  ⟨cfg, root, generalRigidPhysicalDomain⟩

/-! ## The physical nearest non-twin rule on every root branch -/

/-- The root as an automatically detected tetrahedral candidate. -/
def rootTetrahedral : input.certified.TetrahedralCenter :=
  ⟨atom0, by rw [← coverage]; exact root.2⟩

theorem armOne_candidate : atom1 ∈ input.certified.tetrahedralCenterSet := by
  rw [← coverage]
  exact armOneCenter.2

theorem armTwo_candidate : atom2 ∈ input.certified.tetrahedralCenterSet := by
  rw [← coverage]
  exact armTwoCenter.2

/-- The automatically detected molecule's arm-one centre is not a physical terminal twin. -/
theorem armOne_not_twin_detected :
    ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨atom1, armOne_candidate⟩ := by
  intro ht
  have hnotCustom : ¬ ActualPhysicalTerminalTwinCenter input.certified m armOneCenter :=
    actualPhysicalTerminalTwinCenter_false_of_calibrated armOne_calibrated
  exact hnotCustom
    (actualPhysicalTerminalTwinCenter_congr_mol
      (m₁ := input.certified.detectedMultiCenterMolecule) (m₂ := m)
      (c₁ := ⟨atom1, armOne_candidate⟩) (c₂ := armOneCenter)
      (by rw [detectedMultiCenter_mol]; rfl) rfl ht)

/-- The automatically detected molecule's arm-two centre is not a physical terminal twin. -/
theorem armTwo_not_twin_detected :
    ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨atom2, armTwo_candidate⟩ := by
  intro ht
  have hnotCustom : ¬ ActualPhysicalTerminalTwinCenter input.certified m armTwoCenter :=
    actualPhysicalTerminalTwinCenter_false_of_calibrated armTwo_calibrated
  exact hnotCustom
    (actualPhysicalTerminalTwinCenter_congr_mol
      (m₁ := input.certified.detectedMultiCenterMolecule) (m₂ := m)
      (c₁ := ⟨atom2, armTwo_candidate⟩) (c₂ := armTwoCenter)
      (by rw [detectedMultiCenter_mol]; rfl) rfl ht)

/-- Being a non-twin detected candidate is independent of the membership proof term. -/
theorem armOne_not_twin_detected_of_mem
    (candidate : atom1 ∈ input.certified.tetrahedralCenterSet) :
    ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨atom1, candidate⟩ := by
  intro ht
  exact armOne_not_twin_detected (by
    have hc : (⟨atom1, candidate⟩ : input.certified.TetrahedralCenter) =
        ⟨atom1, armOne_candidate⟩ := Subtype.ext rfl
    rwa [hc] at ht)

theorem armTwo_not_twin_detected_of_mem
    (candidate : atom2 ∈ input.certified.tetrahedralCenterSet) :
    ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨atom2, candidate⟩ := by
  intro ht
  exact armTwo_not_twin_detected (by
    have hc : (⟨atom2, candidate⟩ : input.certified.TetrahedralCenter) =
        ⟨atom2, armTwo_candidate⟩ := Subtype.ext rfl
    rwa [hc] at ht)

/-- The first carbon arm is a physical mark at the root. -/
theorem armOne_physicalMarked : PhysicalMarkedAtom input rootTetrahedral atom1 := by
  refine ⟨by decide, ?_⟩
  exact ⟨armOne_candidate, armOne_not_twin_detected⟩

/-- The second carbon arm is a physical mark at the root. -/
theorem armTwo_physicalMarked : PhysicalMarkedAtom input rootTetrahedral atom2 := by
  refine ⟨by decide, ?_⟩
  exact ⟨armTwo_candidate, armTwo_not_twin_detected⟩

/-- A terminal leaf with parent the root has a one-vertex deleted-root cut branch. -/
theorem cutBranch_leaf_eq_self {leaf : Atom} (hleaf : leaf ∈ leafSet)
    (hparent : leafParent leaf = atom0) {y : Atom}
    (hy : y ∈ CutBranch graph atom0 leaf) : y = leaf := by
  rcases hy with ⟨p, hp⟩
  by_cases hnil : p.Nil
  · have hlen : p.length = 0 := SimpleGraph.Walk.nil_iff_length_eq.mp hnil
    exact (SimpleGraph.Walk.eq_of_length_eq_zero hlen).symm
  · obtain ⟨u, hadj, q, hpq⟩ := SimpleGraph.Walk.not_nil_iff.mp hnil
    have hu : u = atom0 := by
      have h := adj_leaf_unique leaf u hleaf hadj
      simpa [hparent] using h
    subst hu
    rw [hpq] at hp
    exact False.elim (hp (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support q)))

theorem atom9_not_tetrahedral :
    atom9 ∉ input.certified.tetrahedralCenterSet := by
  rw [tetrahedralCenterSet_eq]
  decide +kernel

theorem atom10_not_tetrahedral :
    atom10 ∉ input.certified.tetrahedralCenterSet := by
  rw [tetrahedralCenterSet_eq]
  decide +kernel

/-- Root branch `2` (`Br`) contains no physical mark. -/
theorem branchTwo_no_marked :
    ∀ y : Atom,
      y ∈ ActualSlotCut input rootTetrahedral.1 (m.ligandAtomAt root 2) →
        ¬ PhysicalMarkedAtom input rootTetrahedral y := by
  intro y hy hmarked
  have hy' : y = atom9 :=
    cutBranch_leaf_eq_self (leaf := atom9) (by decide +kernel) (by decide +kernel) hy
  subst hy'
  rcases hmarked with ⟨_hne, candidate, _htwin⟩
  exact atom9_not_tetrahedral candidate

/-- Root branch `3` (`I`) contains no physical mark. -/
theorem branchThree_no_marked :
    ∀ y : Atom,
      y ∈ ActualSlotCut input rootTetrahedral.1 (m.ligandAtomAt root 3) →
        ¬ PhysicalMarkedAtom input rootTetrahedral y := by
  intro y hy hmarked
  have hy' : y = atom10 :=
    cutBranch_leaf_eq_self (leaf := atom10) (by decide +kernel) (by decide +kernel) hy
  subst hy'
  rcases hmarked with ⟨_hne, candidate, _htwin⟩
  exact atom10_not_tetrahedral candidate

/-- The first arm is the unique nearest physical mark in root branch `0`, at distance `0`. -/
theorem nearest_branch_zero :
    PhysicalBranchUniqueNearest input rootTetrahedral (m.ligandAtomAt root 0) atom1 0 := by
  refine ⟨?_, armOne_physicalMarked, ?_, ?_, ?_⟩
  · exact cutBranch_mem_self input.certified.moleculeGraph
      (by decide : graph.Adj atom0 atom1)
  · exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, rfl⟩
  · intro y _hy _hmarked walk _path hlen
    omega
  · intro y _hy _hmarked walk _path hlen
    exact (SimpleGraph.Walk.eq_of_length_eq_zero hlen).symm

/-- The second arm is the unique nearest physical mark in root branch `1`, at distance `0`. -/
theorem nearest_branch_one :
    PhysicalBranchUniqueNearest input rootTetrahedral (m.ligandAtomAt root 1) atom2 0 := by
  refine ⟨?_, armTwo_physicalMarked, ?_, ?_, ?_⟩
  · exact cutBranch_mem_self input.certified.moleculeGraph
      (by decide : graph.Adj atom0 atom2)
  · exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, rfl⟩
  · intro y _hy _hmarked walk _path hlen
    omega
  · intro y _hy _hmarked walk _path hlen
    exact (SimpleGraph.Walk.eq_of_length_eq_zero hlen).symm





theorem physicalBranchDomain_all :
    ∀ i : Fin 4, PhysicalBranchDomain input rootTetrahedral (m.ligandAtomAt root i) := by
  intro i
  fin_cases i
  · exact Or.inr ⟨atom1, 0, nearest_branch_zero⟩
  · exact Or.inr ⟨atom2, 0, nearest_branch_one⟩
  · exact Or.inl branchTwo_no_marked
  · exact Or.inl branchThree_no_marked

/-- The two carbon branches are the only branches with a nearest mark, and each has exactly one. -/
theorem nearestBranchSummary :
    PhysicalBranchUniqueNearest input rootTetrahedral (m.ligandAtomAt root 0) atom1 0 ∧
      PhysicalBranchUniqueNearest input rootTetrahedral (m.ligandAtomAt root 1) atom2 0 ∧
        (∀ y : Atom,
          y ∈ ActualSlotCut input rootTetrahedral.1 (m.ligandAtomAt root 2) →
            ¬ PhysicalMarkedAtom input rootTetrahedral y) ∧
          (∀ y : Atom,
            y ∈ ActualSlotCut input rootTetrahedral.1 (m.ligandAtomAt root 3) →
              ¬ PhysicalMarkedAtom input rootTetrahedral y) :=
  ⟨nearest_branch_zero, nearest_branch_one, branchTwo_no_marked, branchThree_no_marked⟩








private theorem actualGeneralRigidPhysicalDomain_cast
    {m₁ m₂ : MultiCenterMolecule Atom}
    (h : m₁ = m₂) (cfg : m₁.Configuration) (root : m₁.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified m₁ cfg root) :
    ActualGeneralRigidPhysicalDomain input.certified m₂ (h ▸ cfg) (h ▸ root) := by
  cases h
  exact domain

private theorem pairwiseProperDistinguishable_cast
    {m₁ m₂ : MultiCenterMolecule Atom}
    (h : m₁ = m₂) (cfg : m₁.Configuration) (root : m₁.Center)
    (distinct : MultiCenterMolecule.PairwiseProperDistinguishable m₁ cfg root) :
    MultiCenterMolecule.PairwiseProperDistinguishable m₂ (h ▸ cfg) (h ▸ root) := by
  cases h
  exact distinct

private theorem enantiomorphic_cast
    {m₁ m₂ : MultiCenterMolecule Atom}
    (h : m₁ = m₂) (cfg : m₁.Configuration) (root : m₁.Center) (i j : Fin 4)
    (pair : Enantiomorphic m₁ cfg root i j) :
    Enantiomorphic m₂ (h ▸ cfg) (h ▸ root) i j := by
  cases h
  exact pair

private theorem enantiomorphic_iff_cast
    {m₁ m₂ : MultiCenterMolecule Atom}
    (h : m₁ = m₂) (cfg : m₁.Configuration) (root : m₁.Center)
    (R : Fin 4 → Fin 4 → Prop)
    (classification : ∀ i j : Fin 4, Enantiomorphic m₁ cfg root i j ↔ R i j) :
    ∀ i j : Fin 4, Enantiomorphic m₂ (h ▸ cfg) (h ▸ root) i j ↔ R i j := by
  cases h
  exact classification

private theorem physicalEnantiomorphicPairCount_cast
    {m₁ m₂ : MultiCenterMolecule Atom}
    (h : m₁ = m₂) (cfg : m₁.Configuration) (root : m₁.Center)
    (count : physicalEnantiomorphicPairCount m₁ cfg root = 1) :
    physicalEnantiomorphicPairCount m₂ (h ▸ cfg) (h ▸ root) = 1 := by
  cases h
  exact count

private theorem pairwiseDisjointLigandBranches_cast
    {m₁ m₂ : MultiCenterMolecule Atom}
    (h : m₁ = m₂) (root : m₁.Center)
    (disjoint : PairwiseDisjointLigandBranches m₁ root) :
    PairwiseDisjointLigandBranches m₂ (h ▸ root) := by
  cases h
  exact disjoint

private theorem physicalBranchDomain_cast
    {m₁ m₂ : MultiCenterMolecule Atom}
    (h : m₁ = m₂) (root : m₁.Center)
    (domain : ∀ i : Fin 4,
      PhysicalBranchDomain input rootTetrahedral (m₁.ligandAtomAt root i)) :
    ∀ i : Fin 4,
      PhysicalBranchDomain input rootTetrahedral (m₂.ligandAtomAt (h ▸ root) i) := by
  cases h
  exact domain

/-- There is a per-center ligand reindexing from the explicit enumeration to the automatically
detected one. -/
theorem exists_detectedReindex :
    ∃ τ : m.Center → Equiv.Perm (Fin 4),
      m.reindexFrames τ = input.certified.detectedMultiCenterMolecule :=
  input.certified.exists_reindexFrames_detectedMultiCenterMolecule rfl coverage



theorem reindexed_generalRigidPhysicalDomain
    (τ : m.Center → Equiv.Perm (Fin 4)) :
    ActualGeneralRigidPhysicalDomain input.certified (m.reindexFrames τ)
      (m.reindexConfiguration τ cfg) root :=
  actualGeneralRigidPhysicalDomain_reindexFrames input.certified m cfg root τ
    generalRigidPhysicalDomain

/-- Root pairwise proper-distinguishability transports to the reindexed enumeration. -/
theorem reindexed_pairwiseProperDistinguishable
    (τ : m.Center → Equiv.Perm (Fin 4)) :
    MultiCenterMolecule.PairwiseProperDistinguishable (m.reindexFrames τ)
      (m.reindexConfiguration τ cfg) root :=
  (MultiCenterMolecule.pairwiseProperDistinguishable_reindexFrames_iff m τ cfg root).mpr
    noProperTransport_root_distinct

/-- Root pairwise disjointness of ligand branches transports to the reindexed enumeration. -/
theorem reindexed_pairwiseDisjointLigandBranches
    (τ : m.Center → Equiv.Perm (Fin 4)) :
    PairwiseDisjointLigandBranches (m.reindexFrames τ) root :=
  (MultiCenterMolecule.pairwiseDisjointLigandBranches_reindexFrames_iff m τ root).mpr
    pairwiseDisjointLigandBranches_root

/-- **Exact root Enantiomorphic classification after reindexing.**  The two enantiomorphic slots
are the preimages under `τ root` of the original arm slots `0` and `1`. -/
theorem reindexed_enantiomorphic_iff
    (τ : m.Center → Equiv.Perm (Fin 4)) (i j : Fin 4) :
    Enantiomorphic (m.reindexFrames τ) (m.reindexConfiguration τ cfg) root i j ↔
      (i = (τ root)⁻¹ 0 ∧ j = (τ root)⁻¹ 1) ∨
        (i = (τ root)⁻¹ 1 ∧ j = (τ root)⁻¹ 0) := by
  rw [MultiCenterMolecule.enantiomorphic_reindexFrames_iff, enantiomorphic_root_iff]
  constructor
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · calc i = (τ root)⁻¹ (τ root i) := (Equiv.symm_apply_apply (τ root) i).symm
          _ = (τ root)⁻¹ 0 := by rw [h0]
      · calc j = (τ root)⁻¹ (τ root j) := (Equiv.symm_apply_apply (τ root) j).symm
          _ = (τ root)⁻¹ 1 := by rw [h1]
    · refine Or.inr ⟨?_, ?_⟩
      · calc i = (τ root)⁻¹ (τ root i) := (Equiv.symm_apply_apply (τ root) i).symm
          _ = (τ root)⁻¹ 1 := by rw [h0]
      · calc j = (τ root)⁻¹ (τ root j) := (Equiv.symm_apply_apply (τ root) j).symm
          _ = (τ root)⁻¹ 0 := by rw [h1]
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · calc τ root i = τ root ((τ root)⁻¹ 0) := by rw [h0]
          _ = 0 := Equiv.apply_symm_apply (τ root) 0
      · calc τ root j = τ root ((τ root)⁻¹ 1) := by rw [h1]
          _ = 1 := Equiv.apply_symm_apply (τ root) 1
    · refine Or.inr ⟨?_, ?_⟩
      · calc τ root i = τ root ((τ root)⁻¹ 1) := by rw [h0]
          _ = 1 := Equiv.apply_symm_apply (τ root) 1
      · calc τ root j = τ root ((τ root)⁻¹ 0) := by rw [h1]
          _ = 0 := Equiv.apply_symm_apply (τ root) 0

/-- The two arm branches after reindexing are the unique enantiomorphic root pair. -/
theorem reindexed_enantiomorphic_arms
    (τ : m.Center → Equiv.Perm (Fin 4)) :
    Enantiomorphic (m.reindexFrames τ) (m.reindexConfiguration τ cfg) root
      ((τ root)⁻¹ 0) ((τ root)⁻¹ 1) :=
  (reindexed_enantiomorphic_iff τ _ _).mpr (Or.inl ⟨rfl, rfl⟩)

/-- The physical enantiomorphic pair count at the root is exactly one. -/
theorem physicalEnantiomorphicPairCount_root :
    physicalEnantiomorphicPairCount m cfg root = 1 := by
  rw [physicalEnantiomorphicPairCount_eq_one_iff]
  refine ⟨0, 1, by decide, enantiomorphic_root_zero_one, ?_⟩
  intro a b _hab h
  rcases (enantiomorphic_root_iff a b).mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- The pair count remains one after reindexing to the detected enumeration. -/
theorem reindexed_physicalEnantiomorphicPairCount
    (τ : m.Center → Equiv.Perm (Fin 4)) :
    physicalEnantiomorphicPairCount (m.reindexFrames τ)
      (m.reindexConfiguration τ cfg) root = 1 := by
  rw [physicalEnantiomorphicPairCount_reindexFrames]
  exact physicalEnantiomorphicPairCount_root

/-- The physical nearest non-twin branch domain transports to the reindexed slot numbering. -/
theorem reindexed_physicalBranchDomain_all
    (τ : m.Center → Equiv.Perm (Fin 4)) :
    ∀ i : Fin 4, PhysicalBranchDomain input rootTetrahedral
      ((m.reindexFrames τ).ligandAtomAt root i) := by
  intro i
  change PhysicalBranchDomain input rootTetrahedral (m.ligandAtomAt root (τ root i))
  exact physicalBranchDomain_all (τ root i)














theorem detected_physicalWitness :
    ∃ τ : m.Center → Equiv.Perm (Fin 4),
      m.reindexFrames τ = input.certified.detectedMultiCenterMolecule ∧
      ActualGeneralRigidPhysicalDomain input.certified (m.reindexFrames τ)
        (m.reindexConfiguration τ cfg) root ∧
      MultiCenterMolecule.PairwiseProperDistinguishable (m.reindexFrames τ)
        (m.reindexConfiguration τ cfg) root ∧
      Enantiomorphic (m.reindexFrames τ) (m.reindexConfiguration τ cfg) root
        ((τ root)⁻¹ 0) ((τ root)⁻¹ 1) ∧
      (∀ i j : Fin 4,
        Enantiomorphic (m.reindexFrames τ) (m.reindexConfiguration τ cfg) root i j ↔
          (i = (τ root)⁻¹ 0 ∧ j = (τ root)⁻¹ 1) ∨
            (i = (τ root)⁻¹ 1 ∧ j = (τ root)⁻¹ 0)) ∧
      physicalEnantiomorphicPairCount (m.reindexFrames τ)
        (m.reindexConfiguration τ cfg) root = 1 ∧
      PairwiseDisjointLigandBranches (m.reindexFrames τ) root ∧
      (∀ i : Fin 4, PhysicalBranchDomain input rootTetrahedral
        ((m.reindexFrames τ).ligandAtomAt root i)) := by
  obtain ⟨τ, hτ⟩ := exists_detectedReindex
  exact ⟨τ, hτ, reindexed_generalRigidPhysicalDomain τ,
    reindexed_pairwiseProperDistinguishable τ, reindexed_enantiomorphic_arms τ,
    reindexed_enantiomorphic_iff τ, reindexed_physicalEnantiomorphicPairCount τ,
    reindexed_pairwiseDisjointLigandBranches τ, reindexed_physicalBranchDomain_all τ⟩




theorem detected_physicalWitness_actual :
    ∃ (τ : m.Center → Equiv.Perm (Fin 4))
      (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
      (cfgD : input.certified.detectedMultiCenterMolecule.Configuration)
      (rootD : input.certified.detectedMultiCenterMolecule.Center),
      cfgD = hτ ▸ m.reindexConfiguration τ cfg ∧
      rootD = hτ ▸ root ∧
      ActualGeneralRigidPhysicalDomain input.certified
        input.certified.detectedMultiCenterMolecule cfgD rootD ∧
      MultiCenterMolecule.PairwiseProperDistinguishable
        input.certified.detectedMultiCenterMolecule cfgD rootD ∧
      Enantiomorphic input.certified.detectedMultiCenterMolecule cfgD rootD
        ((τ root)⁻¹ 0) ((τ root)⁻¹ 1) ∧
      (∀ i j : Fin 4,
        Enantiomorphic input.certified.detectedMultiCenterMolecule cfgD rootD i j ↔
          (i = (τ root)⁻¹ 0 ∧ j = (τ root)⁻¹ 1) ∨
            (i = (τ root)⁻¹ 1 ∧ j = (τ root)⁻¹ 0)) ∧
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
        cfgD rootD = 1 ∧
      PairwiseDisjointLigandBranches input.certified.detectedMultiCenterMolecule rootD ∧
      (∀ i : Fin 4, PhysicalBranchDomain input rootTetrahedral
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD i)) := by
  obtain ⟨τ, hτ⟩ := exists_detectedReindex
  refine ⟨τ, hτ, hτ ▸ m.reindexConfiguration τ cfg, hτ ▸ root, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact actualGeneralRigidPhysicalDomain_cast hτ _ _
      (reindexed_generalRigidPhysicalDomain τ)
  · exact pairwiseProperDistinguishable_cast hτ _ _
      (reindexed_pairwiseProperDistinguishable τ)
  · exact enantiomorphic_cast hτ _ _ _ _ (reindexed_enantiomorphic_arms τ)
  · exact enantiomorphic_iff_cast hτ _ _ _ (reindexed_enantiomorphic_iff τ)
  · exact physicalEnantiomorphicPairCount_cast hτ _ _
      (reindexed_physicalEnantiomorphicPairCount τ)
  · exact pairwiseDisjointLigandBranches_cast hτ _
      (reindexed_pairwiseDisjointLigandBranches τ)
  · exact physicalBranchDomain_cast hτ _ (reindexed_physicalBranchDomain_all τ)

/-! ## Kernel-authority guards for every public declaration -/

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.periodicElement
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.carbon
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.hydrogen
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.fluorine
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.chlorine
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.bromine
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.iodine
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.singleBond
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.source
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.source_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.source_localizedGraphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.source_noDoubleTest
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.source_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.certifiedSource
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.localizedSource
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.input
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.admission
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.input_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.Atom
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.graph
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom0
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom1
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom3
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom4
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom5
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom6
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom7
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom8
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom9
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom10
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.rootLigand
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOneLigand
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwoLigand
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandAt
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.m
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOneCenter
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwoCenter
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.tetrahedralCenterSet_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.coverage
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.adj_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.adj_atom0_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.adj_atom1_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.adj_atom2_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.leafSet
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.leafParent
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.adj_leaf_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.carbonAtoms
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.leafSet_not_carbon
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom0
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom1
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom3
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom4
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom5
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom6
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom7
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom8
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom9
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atomZ_atom10
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom0
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom1
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom3
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom4
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom5
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom6
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom7
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom8
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom9
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointOfAtom_atom10
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.spatialPointAt_atom
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.simpleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.constantFormalCharge
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.cycle_vertex_mem_carbonAtoms
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.acyclic
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.cfg
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.cfg_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.cfg_armOne
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.cfg_armTwo
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointAt
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandAtomAt_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.rootLigand_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.rootLigand_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.rootLigand_two
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.rootLigand_three
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandAtomAt_armOne
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandAtomAt_armTwo
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.rootPoints
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOnePoints
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwoPoints
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointAt_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointAt_armOne
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pointAt_armTwo
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_zInjective
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_zInjective
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_observed
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_observed
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.root_volume
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.root_volume_ne_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.root_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_volume
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_volume
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_volume_ne_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_volume_ne_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.center_eq_of_ne_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.globalPhysicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.physicalDomain_inhabited
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwapPerm
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom0
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom1
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom3
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom4
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom5
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom6
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom7
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom8
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom9
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_apply_atom10
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_atomZ
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_atomMass
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_formalCharge
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_bond
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_mem_graphAut
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwap_preservesCenters
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armSwapAut
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.centerPerm_armSwap_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.centerPerm_armSwap_armOne
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.centerPerm_armSwap_armTwo
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandPermAt_armSwap_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandPermAt_armSwap_armOne
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandPermAt_armSwap_armTwo
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_adj_image
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_atomZ_image
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_root_neighbor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_atom9_of_fixes_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_atom10_of_fixes_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_atom1_eq_atom1_or_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_atom2_eq_atom1_or_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_atom3_of_atom1_to_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_atom4_of_atom1_to_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.aut_atom5_of_atom1_to_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandPermAt_root_eq_one_or_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.ligandPermAt_armOne_eq_one_of_atom1_to_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.root_not_mem_ligandBranch
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.root_not_mem_branch_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_mem_branch_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_mem_branch_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_not_mem_branch_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_not_mem_branch_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.center_eq_armOne_of_branch_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.center_eq_armTwo_of_branch_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.configurationSign_cfg_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.configurationSign_cfg_armOne
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.configurationSign_cfg_armTwo
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.mirrorTransport_root_zero_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.noProperTransport_root_zero_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.root_index_pair_of_root_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.root_index_pair_of_branchTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.noProperTransport_root_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.enantiomorphic_root_zero_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.enantiomorphic_root_one_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.enantiomorphic_root_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.existsUnique_enantiomorphicPartner_root_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.existsUnique_enantiomorphicPartner_root_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.pairwiseDisjointLigandBranches_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_generalRigidCalibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_generalRigidCalibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.generalRigidPhysicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.generalRigidPhysicalDomain_inhabited
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.rootTetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_candidate
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_candidate
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_not_twin_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_not_twin_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_not_twin_detected_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_not_twin_detected_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armOne_physicalMarked
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.armTwo_physicalMarked
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.cutBranch_leaf_eq_self
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom9_not_tetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.atom10_not_tetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.branchTwo_no_marked
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.branchThree_no_marked
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.nearest_branch_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.nearest_branch_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.physicalBranchDomain_all
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.nearestBranchSummary
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.exists_detectedReindex
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.reindexed_generalRigidPhysicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.reindexed_pairwiseProperDistinguishable
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.reindexed_pairwiseDisjointLigandBranches
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.reindexed_enantiomorphic_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.reindexed_enantiomorphic_arms
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.physicalEnantiomorphicPairCount_root
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.reindexed_physicalEnantiomorphicPairCount
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.reindexed_physicalBranchDomain_all
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.detected_physicalWitness
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity.detected_physicalWitness_actual

end TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity
