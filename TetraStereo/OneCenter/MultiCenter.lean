import TetraStereo.OneCenter.Symmetry
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The (typed) set of atoms adjacent to `c`. -/
abbrev Neighbor (m : MoleculeGraph V) (c : V) : Type _ :=
  { v : V // m.Adj c v }

/-- A vertex is a *tetrahedral center* when it has exactly four neighbors. -/
def IsTetrahedralCenter (m : MoleculeGraph V) (c : V) : Prop :=
  Fintype.card (m.Neighbor c) = 4

/-- Choose an equivalence between `Fin 4` and the neighbors of a tetrahedral center. -/
noncomputable def ligandEquivOfIsTetrahedralCenter (m : MoleculeGraph V) (c : V)
    (h : m.IsTetrahedralCenter c) : Fin 4 ≃ m.Neighbor c := by
  classical
  have hcard : Fintype.card (Fin 4) = Fintype.card (m.Neighbor c) := by
    simpa [IsTetrahedralCenter, Neighbor] using h.symm
  exact Fintype.equivOfCardEq hcard

/-- Automorphisms of `m` that fix a chosen center. -/
def CenterAut (m : MoleculeGraph V) (c : V) : Subgroup (Equiv.Perm V) where
  carrier := { e | e ∈ m.Aut ∧ e c = c }
  one_mem' := by
    refine ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_⟩
    calc
      (a * b) c = a (b c) := rfl
      _ = a c := by simp [hb.2]
      _ = c := ha.2
  inv_mem' := by
    intro a ha
    refine ⟨Subgroup.inv_mem _ ha.1, ?_⟩
    have h := congrArg (fun x => a⁻¹ x) ha.2
    simpa using h.symm

namespace CenterAut

variable (m : MoleculeGraph V) (c : V)

@[simp] theorem mem_molAut (e : m.CenterAut c) : (e : Equiv.Perm V) ∈ m.Aut :=
  e.property.1

@[simp] theorem apply_center (e : m.CenterAut c) : (e : Equiv.Perm V) c = c :=
  e.property.2

end CenterAut

/-- The induced permutation on the neighbor subtype coming from a center-fixing automorphism. -/
noncomputable def neighborPerm (m : MoleculeGraph V) (c : V) (e : m.CenterAut c) :
    Equiv.Perm (m.Neighbor c) := by
  classical
  let eMol : m.Aut := ⟨(e : Equiv.Perm V), e.property.1⟩
  refine
    { toFun := fun v => ⟨(e : Equiv.Perm V) v.1, ?_⟩
      invFun := fun v => ⟨((e : Equiv.Perm V)⁻¹) v.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- adjacency for `toFun`
    have : m.Adj ((e : Equiv.Perm V) c) ((e : Equiv.Perm V) v.1) := (MoleculeGraph.Aut.adj_iff (m := m) eMol c v.1).2 v.2
    simpa [e.property.2] using this
  · -- adjacency for `invFun`
    have heInv : ((e : Equiv.Perm V)⁻¹) ∈ m.Aut :=
      Subgroup.inv_mem _ e.property.1
    let eInvMol : m.Aut := ⟨((e : Equiv.Perm V)⁻¹), heInv⟩
    have hcenter : ((e : Equiv.Perm V)⁻¹) c = c := by
      -- `e⁻¹` is again a center-fixing automorphism.
      simpa using (MoleculeGraph.CenterAut.apply_center (m := m) (c := c) (e := (e⁻¹ : m.CenterAut c)))
    have : m.Adj (((e : Equiv.Perm V)⁻¹) c) (((e : Equiv.Perm V)⁻¹) v.1) := (MoleculeGraph.Aut.adj_iff (m := m) eInvMol c v.1).2 v.2
    simpa [hcenter] using this
  · intro v
    apply Subtype.ext
    simp
  · intro v
    apply Subtype.ext
    simp

/-- The induced permutation on ligand indices from a center-fixing automorphism, given a proof that
the center has exactly four neighbors. -/
noncomputable def ligandPermOfIsTetrahedralCenter (m : MoleculeGraph V) (c : V)
    (h : m.IsTetrahedralCenter c) (e : m.CenterAut c) : Equiv.Perm (Fin 4) :=
  (m.ligandEquivOfIsTetrahedralCenter c h).trans (m.neighborPerm c e) |>.trans
    (m.ligandEquivOfIsTetrahedralCenter c h).symm

end MoleculeGraph

/-- A molecular graph together with a (finite) set of distinguished tetrahedral centers.

Each distinguished center comes with an explicit enumeration of its four adjacent ligand atoms. -/
structure MultiCenterMolecule (V : Type*) [Fintype V] [DecidableEq V] where
  mol : MoleculeGraph V
  centers : Finset V
  ligandAtom : ∀ c, c ∈ centers → Fin 4 → V
  ligandAtom_adj : ∀ c hc i, mol.Adj c (ligandAtom c hc i)
  ligandAtom_injective : ∀ c hc, Function.Injective (ligandAtom c hc)
  /-- The four ligand atoms enumerate all neighbors of the distinguished center. -/
  ligandAtom_surjective : ∀ c hc v, mol.Adj c v → ∃ i, ligandAtom c hc i = v

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The type of distinguished centers of a `MultiCenterMolecule`. -/
abbrev Center (m : MultiCenterMolecule V) : Type _ :=
  { c : V // c ∈ m.centers }

/-- The ligand enumeration at a distinguished center. -/
abbrev ligandAtomAt (m : MultiCenterMolecule V) (c : m.Center) : Fin 4 → V :=
  m.ligandAtom c.1 c.2

@[simp] theorem ligandAtomAt_adj (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) :
    m.mol.Adj c.1 (m.ligandAtomAt c i) :=
  m.ligandAtom_adj c.1 c.2 i

theorem ligandAtomAt_injective (m : MultiCenterMolecule V) (c : m.Center) :
    Function.Injective (m.ligandAtomAt c) :=
  m.ligandAtom_injective c.1 c.2

theorem ligandAtomAt_surjective (m : MultiCenterMolecule V) (c : m.Center) (v : V) :
    m.mol.Adj c.1 v → ∃ i, m.ligandAtomAt c i = v :=
  m.ligandAtom_surjective c.1 c.2 v

/-- Regard a distinguished center of a `MultiCenterMolecule` as a `OneCenterMolecule`. -/
noncomputable def toOneCenterMolecule (m : MultiCenterMolecule V) (c : m.Center) :
    OneCenterMolecule V where
  mol := m.mol
  center := c.1
  ligandAtom := m.ligandAtomAt c
  ligandAtom_adj := by
    intro i
    exact m.ligandAtomAt_adj c i
  ligandAtom_injective := m.ligandAtomAt_injective c
  ligandAtom_surjective := by
    intro v hv
    exact m.ligandAtomAt_surjective c v hv

/-- The ligand enumeration as an equivalence between the four indices and the neighbors of a
distinguished center. -/
noncomputable def ligandEquiv (m : MultiCenterMolecule V) (c : m.Center) :
    Fin 4 ≃ m.mol.Neighbor c.1 := by
  classical
  refine
    { toFun := fun i => ⟨m.ligandAtomAt c i, m.ligandAtomAt_adj c i⟩
      invFun := fun v => Classical.choose (m.ligandAtomAt_surjective c v.1 v.2)
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    have h :=
      Classical.choose_spec (m.ligandAtomAt_surjective c (m.ligandAtomAt c i) (m.ligandAtomAt_adj c i))
    exact m.ligandAtomAt_injective c h
  · intro v
    apply Subtype.ext
    exact Classical.choose_spec (m.ligandAtomAt_surjective c v.1 v.2)

end MultiCenterMolecule

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The distinguished center of a `OneCenterMolecule` is a tetrahedral center (it has exactly four
neighbors). -/
theorem isTetrahedralCenter (m : OneCenterMolecule V) : m.mol.IsTetrahedralCenter m.center := by
  classical
  -- Use the `Fin 4 ≃ Neighbor` equivalence already bundled for a one-center molecule.
  have e : Fin 4 ≃ m.mol.Neighbor m.center := by
    simpa [MoleculeGraph.Neighbor, OneCenterMolecule.Neighbor] using m.ligandEquiv
  have hcard : Fintype.card (m.mol.Neighbor m.center) = 4 := by
    -- `card Neighbor = card (Fin 4) = 4`.
    simpa using (Fintype.card_congr e).symm
  simpa [MoleculeGraph.IsTetrahedralCenter] using hcard

/-- Regard a `OneCenterMolecule` as a `MultiCenterMolecule` with a singleton set of centers. -/
noncomputable def toMultiCenterMolecule (m : OneCenterMolecule V) : MultiCenterMolecule V where
  mol := m.mol
  centers := {m.center}
  ligandAtom := by
    intro c hc
    have : c = m.center := by simpa using hc
    cases this
    exact m.ligandAtom
  ligandAtom_adj := by
    intro c hc i
    have : c = m.center := by simpa using hc
    cases this
    simpa using m.ligandAtom_adj i
  ligandAtom_injective := by
    intro c hc
    have : c = m.center := by simpa using hc
    cases this
    simpa using m.ligandAtom_injective
  ligandAtom_surjective := by
    intro c hc v hv
    have : c = m.center := by simpa using hc
    cases this
    exact m.ligandAtom_surjective v hv

end OneCenterMolecule

end
end OneCenter
end TetraStereo
