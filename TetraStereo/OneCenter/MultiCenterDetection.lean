import TetraStereo.OneCenter.MultiCenterSymmetry
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
  Automatic graph-level detection of tetrahedral-center candidates.

  `MultiCenterMolecule` still stores explicit ligand enumerations, because most downstream
  stereochemical constructions need indexed tetrahedral frames.  This file supplies the bridge from
  a bare molecular graph to those indexed views whenever a vertex has exactly four neighbors.
-/

/-- The finset of graph vertices with exactly four adjacent atoms. -/
def tetrahedralCenterSet (m : MoleculeGraph V) : Finset V :=
  (Finset.univ : Finset V).filter fun c => (m.neighborFinset c).card = 4

theorem isTetrahedralCenter_iff_neighborFinset_card (m : MoleculeGraph V) (c : V) :
    m.IsTetrahedralCenter c ↔ (m.neighborFinset c).card = 4 := by
  classical
  have hcard : Fintype.card (m.Neighbor c) = (m.neighborFinset c).card := by
    exact Fintype.card_of_subtype (m.neighborFinset c) (by intro x; simp [MoleculeGraph.mem_neighborFinset])
  simp [IsTetrahedralCenter, hcard]

@[simp] theorem mem_tetrahedralCenterSet (m : MoleculeGraph V) (c : V) :
    c ∈ m.tetrahedralCenterSet ↔ m.IsTetrahedralCenter c := by
  simp [tetrahedralCenterSet, m.isTetrahedralCenter_iff_neighborFinset_card c]

/-- The subtype of automatically detected tetrahedral-center candidates. -/
abbrev TetrahedralCenter (m : MoleculeGraph V) : Type _ :=
  { c : V // c ∈ m.tetrahedralCenterSet }

theorem isTetrahedralCenter_of_tetrahedralCenter (m : MoleculeGraph V)
    (c : m.TetrahedralCenter) : m.IsTetrahedralCenter c.1 := by
  simpa using (m.mem_tetrahedralCenterSet c.1).1 c.2

theorem isTetrahedralCenter_apply_aut_iff (m : MoleculeGraph V) (e : m.Aut) (c : V) :
    m.IsTetrahedralCenter ((e : Equiv.Perm V) c) ↔ m.IsTetrahedralCenter c := by
  classical
  have hcard :
      Fintype.card (m.Neighbor c) = Fintype.card (m.Neighbor ((e : Equiv.Perm V) c)) :=
    Fintype.card_congr (m.neighborEquiv e c)
  constructor
  · intro h
    simpa [IsTetrahedralCenter, hcard] using h
  · intro h
    simpa [IsTetrahedralCenter, hcard] using h

theorem mem_tetrahedralCenterSet_apply_aut_iff (m : MoleculeGraph V) (e : m.Aut) (c : V) :
    c ∈ m.tetrahedralCenterSet ↔ (e : Equiv.Perm V) c ∈ m.tetrahedralCenterSet := by
  simp [m.isTetrahedralCenter_apply_aut_iff e c]

/-- Regard a graph vertex with four neighbors as a one-center molecule by choosing an enumeration of
those four neighbors. -/
noncomputable def toOneCenterMoleculeOfIsTetrahedralCenter (m : MoleculeGraph V) (c : V)
    (h : m.IsTetrahedralCenter c) : OneCenterMolecule V where
  mol := m
  center := c
  ligandAtom := fun i => (m.ligandEquivOfIsTetrahedralCenter c h i).1
  ligandAtom_adj := by
    intro i
    exact (m.ligandEquivOfIsTetrahedralCenter c h i).2
  ligandAtom_injective := by
    intro i j hij
    apply (m.ligandEquivOfIsTetrahedralCenter c h).injective
    exact Subtype.ext hij
  ligandAtom_surjective := by
    intro v hv
    let n : m.Neighbor c := ⟨v, hv⟩
    refine ⟨(m.ligandEquivOfIsTetrahedralCenter c h).symm n, ?_⟩
    exact congrArg Subtype.val ((m.ligandEquivOfIsTetrahedralCenter c h).apply_symm_apply n)

/-- The one-center molecule attached to an automatically detected tetrahedral-center candidate. -/
noncomputable def detectedOneCenterMolecule (m : MoleculeGraph V) (c : m.TetrahedralCenter) :
    OneCenterMolecule V :=
  m.toOneCenterMoleculeOfIsTetrahedralCenter c.1 (m.isTetrahedralCenter_of_tetrahedralCenter c)

/-- A `MultiCenterMolecule` whose distinguished centers are all graph vertices with exactly four
neighbors. -/
noncomputable def detectedMultiCenterMolecule (m : MoleculeGraph V) : MultiCenterMolecule V where
  mol := m
  centers := m.tetrahedralCenterSet
  ligandAtom := fun c hc i =>
    (m.ligandEquivOfIsTetrahedralCenter c ((m.mem_tetrahedralCenterSet c).1 hc) i).1
  ligandAtom_adj := by
    intro c hc i
    exact (m.ligandEquivOfIsTetrahedralCenter c ((m.mem_tetrahedralCenterSet c).1 hc) i).2
  ligandAtom_injective := by
    intro c hc i j hij
    apply (m.ligandEquivOfIsTetrahedralCenter c ((m.mem_tetrahedralCenterSet c).1 hc)).injective
    exact Subtype.ext hij
  ligandAtom_surjective := by
    intro c hc v hv
    let n : m.Neighbor c := ⟨v, hv⟩
    refine ⟨(m.ligandEquivOfIsTetrahedralCenter c ((m.mem_tetrahedralCenterSet c).1 hc)).symm n, ?_⟩
    exact congrArg Subtype.val
      ((m.ligandEquivOfIsTetrahedralCenter c ((m.mem_tetrahedralCenterSet c).1 hc)).apply_symm_apply n)

@[simp] theorem detectedMultiCenterMolecule_centers (m : MoleculeGraph V) :
    m.detectedMultiCenterMolecule.centers = m.tetrahedralCenterSet := rfl

theorem mem_detectedMultiCenterMolecule_centers_iff (m : MoleculeGraph V) (c : V) :
    c ∈ m.detectedMultiCenterMolecule.centers ↔ m.IsTetrahedralCenter c := by
  simp [detectedMultiCenterMolecule]

theorem detectedMultiCenterMolecule_preservesCenters_of_aut (m : MoleculeGraph V) (e : m.Aut) :
    m.detectedMultiCenterMolecule.PreservesCenters (e : Equiv.Perm V) := by
  intro c
  exact m.mem_tetrahedralCenterSet_apply_aut_iff e c

/-- Any graph automorphism acts as a multi-center automorphism of the automatically detected
stereo system. -/
def detectedMultiCenterAutOfGraphAut (m : MoleculeGraph V) (e : m.Aut) :
    m.detectedMultiCenterMolecule.Aut :=
  ⟨(e : Equiv.Perm V), ⟨e.property, m.detectedMultiCenterMolecule_preservesCenters_of_aut e⟩⟩

end MoleculeGraph

end OneCenter
end TetraStereo
