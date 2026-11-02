import TetraStereo.OneCenter.MultiCenter

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An automorphism of `m` transports the neighbors of `c` to the neighbors of `e c`. -/
noncomputable def neighborEquiv (m : MoleculeGraph V) (e : m.Aut) (c : V) :
    m.Neighbor c ≃ m.Neighbor ((e : Equiv.Perm V) c) := by
  classical
  refine
    { toFun := fun v => ⟨(e : Equiv.Perm V) v.1, ?_⟩
      invFun := fun v => ⟨((e : Equiv.Perm V)⁻¹) v.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have : m.Adj ((e : Equiv.Perm V) c) ((e : Equiv.Perm V) v.1) :=
      (MoleculeGraph.Aut.adj_iff (m := m) e c v.1).2 v.2
    simpa using this
  · have :
        m.Adj (((e⁻¹ : m.Aut) : Equiv.Perm V) ((e : Equiv.Perm V) c))
          (((e⁻¹ : m.Aut) : Equiv.Perm V) v.1) :=
      (MoleculeGraph.Aut.adj_iff (m := m) (e := (e⁻¹ : m.Aut)) ((e : Equiv.Perm V) c) v.1).2 v.2
    simpa using this
  · intro v
    apply Subtype.ext
    simp
  · intro v
    apply Subtype.ext
    simp

end MoleculeGraph

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A permutation *preserves the set of distinguished centers* when it maps `m.centers` to itself. -/
def PreservesCenters (m : MultiCenterMolecule V) (e : Equiv.Perm V) : Prop :=
  ∀ c, c ∈ m.centers ↔ e c ∈ m.centers

/-- Automorphisms of a multi-center molecule: graph automorphisms that preserve the distinguished
center set. -/
def Aut (m : MultiCenterMolecule V) : Subgroup (Equiv.Perm V) where
  carrier := { e | e ∈ m.mol.Aut ∧ m.PreservesCenters e }
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro c
    simp
  mul_mem' := by
    intro a b ha hb
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_⟩
    intro c
    -- `c ∈ centers ↔ b c ∈ centers ↔ a (b c) ∈ centers`.
    constructor
    · intro hc
      have : (b : Equiv.Perm V) c ∈ m.centers := (hb.2 c).1 hc
      exact (ha.2 ((b : Equiv.Perm V) c)).1 this
    · intro hc
      have : (b : Equiv.Perm V) c ∈ m.centers := (ha.2 ((b : Equiv.Perm V) c)).2 hc
      exact (hb.2 c).2 this
  inv_mem' := by
    intro a ha
    refine ⟨Subgroup.inv_mem _ ha.1, ?_⟩
    intro c
    -- Use the equivalence for `a` at `a⁻¹ c`.
    have h :=
      ha.2 (((a : Equiv.Perm V)⁻¹) c)
    -- `h` is `(a⁻¹ c) ∈ centers ↔ c ∈ centers`.
    simpa using h.symm

namespace Aut

variable (m : MultiCenterMolecule V)

@[simp] theorem mem_molAut (e : m.Aut) : (e : Equiv.Perm V) ∈ m.mol.Aut :=
  e.property.1

@[simp] theorem preservesCenters (e : m.Aut) : m.PreservesCenters (e : Equiv.Perm V) :=
  e.property.2

@[simp] theorem mem_centers_iff (e : m.Aut) (c : V) :
    c ∈ m.centers ↔ (e : Equiv.Perm V) c ∈ m.centers :=
  (MultiCenterMolecule.Aut.preservesCenters (m := m) e) c

@[simp] theorem apply_mem_centers_iff (e : m.Aut) (c : V) :
    (e : Equiv.Perm V) c ∈ m.centers ↔ c ∈ m.centers := by
  simpa using (MultiCenterMolecule.Aut.mem_centers_iff (m := m) (e := e) c).symm

end Aut

/-- An automorphism of a multi-center molecule permutes the distinguished centers. -/
noncomputable def centerPerm (m : MultiCenterMolecule V) (e : m.Aut) :
    Equiv.Perm m.Center := by
  classical
  refine
    { toFun := fun c =>
        ⟨(e : Equiv.Perm V) c.1,
          (MultiCenterMolecule.Aut.mem_centers_iff (m := m) (e := e) c.1).1 c.2⟩
      invFun := fun c => ⟨((e : Equiv.Perm V)⁻¹) c.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- membership for `invFun`
    have h :
        ((e : Equiv.Perm V)⁻¹) c.1 ∈ m.centers ↔ c.1 ∈ m.centers := by
      -- Apply `PreservesCenters` at `e⁻¹ c`.
      have :=
        (MultiCenterMolecule.Aut.preservesCenters (m := m) e) (((e : Equiv.Perm V)⁻¹) c.1)
      simpa using this
    exact h.2 c.2
  · intro c
    apply Subtype.ext
    simp
  · intro c
    apply Subtype.ext
    simp

/-- `centerPerm` is a group homomorphism from multi-center automorphisms to permutations of the
distinguished center type. -/
noncomputable def centerPermHom (m : MultiCenterMolecule V) :
    m.Aut →* Equiv.Perm m.Center where
  toFun := m.centerPerm
  map_one' := by
    classical
    ext c
    simp [centerPerm]
  map_mul' := by
    classical
    intro e f
    ext c
    simp [centerPerm]

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
