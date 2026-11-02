import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.MoleculeGraph
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A permutation of atoms is a molecular-graph automorphism when it preserves every constitutional
atom label (including formal charge) and bond orders. -/
def IsAutomorphism (m : MoleculeGraph V) (e : Equiv.Perm V) : Prop :=
  (∀ v, m.atomZ (e v) = m.atomZ v) ∧
    (∀ v, m.atomMass (e v) = m.atomMass v) ∧
    (∀ v, m.formalCharge (e v) = m.formalCharge v) ∧
    (∀ u v, m.bond (e u) (e v) = m.bond u v)

/-- The automorphism group of a molecular graph, as a subgroup of permutations of the atoms. -/
def Aut (m : MoleculeGraph V) : Subgroup (Equiv.Perm V) where
  carrier := { e | m.IsAutomorphism e }
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro v <;> simp
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨haZ, haMass, haCharge, haBond⟩
    rcases hb with ⟨hbZ, hbMass, hbCharge, hbBond⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      simpa using (haZ (b v)).trans (hbZ v)
    · intro v
      simpa using (haMass (b v)).trans (hbMass v)
    · intro v
      simpa using (haCharge (b v)).trans (hbCharge v)
    · intro u v
      simpa using (haBond (b u) (b v)).trans (hbBond u v)
  inv_mem' := by
    intro a ha
    rcases ha with ⟨haZ, haMass, haCharge, haBond⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      have := haZ (a⁻¹ v)
      -- `simp` turns this into `m.atomZ v = m.atomZ (a⁻¹ v)`.
      simpa using this.symm
    · intro v
      have := haMass (a⁻¹ v)
      simpa using this.symm
    · intro v
      have := haCharge (a⁻¹ v)
      simpa using this.symm
    · intro u v
      have := haBond (a⁻¹ u) (a⁻¹ v)
      simpa using this.symm

namespace Aut

variable (m : MoleculeGraph V)

@[simp] theorem atomZ_eq (e : m.Aut) (v : V) :
    m.atomZ ((e : Equiv.Perm V) v) = m.atomZ v :=
  e.property.1 v

@[simp] theorem atomMass_eq (e : m.Aut) (v : V) :
    m.atomMass ((e : Equiv.Perm V) v) = m.atomMass v :=
  e.property.2.1 v

@[simp] theorem formalCharge_eq (e : m.Aut) (v : V) :
    m.formalCharge ((e : Equiv.Perm V) v) = m.formalCharge v :=
  e.property.2.2.1 v

@[simp] theorem bond_eq (e : m.Aut) (u v : V) :
    m.bond ((e : Equiv.Perm V) u) ((e : Equiv.Perm V) v) = m.bond u v :=
  e.property.2.2.2 u v

@[simp] theorem adj_iff (e : m.Aut) (u v : V) :
    m.Adj ((e : Equiv.Perm V) u) ((e : Equiv.Perm V) v) ↔ m.Adj u v := by
  simp [MoleculeGraph.Adj]

end Aut

end MoleculeGraph

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Automorphisms of a one-center molecule that fix the stereocenter. -/
def CenterAut (m : OneCenterMolecule V) : Subgroup (Equiv.Perm V) where
  carrier := { e | e ∈ m.mol.Aut ∧ e m.center = m.center }
  one_mem' := by
    refine ⟨?_, by simp⟩
    exact Subgroup.one_mem _
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ ha.1 hb.1
    · calc
        (a * b) m.center = a (b m.center) := rfl
        _ = a m.center := by simp [hb.2]
        _ = m.center := ha.2
  inv_mem' := by
    intro a ha
    refine ⟨Subgroup.inv_mem _ ha.1, ?_⟩
    -- Use `a center = center`.
    have h := congrArg (fun x => a⁻¹ x) ha.2
    -- `simp` turns this into `m.center = a⁻¹ m.center`.
    simpa using h.symm

namespace CenterAut

variable (m : OneCenterMolecule V)

@[simp] theorem mem_molAut (e : m.CenterAut) : (e : Equiv.Perm V) ∈ m.mol.Aut :=
  e.property.1

@[simp] theorem apply_center (e : m.CenterAut) : (e : Equiv.Perm V) m.center = m.center :=
  e.property.2

end CenterAut

/-- The (typed) set of atoms adjacent to the stereocenter. -/
abbrev Neighbor (m : OneCenterMolecule V) : Type _ :=
  { v : V // m.mol.Adj m.center v }

/-- The ligand enumeration as an equivalence between the four indices and the neighbors of the
stereocenter. -/
noncomputable def ligandEquiv (m : OneCenterMolecule V) : Fin 4 ≃ m.Neighbor := by
  classical
  refine
    { toFun := fun i => ⟨m.ligandAtom i, m.ligandAtom_adj i⟩
      invFun := fun v => Classical.choose (m.ligandAtom_surjective v.1 v.2)
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    have h :=
      Classical.choose_spec (m.ligandAtom_surjective (m.ligandAtom i) (m.ligandAtom_adj i))
    exact m.ligandAtom_injective h
  · intro v
    apply Subtype.ext
    exact Classical.choose_spec (m.ligandAtom_surjective v.1 v.2)

/-- The induced permutation of the neighbor-subtype from a center-fixing automorphism. -/
noncomputable def neighborPerm (m : OneCenterMolecule V) (e : m.CenterAut) :
    Equiv.Perm m.Neighbor := by
  classical
  let eMol : m.mol.Aut := ⟨(e : Equiv.Perm V), e.property.1⟩
  refine
    { toFun := fun v => ⟨(e : Equiv.Perm V) v.1, ?_⟩
      invFun := fun v => ⟨((e : Equiv.Perm V)⁻¹) v.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hbond' : m.mol.bond ((e : Equiv.Perm V) m.center) ((e : Equiv.Perm V) v.1) =
        m.mol.bond m.center v.1 :=
      MoleculeGraph.Aut.bond_eq (m := m.mol) eMol m.center v.1
    have hbond : m.mol.bond m.center ((e : Equiv.Perm V) v.1) = m.mol.bond m.center v.1 := by
      simpa [e.property.2] using hbond'
    simpa [MoleculeGraph.Adj, hbond] using v.2
  · have heInv : ((e : Equiv.Perm V)⁻¹) ∈ m.mol.Aut :=
      Subgroup.inv_mem _ e.property.1
    let eInvMol : m.mol.Aut := ⟨((e : Equiv.Perm V)⁻¹), heInv⟩
    have hcenter : ((e : Equiv.Perm V)⁻¹) m.center = m.center := by
      have h :
          ((e : Equiv.Perm V)⁻¹) m.center =
            ((e : Equiv.Perm V)⁻¹) ((e : Equiv.Perm V) m.center) :=
        congrArg (fun x => ((e : Equiv.Perm V)⁻¹) x) e.property.2.symm
      calc
        ((e : Equiv.Perm V)⁻¹) m.center
            = ((e : Equiv.Perm V)⁻¹) ((e : Equiv.Perm V) m.center) := h
        _ = m.center := by
              simpa using (show (e : Equiv.Perm V).symm ((e : Equiv.Perm V) m.center) = m.center from
                (e : Equiv.Perm V).symm_apply_apply m.center)
    have hbond' :
        m.mol.bond (((e : Equiv.Perm V)⁻¹) m.center) (((e : Equiv.Perm V)⁻¹) v.1) =
          m.mol.bond m.center v.1 :=
      MoleculeGraph.Aut.bond_eq (m := m.mol) eInvMol m.center v.1
    have hbond :
        m.mol.bond m.center (((e : Equiv.Perm V)⁻¹) v.1) = m.mol.bond m.center v.1 := by
      simpa [hcenter] using hbond'
    have hv : 0 < m.mol.bond m.center v.1 := by
      simpa [MoleculeGraph.Adj] using v.2
    -- Transport the strict inequality across the bond-order equality.
    dsimp [MoleculeGraph.Adj]
    exact lt_of_lt_of_eq hv hbond.symm
  · intro v
    apply Subtype.ext
    simp
  · intro v
    apply Subtype.ext
    simp

/-- The induced permutation on ligand indices coming from a center-fixing automorphism. -/
noncomputable def ligandPerm (m : OneCenterMolecule V) (e : m.CenterAut) :
    Equiv.Perm (Fin 4) :=
  (m.ligandEquiv.trans (m.neighborPerm e)).trans (m.ligandEquiv.symm)

@[simp] theorem ligandAtom_ligandPerm (m : OneCenterMolecule V) (e : m.CenterAut) (i : Fin 4) :
    m.ligandAtom (m.ligandPerm e i) = (e : Equiv.Perm V) (m.ligandAtom i) := by
  classical
  have h :
      m.ligandEquiv (m.ligandPerm e i) =
        m.neighborPerm e (m.ligandEquiv i) := by
    simp [ligandPerm]
  simpa [ligandEquiv, neighborPerm] using congrArg Subtype.val h

/-- `ligandPerm` is a group homomorphism from center automorphisms to ligand-index permutations. -/
noncomputable def ligandPermHom (m : OneCenterMolecule V) :
    m.CenterAut →* Equiv.Perm (Fin 4) where
  toFun := m.ligandPerm
  map_one' := by
    classical
    ext i
    -- `ext` produces a goal in `Fin` coerces, so compare via `ligandAtom` and use injectivity.
    have hi : (m.ligandPerm (1 : m.CenterAut) i) = i := by
      apply m.ligandAtom_injective
      simp [ligandAtom_ligandPerm]
    simpa using congrArg Fin.val hi
  map_mul' := by
    classical
    intro e f
    ext i
    have hi : m.ligandPerm (e * f) i = (m.ligandPerm e * m.ligandPerm f) i := by
      apply m.ligandAtom_injective
      simp [ligandAtom_ligandPerm]
    simpa using congrArg Fin.val hi

/-- A one-center molecule is *achiral by symmetry* when some center-fixing automorphism induces an
odd permutation of the four ligands. -/
def AchiralBySymmetry (m : OneCenterMolecule V) : Prop :=
  ∃ e : m.CenterAut, permHandedness (m.ligandPermHom e) = -1

/-- A one-center molecule is *chiral by symmetry* when every center-fixing automorphism induces an
even permutation of the four ligands. -/
def ChiralBySymmetry (m : OneCenterMolecule V) : Prop :=
  ∀ e : m.CenterAut, permHandedness (m.ligandPermHom e) = 1

/-- The stereochemical parity relation after allowing symmetry-induced ligand relabelings.

When the symmetry group contains an odd ligand permutation, this relation becomes universal
(every frame is equivalent). When the symmetry group is purely even, it reduces to the usual
two-class parity relation. -/
def SameStereo (m : OneCenterMolecule V) (σ τ : Equiv.Perm (Fin 4)) : Prop :=
  ∃ e : m.CenterAut, permHandedness σ = permHandedness (τ * m.ligandPermHom e)

theorem sameStereo_refl (m : OneCenterMolecule V) (σ : Equiv.Perm (Fin 4)) :
    m.SameStereo σ σ := by
  refine ⟨1, by simp⟩

theorem sameStereo_symm (m : OneCenterMolecule V) {σ τ : Equiv.Perm (Fin 4)} :
    m.SameStereo σ τ → m.SameStereo τ σ := by
  intro h
  rcases h with ⟨e, h⟩
  refine ⟨e, ?_⟩
  rcases permHandedness_eq_one_or_eq_neg_one (m.ligandPermHom e) with he | he
  · -- even symmetry
    have hστ : permHandedness σ = permHandedness τ := by
      simpa [permHandedness_mul, he] using h
    -- now `σ * e` has the same sign as `σ`.
    simpa [permHandedness_mul, he] using hστ.symm
  · -- odd symmetry
    have hσ : permHandedness σ = -permHandedness τ := by
      simpa [permHandedness_mul, he] using h
    have ht : permHandedness τ = -permHandedness σ := by
      have := congrArg Neg.neg hσ
      simpa using this.symm
    simpa [permHandedness_mul, he] using ht

theorem sameStereo_trans (m : OneCenterMolecule V) {σ τ υ : Equiv.Perm (Fin 4)} :
    m.SameStereo σ τ → m.SameStereo τ υ → m.SameStereo σ υ := by
  intro hστ hτυ
  rcases hστ with ⟨e, hσ⟩
  rcases hτυ with ⟨f, hτ⟩
  refine ⟨f * e, ?_⟩
  -- Use multiplicativity of `permHandedness` and the fact `ligandPermHom` is a hom.
  -- `τ * ligandPerm e` has the same sign as `υ * ligandPerm f * ligandPerm e`.
  -- Reassociate products to match.
  calc
    permHandedness σ
        = permHandedness (τ * m.ligandPermHom e) := hσ
    _ = permHandedness τ * permHandedness (m.ligandPermHom e) := by
          simp [permHandedness_mul]
    _ = permHandedness (υ * m.ligandPermHom f) * permHandedness (m.ligandPermHom e) := by
          simpa [permHandedness_mul] using congrArg (fun x => x * permHandedness (m.ligandPermHom e)) hτ
    _ = permHandedness (υ * (m.ligandPermHom f * m.ligandPermHom e)) := by
          simp [permHandedness_mul, mul_assoc]
    _ = permHandedness (υ * m.ligandPermHom (f * e)) := by
          simp [OneCenterMolecule.ligandPermHom, map_mul]

/-- The setoid on frames induced by `SameStereo`. -/
def stereoSetoid (m : OneCenterMolecule V) : Setoid (Equiv.Perm (Fin 4)) where
  r := m.SameStereo
  iseqv := ⟨m.sameStereo_refl, m.sameStereo_symm, m.sameStereo_trans⟩

/-- The (toy) stereochemical quotient after accounting for center symmetries. -/
abbrev StereoQ (m : OneCenterMolecule V) := Quotient (m.stereoSetoid)

theorem sameStereo_universal_of_achiralBySymmetry (m : OneCenterMolecule V)
    (hodd : m.AchiralBySymmetry) (σ τ : Equiv.Perm (Fin 4)) : m.SameStereo σ τ := by
  classical
  rcases hodd with ⟨eOdd, heOdd⟩
  -- Either `σ` has the same parity as `τ`, or the opposite; in the opposite case, use `eOdd`.
  rcases permHandedness_eq_one_or_eq_neg_one σ with hs | hs
  · rcases permHandedness_eq_one_or_eq_neg_one τ with ht | ht
    · refine ⟨1, ?_⟩
      simp [hs, ht]
    · refine ⟨eOdd, ?_⟩
      -- `τ * odd` has sign `(-1) * (-1) = 1`.
      simp [hs, ht, permHandedness_mul, heOdd]
  · rcases permHandedness_eq_one_or_eq_neg_one τ with ht | ht
    · refine ⟨eOdd, ?_⟩
      -- `τ * odd` has sign `1 * (-1) = -1`.
      simp [hs, ht, permHandedness_mul, heOdd]
    · refine ⟨1, ?_⟩
      simp [hs, ht]

theorem subsingleton_stereoQ_of_achiralBySymmetry (m : OneCenterMolecule V)
    (hodd : m.AchiralBySymmetry) : Subsingleton (m.StereoQ) := by
  classical
  refine ⟨?_⟩
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro σ τ
  apply Quotient.sound
  exact m.sameStereo_universal_of_achiralBySymmetry hodd σ τ

theorem sameStereo_iff_sameClass_of_chiralBySymmetry (m : OneCenterMolecule V)
    (heven : m.ChiralBySymmetry) (σ τ : Equiv.Perm (Fin 4)) :
    m.SameStereo σ τ ↔ permHandedness σ = permHandedness τ := by
  constructor
  · intro h
    rcases h with ⟨e, h⟩
    have : permHandedness (m.ligandPermHom e) = 1 := heven e
    simpa [SameStereo, permHandedness_mul, this] using h
  · intro h
    refine ⟨1, ?_⟩
    simp [h]

/-- The “positive” symmetry-aware stereochemical class: the class of the identity frame. -/
def qPlus (m : OneCenterMolecule V) : m.StereoQ :=
  Quotient.mk (m.stereoSetoid) (1 : Equiv.Perm (Fin 4))

/-- The “negative” symmetry-aware stereochemical class: the class of a transposition. -/
def qMinus (m : OneCenterMolecule V) : m.StereoQ :=
  Quotient.mk (m.stereoSetoid) (Equiv.swap (0 : Fin 4) 1)

theorem qPlus_ne_qMinus_of_chiralBySymmetry (m : OneCenterMolecule V)
    (heven : m.ChiralBySymmetry) : m.qPlus ≠ m.qMinus := by
  intro h
  have hrel :
      m.SameStereo (1 : Equiv.Perm (Fin 4)) (Equiv.swap (0 : Fin 4) 1) :=
    Quotient.exact h
  have hpar : permHandedness (1 : Equiv.Perm (Fin 4)) =
      permHandedness (Equiv.swap (0 : Fin 4) 1) :=
    (m.sameStereo_iff_sameClass_of_chiralBySymmetry heven _ _).1 hrel
  -- But `1` is even and a transposition is odd.
  simp at hpar
  have : (1 : ℝ) ≠ (-1 : ℝ) := by norm_num
  exact this hpar

theorem stereoQ_two_point_of_chiralBySymmetry (m : OneCenterMolecule V)
    (heven : m.ChiralBySymmetry) (q : m.StereoQ) :
    q = m.qPlus ∨ q = m.qMinus := by
  refine Quotient.inductionOn q ?_
  intro σ
  rcases permHandedness_eq_one_or_eq_neg_one σ with hσ | hσ
  · left
    apply Quotient.sound
    refine (m.sameStereo_iff_sameClass_of_chiralBySymmetry heven _ _).2 ?_
    simp [hσ]
  · right
    apply Quotient.sound
    refine (m.sameStereo_iff_sameClass_of_chiralBySymmetry heven _ _).2 ?_
    simp [hσ]

theorem stereoQ_exactly_two_classes_of_chiralBySymmetry (m : OneCenterMolecule V)
    (heven : m.ChiralBySymmetry) :
    ∃ a b : m.StereoQ, a ≠ b ∧ ∀ q : m.StereoQ, q = a ∨ q = b := by
  refine ⟨m.qPlus, m.qMinus, m.qPlus_ne_qMinus_of_chiralBySymmetry heven, ?_⟩
  intro q
  simpa using m.stereoQ_two_point_of_chiralBySymmetry heven q

end OneCenterMolecule

end
end OneCenter
end TetraStereo
