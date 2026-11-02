import TetraStereo.OneCenter.CIP
import TetraStereo.OneCenter.Symmetry

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The CIP key of a ligand is invariant under any center-fixing molecular automorphism. -/
theorem cipKey_eq_cipKey_ligandPermHom (m : OneCenterMolecule V) (e : m.CenterAut) (i : Fin 4) :
    m.cipKey ((m.ligandPermHom e) i) = m.cipKey i := by
  classical
  -- Package `e` as a molecular-graph automorphism.
  let eMol : m.mol.Aut := ⟨(e : Equiv.Perm V), e.property.1⟩
  have hZ : ∀ v, m.mol.atomZ ((e : Equiv.Perm V) v) = m.mol.atomZ v := by
    intro v
    exact MoleculeGraph.Aut.atomZ_eq (m := m.mol) eMol v
  have hMass : ∀ v, m.mol.atomMass ((e : Equiv.Perm V) v) = m.mol.atomMass v := by
    intro v
    exact MoleculeGraph.Aut.atomMass_eq (m := m.mol) eMol v
  have hBond : ∀ u v, m.mol.bond ((e : Equiv.Perm V) u) ((e : Equiv.Perm V) v) = m.mol.bond u v := by
    intro u v
    exact MoleculeGraph.Aut.bond_eq (m := m.mol) eMol u v

  have hlig :
      m.ligandAtom ((m.ligandPermHom e) i) = (e : Equiv.Perm V) (m.ligandAtom i) := by
    -- `ligandPermHom` is defined from `ligandPerm`.
    change m.ligandAtom (m.ligandPerm e i) = (e : Equiv.Perm V) (m.ligandAtom i)
    exact m.ligandAtom_ligandPerm (e := e) i

  -- Apply invariance of `cipKeyFrom` under graph automorphisms.
  have hcenter : (e : Equiv.Perm V) m.center = m.center := e.property.2
  have hkey :
      MoleculeGraph.cipKeyFrom m.mol m.center ((e : Equiv.Perm V) (m.ligandAtom i)) =
        MoleculeGraph.cipKeyFrom m.mol m.center (m.ligandAtom i) := by
    have hpres :
        MoleculeGraph.cipKeyFrom m.mol ((e : Equiv.Perm V) m.center) ((e : Equiv.Perm V) (m.ligandAtom i)) =
          MoleculeGraph.cipKeyFrom m.mol m.center (m.ligandAtom i) :=
      MoleculeGraph.cipKeyFrom_eq_of_preserves (m := m.mol) (e := (e : Equiv.Perm V))
        (hZ := hZ) (hMass := hMass) (hBond := hBond) (center := m.center) (start := m.ligandAtom i)
    simpa [hcenter] using hpres

  -- Unfold `cipKey` and rewrite by `hlig`.
  dsimp [OneCenterMolecule.cipKey]
  simpa [hlig] using hkey

/-- If the CIP keys are all distinct, every center symmetry fixes the ligand indices. -/
theorem ligandPermHom_eq_one_of_stereogenicByCIP (m : OneCenterMolecule V)
    (h : m.StereogenicByCIP) (e : m.CenterAut) :
    m.ligandPermHom e = 1 := by
  classical
  ext i
  have hkey := m.cipKey_eq_cipKey_ligandPermHom (e := e) i
  -- Injectivity forces the induced permutation to fix each index.
  have hi : (m.ligandPermHom e) i = i := h hkey
  simpa using congrArg Fin.val hi

/-- If the CIP keys are all distinct, the molecule is chiral by the symmetry criterion:
every center symmetry induces an even ligand permutation (indeed the identity). -/
theorem chiralBySymmetry_of_stereogenicByCIP (m : OneCenterMolecule V)
    (h : m.StereogenicByCIP) : m.ChiralBySymmetry := by
  intro e
  have hfix : m.ligandPermHom e = 1 := m.ligandPermHom_eq_one_of_stereogenicByCIP h e
  simp [hfix]

/-- A CIP-stereogenic one-center molecule has exactly two symmetry-aware stereochemical classes. -/
theorem stereoQ_exactly_two_classes_of_stereogenicByCIP (m : OneCenterMolecule V)
    (h : m.StereogenicByCIP) :
    ∃ a b : m.StereoQ, a ≠ b ∧ ∀ q : m.StereoQ, q = a ∨ q = b := by
  exact
    m.stereoQ_exactly_two_classes_of_chiralBySymmetry (m.chiralBySymmetry_of_stereogenicByCIP h)

end OneCenterMolecule

end
end OneCenter
end TetraStereo
