import TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

noncomputable section

namespace TetraStereo
namespace OneCenter
namespace RootedTetrahedralBranchSymmetry

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Module-local root-avoiding walk helper

The shared module `TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry` owns the public
relations `LigandBranchReaches`, `BranchTransport`, `ProperTransport`, `MirrorTransport` and
`Enantiomorphic`.  This module does not redeclare them.  The inductive below is a local
constructive helper for enumerating the small fixture branches exactly; it lives in its own
namespace and is proved equivalent to the shared simple-graph walk relation.
-/

namespace WitnessBranchWalk

/-- A walk in a molecular graph that avoids a fixed root atom at every vertex. -/
inductive BranchWalk (m : MoleculeGraph V) (root : V) : V → V → Prop where
  | refl {v : V} (hv : v ≠ root) : BranchWalk m root v v
  | step {u v w : V} (hu : u ≠ root) (huv : m.Adj u v)
      (tail : BranchWalk m root v w) : BranchWalk m root u w

namespace BranchWalk

theorem start_ne_root {m : MoleculeGraph V} {root v w : V}
    (hw : BranchWalk m root v w) : v ≠ root := by
  cases hw with
  | refl hv => exact hv
  | step hu _ _ => exact hu

theorem endpoint_ne_root {m : MoleculeGraph V} {root v w : V}
    (hw : BranchWalk m root v w) : w ≠ root := by
  induction hw with
  | refl hv => exact hv
  | step _ _ _ ih => exact ih

/-- If a finite vertex set contains the start of a branch walk, excludes the root, and is closed
under non-root edges, then it contains the endpoint.  This is the exact reachability principle used
below: it proves that no vertex outside the stated branch can be reached. -/
theorem endpoint_mem_of_closed {m : MoleculeGraph V} {root v w : V}
    (hw : BranchWalk m root v w) {S : Finset V}
    (hclosed : ∀ u ∈ S, ∀ x : V, m.Adj u x → x ≠ root → x ∈ S) :
    v ∈ S → w ∈ S := by
  induction hw with
  | refl _ => exact id
  | step hu huv htail ih =>
      intro hvS
      exact ih (hclosed _ hvS _ huv (start_ne_root htail))

end BranchWalk

/-- Convert the local root-avoiding walk helper to a simple-graph walk whose support avoids the
root. -/
theorem branchWalk_to_walk {m : MoleculeGraph V} {root u v : V}
    (hw : BranchWalk m root u v) :
    ∃ p : m.underlyingSimpleGraph.Walk u v, root ∉ p.support := by
  induction hw with
  | refl hv =>
      exact ⟨SimpleGraph.Walk.nil, by simpa using hv.symm⟩
  | step hu hadj _ ih =>
      rcases ih with ⟨p, hp⟩
      refine ⟨SimpleGraph.Walk.cons (by simpa using hadj) p, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
      exact ⟨fun h => hu h.symm, hp⟩

/-- Convert a simple-graph walk avoiding the root into the local root-avoiding walk helper. -/
theorem walk_to_branchWalk {m : MoleculeGraph V} {root u v : V}
    (p : m.underlyingSimpleGraph.Walk u v) :
    root ∉ p.support → BranchWalk m root u v := by
  induction p with
  | nil =>
      intro hp
      exact BranchWalk.refl (by
        intro h
        exact hp (by simp [h]))
  | cons hadj tail ih =>
      intro hp
      rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hp
      exact BranchWalk.step (fun h => hp.1 h.symm) (by simpa using hadj) (ih hp.2)

/-- The local helper proves exactly the shared branch-reachability relation. -/
theorem branchWalk_to_ligandBranchReaches {m : MultiCenterMolecule V} {c : m.Center}
    {i : Fin 4} {v : V}
    (hw : BranchWalk m.mol c.1 (m.ligandAtomAt c i) v) :
    LigandBranchReaches m c i v :=
  branchWalk_to_walk hw

/-- The local helper is equivalent to the shared simple-graph branch-reachability relation. -/
theorem ligandBranchReaches_iff_branchWalk {m : MultiCenterMolecule V} {c : m.Center}
    {i : Fin 4} {v : V} :
    LigandBranchReaches m c i v ↔ BranchWalk m.mol c.1 (m.ligandAtomAt c i) v := by
  constructor
  · rintro ⟨p, hp⟩
    exact walk_to_branchWalk p hp
  · exact branchWalk_to_ligandBranchReaches

/-- The attachment root is never reached inside its own ligand branch. -/
theorem ligandBranchReaches_not_root (m : MultiCenterMolecule V) (c : m.Center)
    (i : Fin 4) : ¬ LigandBranchReaches m c i c.1 := by
  rintro ⟨p, hp⟩
  exact hp p.end_mem_support

end WitnessBranchWalk

/-! ## The trihydroxyglutaric acid fixture -/

namespace TrihydroxyglutaricWitness

open TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid
open TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.Atom
open WitnessBranchWalk

/-! ### Ligand atom values -/

@[simp] theorem ligandAtomAt_left_zero : multi.ligandAtomAt leftCenter 0 = o2 := by
  simp [MultiCenterMolecule.ligandAtomAt, leftCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_left_one : multi.ligandAtomAt leftCenter 1 = carboxylL := by
  simp [MultiCenterMolecule.ligandAtomAt, leftCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_left_two : multi.ligandAtomAt leftCenter 2 = c3 := by
  simp [MultiCenterMolecule.ligandAtomAt, leftCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_left_three : multi.ligandAtomAt leftCenter 3 = h2 := by
  simp [MultiCenterMolecule.ligandAtomAt, leftCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_middle_zero : multi.ligandAtomAt middleCenter 0 = o3 := by
  simp [MultiCenterMolecule.ligandAtomAt, middleCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_middle_one : multi.ligandAtomAt middleCenter 1 = c2 := by
  simp [MultiCenterMolecule.ligandAtomAt, middleCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_middle_two : multi.ligandAtomAt middleCenter 2 = c4 := by
  simp [MultiCenterMolecule.ligandAtomAt, middleCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_middle_three : multi.ligandAtomAt middleCenter 3 = h3 := by
  simp [MultiCenterMolecule.ligandAtomAt, middleCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_right_zero : multi.ligandAtomAt rightCenter 0 = o4 := by
  simp [MultiCenterMolecule.ligandAtomAt, rightCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_right_one : multi.ligandAtomAt rightCenter 1 = carboxylR := by
  simp [MultiCenterMolecule.ligandAtomAt, rightCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_right_two : multi.ligandAtomAt rightCenter 2 = c3 := by
  simp [MultiCenterMolecule.ligandAtomAt, rightCenter, multi, ligandAt]

@[simp] theorem ligandAtomAt_right_three : multi.ligandAtomAt rightCenter 3 = h4 := by
  simp [MultiCenterMolecule.ligandAtomAt, rightCenter, multi, ligandAt]

/-- The atomic-number signature of the four ligand slots of any of the three fixture centers:
a carboxyl/oxygen carbon, the other two carbons, and hydrogen. -/
def terminalZ : Fin 4 → ℕ
  | 0 => 8
  | 1 => 6
  | 2 => 6
  | 3 => 1

@[simp] theorem terminalZ_zero : terminalZ 0 = 8 := rfl
@[simp] theorem terminalZ_one : terminalZ 1 = 6 := rfl
@[simp] theorem terminalZ_two : terminalZ 2 = 6 := rfl
@[simp] theorem terminalZ_three : terminalZ 3 = 1 := rfl

theorem atomZ_ligandAtomAt_left (k : Fin 4) :
    multi.mol.atomZ (multi.ligandAtomAt leftCenter k) = terminalZ k := by
  fin_cases k <;>
    simp [MultiCenterMolecule.ligandAtomAt, leftCenter, multi, mol, atomZ, ligandAt, terminalZ]

theorem atomZ_ligandAtomAt_middle (k : Fin 4) :
    multi.mol.atomZ (multi.ligandAtomAt middleCenter k) = terminalZ k := by
  fin_cases k <;>
    simp [MultiCenterMolecule.ligandAtomAt, middleCenter, multi, mol, atomZ, ligandAt, terminalZ]

theorem atomZ_ligandAtomAt_right (k : Fin 4) :
    multi.mol.atomZ (multi.ligandAtomAt rightCenter k) = terminalZ k := by
  fin_cases k <;>
    simp [MultiCenterMolecule.ligandAtomAt, rightCenter, multi, mol, atomZ, ligandAt, terminalZ]

theorem eq_zero_of_terminalZ {k : Fin 4} (h : terminalZ k = 8) : k = 0 := by
  fin_cases k <;> simp [terminalZ] at h ⊢

theorem eq_three_of_terminalZ {k : Fin 4} (h : terminalZ k = 1) : k = 3 := by
  fin_cases k <;> simp [terminalZ] at h ⊢

theorem eq_one_or_two_of_terminalZ {k : Fin 4} (h : terminalZ k = 6) : k = 1 ∨ k = 2 := by
  fin_cases k <;> simp [terminalZ] at h ⊢

theorem eq_two_of_right_ligand_eq_c3 {k : Fin 4}
    (h : multi.ligandAtomAt rightCenter k = c3) : k = 2 := by
  fin_cases k <;> simp at h ⊢

theorem eq_two_of_left_ligand_eq_c3 {k : Fin 4}
    (h : multi.ligandAtomAt leftCenter k = c3) : k = 2 := by
  fin_cases k <;> simp at h ⊢

/-! ### Exact side-branch reachability -/

/-- The atoms of the left side branch of the middle center. -/
def leftBranchAtoms : Finset Atom := {c2, carboxylL, carboxylLO1, carboxylLO2, o2, h2}

/-- The atoms of the right side branch of the middle center. -/
def rightBranchAtoms : Finset Atom := {c4, carboxylR, carboxylRO1, carboxylRO2, o4, h4}

/-- The left branch is closed under edges that do not return to the root. -/
theorem leftBranchAtoms_closed :
    ∀ u ∈ leftBranchAtoms, ∀ w : Atom, multi.mol.Adj u w → w ≠ middleCenter.1 →
      w ∈ leftBranchAtoms := by
  decide

/-- The right branch is closed under edges that do not return to the root. -/
theorem rightBranchAtoms_closed :
    ∀ u ∈ rightBranchAtoms, ∀ w : Atom, multi.mol.Adj u w → w ≠ middleCenter.1 →
      w ∈ rightBranchAtoms := by
  decide

/-- Exactly one distinguished center lies in the left branch: the left terminal center. -/
theorem leftBranchAtoms_center_eq :
    ∀ a : Atom, a ∈ leftBranchAtoms → a ∈ multi.centers → a = c2 := by
  decide

/-- Exactly one distinguished center lies in the right branch: the right terminal center. -/
theorem rightBranchAtoms_center_eq :
    ∀ a : Atom, a ∈ rightBranchAtoms → a ∈ multi.centers → a = c4 := by
  decide

/-- A one-edge branch walk with all intermediate vertices named explicitly. -/
theorem branchWalk_one {root a b : Atom} (ha : a ≠ root) (hb : b ≠ root)
    (hab : multi.mol.Adj a b) : BranchWalk multi.mol root a b :=
  BranchWalk.step (u := a) (v := b) (w := b) ha hab (BranchWalk.refl hb)

/-- A two-edge branch walk with all intermediate vertices named explicitly. -/
theorem branchWalk_two {root a b c : Atom} (ha : a ≠ root) (hb : b ≠ root) (hc : c ≠ root)
    (hab : multi.mol.Adj a b) (hbc : multi.mol.Adj b c) :
    BranchWalk multi.mol root a c :=
  BranchWalk.step (u := a) (v := b) (w := c) ha hab
    (BranchWalk.step (u := b) (v := c) (w := c) hb hbc (BranchWalk.refl hc))

/-- Exact reachability of the left side branch at the middle center. -/
theorem ligandBranchReaches_middle_one_iff (v : Atom) :
    LigandBranchReaches multi middleCenter 1 v ↔ v ∈ leftBranchAtoms := by
  constructor
  · rintro ⟨p, hp⟩
    exact (BranchWalk.endpoint_mem_of_closed (walk_to_branchWalk p hp) leftBranchAtoms_closed)
      (by simp [leftBranchAtoms])
  · intro hv
    have hcustom : BranchWalk multi.mol middleCenter.1 (multi.ligandAtomAt middleCenter 1) v := by
      have hstart : multi.ligandAtomAt middleCenter 1 = c2 := by simp
      rw [hstart]
      simp only [leftBranchAtoms, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact BranchWalk.refl (by decide)
      · exact branchWalk_one (root := middleCenter.1) (a := c2) (b := carboxylL)
          (by decide) (by decide) (by decide)
      · exact branchWalk_two (root := middleCenter.1) (a := c2) (b := carboxylL) (c := carboxylLO1)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact branchWalk_two (root := middleCenter.1) (a := c2) (b := carboxylL) (c := carboxylLO2)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact branchWalk_one (root := middleCenter.1) (a := c2) (b := o2)
          (by decide) (by decide) (by decide)
      · exact branchWalk_one (root := middleCenter.1) (a := c2) (b := h2)
          (by decide) (by decide) (by decide)
    exact branchWalk_to_ligandBranchReaches hcustom

/-- Exact reachability of the right side branch at the middle center. -/
theorem ligandBranchReaches_middle_two_iff (v : Atom) :
    LigandBranchReaches multi middleCenter 2 v ↔ v ∈ rightBranchAtoms := by
  constructor
  · rintro ⟨p, hp⟩
    exact (BranchWalk.endpoint_mem_of_closed (walk_to_branchWalk p hp) rightBranchAtoms_closed)
      (by simp [rightBranchAtoms])
  · intro hv
    have hcustom : BranchWalk multi.mol middleCenter.1 (multi.ligandAtomAt middleCenter 2) v := by
      have hstart : multi.ligandAtomAt middleCenter 2 = c4 := by simp
      rw [hstart]
      simp only [rightBranchAtoms, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact BranchWalk.refl (by decide)
      · exact branchWalk_one (root := middleCenter.1) (a := c4) (b := carboxylR)
          (by decide) (by decide) (by decide)
      · exact branchWalk_two (root := middleCenter.1) (a := c4) (b := carboxylR) (c := carboxylRO1)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact branchWalk_two (root := middleCenter.1) (a := c4) (b := carboxylR) (c := carboxylRO2)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact branchWalk_one (root := middleCenter.1) (a := c4) (b := o4)
          (by decide) (by decide) (by decide)
      · exact branchWalk_one (root := middleCenter.1) (a := c4) (b := h4)
          (by decide) (by decide) (by decide)
    exact branchWalk_to_ligandBranchReaches hcustom

/-- Every center reached from middle slot `1` is the left terminal center. -/
theorem branchReaches_middle_one_center {d : multi.Center}
    (hd : LigandBranchReaches multi middleCenter 1 d.1) : d = leftCenter := by
  have h : d.1 = c2 :=
    leftBranchAtoms_center_eq d.1 ((ligandBranchReaches_middle_one_iff d.1).1 hd) d.2
  rcases d with ⟨a, ha⟩
  simp only at h
  subst h
  exact Subtype.ext rfl

/-- Every center reached from middle slot `2` is the right terminal center. -/
theorem branchReaches_middle_two_center {d : multi.Center}
    (hd : LigandBranchReaches multi middleCenter 2 d.1) : d = rightCenter := by
  have h : d.1 = c4 :=
    rightBranchAtoms_center_eq d.1 ((ligandBranchReaches_middle_two_iff d.1).1 hd) d.2
  rcases d with ⟨a, ha⟩
  simp only at h
  subst h
  exact Subtype.ext rfl

/-- The left terminal center lies in the left branch of the middle center. -/
theorem ligandBranchReaches_middle_one_leftCenter :
    LigandBranchReaches multi middleCenter 1 leftCenter.1 := by
  rw [ligandBranchReaches_middle_one_iff]
  simp [leftBranchAtoms, leftCenter]

/-- The right terminal center lies in the right branch of the middle center. -/
theorem ligandBranchReaches_middle_two_rightCenter :
    LigandBranchReaches multi middleCenter 2 rightCenter.1 := by
  rw [ligandBranchReaches_middle_two_iff]
  simp [rightBranchAtoms, rightCenter]

/-! ### The same-terminal-sign configuration variant -/

/-- The same-terminal-sign variant: every local frame is the identity, so both terminal centers
carry local sign `+1` rather than opposite signs. -/
def cfgSame : multi.Configuration := fun _ => 1

@[simp] theorem cfgSame_sign_left : multi.configurationSign cfgSame leftCenter = 1 := by
  simp [MultiCenterMolecule.configurationSign, cfgSame]

@[simp] theorem cfgSame_sign_middle : multi.configurationSign cfgSame middleCenter = 1 := by
  simp [MultiCenterMolecule.configurationSign, cfgSame]

@[simp] theorem cfgSame_sign_right : multi.configurationSign cfgSame rightCenter = 1 := by
  simp [MultiCenterMolecule.configurationSign, cfgSame]

/-- Proper transport rules out enantiomorphism at the fixture root. -/
theorem witness_not_enantiomorphic_of_properTransport (cfg' : multi.Configuration) {i j : Fin 4}
    (h : ProperTransport multi cfg' middleCenter i j) :
    ¬ Enantiomorphic multi cfg' middleCenter i j := by
  intro hen
  rcases hen with ⟨_, _, hp⟩
  exact hp h

/-! ### The fixture half-turn symmetry -/

theorem centerPerm_flipAut_middle :
    multi.centerPerm flipAut middleCenter = middleCenter := by
  apply Subtype.ext
  simp [middleCenter, multi, flipAut, flipPerm,
    TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.flip,
    MultiCenterMolecule.centerPerm]

theorem centerPerm_flipAut_left :
    multi.centerPerm flipAut leftCenter = rightCenter := by
  apply Subtype.ext
  simp [leftCenter, rightCenter, multi, flipAut, flipPerm,
    TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.flip,
    MultiCenterMolecule.centerPerm]

theorem centerPerm_flipAut_right :
    multi.centerPerm flipAut rightCenter = leftCenter := by
  apply Subtype.ext
  simp [leftCenter, rightCenter, multi, flipAut, flipPerm,
    TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid.flip,
    MultiCenterMolecule.centerPerm]

theorem ligandPermAt_flipAut_middle_one :
    multi.ligandPermAt flipAut middleCenter 1 = 2 := by
  rw [ligandPermAt_flipAut_middle]
  decide

theorem ligandPermAt_flipAut_middle_two :
    multi.ligandPermAt flipAut middleCenter 2 = 1 := by
  rw [ligandPermAt_flipAut_middle]
  decide

/-! ### Root-fixing automorphisms fix the oxygen and hydrogen slots of the middle center

Atomic numbers are preserved by graph automorphisms.  The middle center has exactly one
oxygen-numbered neighbour (`o3`) and exactly one hydrogen-numbered neighbour (`h3`), so every
root-fixing automorphism fixes slots `0` and `3` of the middle center.  Consequently the only
possible non-identity side exchange at the middle center is `1 ↔ 2`. -/

theorem ligandPermAt_middle_fixes_zero_three (e : multi.Aut)
    (hefix : multi.centerPerm e middleCenter = middleCenter) :
    multi.ligandPermAt e middleCenter 0 = 0 ∧
      multi.ligandPermAt e middleCenter 3 = 3 := by
  let eMol : multi.mol.Aut :=
    ⟨(e : Equiv.Perm Atom), MultiCenterMolecule.Aut.mem_molAut (m := multi) e⟩
  have hZaut : ∀ a : Atom, multi.mol.atomZ ((e : Equiv.Perm Atom) a) = multi.mol.atomZ a := by
    intro a
    simpa [eMol] using MoleculeGraph.Aut.atomZ_eq (m := multi.mol) eMol a
  have h0 : multi.ligandPermAt e middleCenter 0 = 0 := by
    have h := multi.ligandAtomAt_ligandPermAt (e := e) (c := middleCenter) (i := 0)
    rw [hefix] at h
    have hz :
        multi.mol.atomZ
            (multi.ligandAtomAt middleCenter (multi.ligandPermAt e middleCenter 0)) = 8 := by
      rw [h, hZaut]
      simp [MultiCenterMolecule.ligandAtomAt, middleCenter, multi, mol, atomZ, ligandAt]
    refine eq_zero_of_terminalZ ?_
    simpa [atomZ_ligandAtomAt_middle] using hz
  have h3 : multi.ligandPermAt e middleCenter 3 = 3 := by
    have h := multi.ligandAtomAt_ligandPermAt (e := e) (c := middleCenter) (i := 3)
    rw [hefix] at h
    have hz :
        multi.mol.atomZ
            (multi.ligandAtomAt middleCenter (multi.ligandPermAt e middleCenter 3)) = 1 := by
      rw [h, hZaut]
      simp [MultiCenterMolecule.ligandAtomAt, middleCenter, multi, mol, atomZ, ligandAt]
    refine eq_three_of_terminalZ ?_
    simpa [atomZ_ligandAtomAt_middle] using hz
  exact ⟨h0, h3⟩

/-- A permutation of `Fin 4` that fixes `0` and `3` can only exchange `1` and `2`. -/
theorem perm_side_pair_of_fixes_zero_three (σ : Equiv.Perm (Fin 4))
    (h0 : σ 0 = 0) (h3 : σ 3 = 3) {i j : Fin 4} (hij : σ i = j) (hne : i ≠ j) :
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  fin_cases i
  · exact absurd (h0.symm.trans hij) hne
  · have hj0 : j ≠ 0 := by
      intro hj
      exact absurd (σ.injective (hij.trans (hj.trans h0.symm))) (by decide)
    have hj3 : j ≠ 3 := by
      intro hj
      exact absurd (σ.injective (hij.trans (hj.trans h3.symm))) (by decide)
    have hj1 : j ≠ 1 := by
      intro hj
      exact hne hj.symm
    fin_cases j <;> simp_all
  · have hj0 : j ≠ 0 := by
      intro hj
      exact absurd (σ.injective (hij.trans (hj.trans h0.symm))) (by decide)
    have hj3 : j ≠ 3 := by
      intro hj
      exact absurd (σ.injective (hij.trans (hj.trans h3.symm))) (by decide)
    have hj2 : j ≠ 2 := by
      intro hj
      exact hne hj.symm
    fin_cases j <;> simp_all
  · exact absurd (h3.symm.trans hij) hne

/-! ### Forcing the terminal ligand permutation

Any root-fixing automorphism exchanging the middle side slots `1` and `2` maps the left terminal
center to the right terminal center.  On the left terminal center its induced ligand permutation is
the identity: slot `0` is the unique oxygen neighbour, slot `3` the unique hydrogen neighbour,
slot `2` the (fixed) middle center, and the remaining slot `1` is the only carboxyl carbon. -/

theorem apply_leftCenter_eq_rightCenter_of_maps_middle_one_two (e : multi.Aut)
    (hefix : multi.centerPerm e middleCenter = middleCenter)
    (hmap : multi.ligandPermAt e middleCenter 1 = 2) :
    (e : Equiv.Perm Atom) c2 = c4 := by
  have h := multi.ligandAtomAt_ligandPermAt (e := e) (c := middleCenter) (i := 1)
  rw [hefix, hmap] at h
  simpa using h.symm

theorem centerPerm_left_eq_right_of_maps_middle_one_two (e : multi.Aut)
    (hefix : multi.centerPerm e middleCenter = middleCenter)
    (hmap : multi.ligandPermAt e middleCenter 1 = 2) :
    multi.centerPerm e leftCenter = rightCenter := by
  apply Subtype.ext
  simpa [MultiCenterMolecule.centerPerm, leftCenter, rightCenter] using
    apply_leftCenter_eq_rightCenter_of_maps_middle_one_two e hefix hmap

theorem ligandPermAt_leftCenter_eq_one_of_maps_middle_one_two (e : multi.Aut)
    (hefix : multi.centerPerm e middleCenter = middleCenter)
    (hmap : multi.ligandPermAt e middleCenter 1 = 2) :
    multi.ligandPermAt e leftCenter = 1 := by
  have he_c2 : (e : Equiv.Perm Atom) c2 = c4 :=
    apply_leftCenter_eq_rightCenter_of_maps_middle_one_two e hefix hmap
  have he_c3 : (e : Equiv.Perm Atom) c3 = c3 := by
    have h := congrArg Subtype.val hefix
    simpa [MultiCenterMolecule.centerPerm, middleCenter] using h
  have hcenter : multi.centerPerm e leftCenter = rightCenter :=
    centerPerm_left_eq_right_of_maps_middle_one_two e hefix hmap
  let eMol : multi.mol.Aut :=
    ⟨(e : Equiv.Perm Atom), MultiCenterMolecule.Aut.mem_molAut (m := multi) e⟩
  have hZaut : ∀ a : Atom, multi.mol.atomZ ((e : Equiv.Perm Atom) a) = multi.mol.atomZ a := by
    intro a
    simpa [eMol] using MoleculeGraph.Aut.atomZ_eq (m := multi.mol) eMol a
  have hσ : ∀ k : Fin 4,
      multi.ligandAtomAt rightCenter (multi.ligandPermAt e leftCenter k) =
        (e : Equiv.Perm Atom) (multi.ligandAtomAt leftCenter k) := by
    intro k
    have h := multi.ligandAtomAt_ligandPermAt (e := e) (c := leftCenter) (i := k)
    rwa [hcenter] at h
  have hZk : ∀ k : Fin 4,
      terminalZ (multi.ligandPermAt e leftCenter k) = terminalZ k := by
    intro k
    calc
      terminalZ (multi.ligandPermAt e leftCenter k)
          = multi.mol.atomZ
              (multi.ligandAtomAt rightCenter (multi.ligandPermAt e leftCenter k)) :=
            (atomZ_ligandAtomAt_right _).symm
      _ = multi.mol.atomZ
            ((e : Equiv.Perm Atom) (multi.ligandAtomAt leftCenter k)) := by rw [hσ k]
      _ = multi.mol.atomZ (multi.ligandAtomAt leftCenter k) := hZaut _
      _ = terminalZ k := atomZ_ligandAtomAt_left k
  have h0 : multi.ligandPermAt e leftCenter 0 = 0 := by
    refine eq_zero_of_terminalZ ?_
    simpa using hZk 0
  have h3 : multi.ligandPermAt e leftCenter 3 = 3 := by
    refine eq_three_of_terminalZ ?_
    simpa using hZk 3
  have h1 : multi.ligandPermAt e leftCenter 1 = 1 := by
    rcases eq_one_or_two_of_terminalZ (by simpa using hZk 1) with h1 | h1
    · exact h1
    · exfalso
      have heq : (e : Equiv.Perm Atom) carboxylL = (e : Equiv.Perm Atom) c3 := by
        have h := hσ 1
        rw [h1] at h
        rw [show multi.ligandAtomAt rightCenter 2 = c3 from by simp] at h
        rw [show multi.ligandAtomAt leftCenter 1 = carboxylL from by simp] at h
        rw [← he_c3] at h
        exact h.symm
      exact absurd ((e : Equiv.Perm Atom).injective heq) (by decide)
  have h2 : multi.ligandPermAt e leftCenter 2 = 2 := by
    have h := hσ 2
    rw [show multi.ligandAtomAt leftCenter 2 = c3 from by simp, he_c3] at h
    exact eq_two_of_right_ligand_eq_c3 h
  apply Equiv.ext
  intro k
  fin_cases k <;> simp [h0, h1, h2, h3]

theorem apply_rightCenter_eq_leftCenter_of_maps_middle_two_one (e : multi.Aut)
    (hefix : multi.centerPerm e middleCenter = middleCenter)
    (hmap : multi.ligandPermAt e middleCenter 2 = 1) :
    (e : Equiv.Perm Atom) c4 = c2 := by
  have h := multi.ligandAtomAt_ligandPermAt (e := e) (c := middleCenter) (i := 2)
  rw [hefix, hmap] at h
  simpa using h.symm

theorem centerPerm_right_eq_left_of_maps_middle_two_one (e : multi.Aut)
    (hefix : multi.centerPerm e middleCenter = middleCenter)
    (hmap : multi.ligandPermAt e middleCenter 2 = 1) :
    multi.centerPerm e rightCenter = leftCenter := by
  apply Subtype.ext
  simpa [MultiCenterMolecule.centerPerm, leftCenter, rightCenter] using
    apply_rightCenter_eq_leftCenter_of_maps_middle_two_one e hefix hmap

theorem ligandPermAt_rightCenter_eq_one_of_maps_middle_two_one (e : multi.Aut)
    (hefix : multi.centerPerm e middleCenter = middleCenter)
    (hmap : multi.ligandPermAt e middleCenter 2 = 1) :
    multi.ligandPermAt e rightCenter = 1 := by
  have he_c4 : (e : Equiv.Perm Atom) c4 = c2 :=
    apply_rightCenter_eq_leftCenter_of_maps_middle_two_one e hefix hmap
  have he_c3 : (e : Equiv.Perm Atom) c3 = c3 := by
    have h := congrArg Subtype.val hefix
    simpa [MultiCenterMolecule.centerPerm, middleCenter] using h
  have hcenter : multi.centerPerm e rightCenter = leftCenter :=
    centerPerm_right_eq_left_of_maps_middle_two_one e hefix hmap
  let eMol : multi.mol.Aut :=
    ⟨(e : Equiv.Perm Atom), MultiCenterMolecule.Aut.mem_molAut (m := multi) e⟩
  have hZaut : ∀ a : Atom, multi.mol.atomZ ((e : Equiv.Perm Atom) a) = multi.mol.atomZ a := by
    intro a
    simpa [eMol] using MoleculeGraph.Aut.atomZ_eq (m := multi.mol) eMol a
  have hσ : ∀ k : Fin 4,
      multi.ligandAtomAt leftCenter (multi.ligandPermAt e rightCenter k) =
        (e : Equiv.Perm Atom) (multi.ligandAtomAt rightCenter k) := by
    intro k
    have h := multi.ligandAtomAt_ligandPermAt (e := e) (c := rightCenter) (i := k)
    rwa [hcenter] at h
  have hZk : ∀ k : Fin 4,
      terminalZ (multi.ligandPermAt e rightCenter k) = terminalZ k := by
    intro k
    calc
      terminalZ (multi.ligandPermAt e rightCenter k)
          = multi.mol.atomZ
              (multi.ligandAtomAt leftCenter (multi.ligandPermAt e rightCenter k)) :=
            (atomZ_ligandAtomAt_left _).symm
      _ = multi.mol.atomZ
            ((e : Equiv.Perm Atom) (multi.ligandAtomAt rightCenter k)) := by rw [hσ k]
      _ = multi.mol.atomZ (multi.ligandAtomAt rightCenter k) := hZaut _
      _ = terminalZ k := atomZ_ligandAtomAt_right k
  have h0 : multi.ligandPermAt e rightCenter 0 = 0 := by
    refine eq_zero_of_terminalZ ?_
    simpa using hZk 0
  have h3 : multi.ligandPermAt e rightCenter 3 = 3 := by
    refine eq_three_of_terminalZ ?_
    simpa using hZk 3
  have h1 : multi.ligandPermAt e rightCenter 1 = 1 := by
    rcases eq_one_or_two_of_terminalZ (by simpa using hZk 1) with h1 | h1
    · exact h1
    · exfalso
      have heq : (e : Equiv.Perm Atom) carboxylR = (e : Equiv.Perm Atom) c3 := by
        have h := hσ 1
        rw [h1] at h
        rw [show multi.ligandAtomAt leftCenter 2 = c3 from by simp] at h
        rw [show multi.ligandAtomAt rightCenter 1 = carboxylR from by simp] at h
        rw [← he_c3] at h
        exact h.symm
      exact absurd ((e : Equiv.Perm Atom).injective heq) (by decide)
  have h2 : multi.ligandPermAt e rightCenter 2 = 2 := by
    have h := hσ 2
    rw [show multi.ligandAtomAt rightCenter 2 = c3 from by simp, he_c3] at h
    exact eq_two_of_left_ligand_eq_c3 h
  apply Equiv.ext
  intro k
  fin_cases k <;> simp [h0, h1, h2, h3]

/-! ### Transport facts for the original opposite-terminal configuration -/

/-- The two middle side branches are mirror-related under the actual half-turn symmetry. -/
theorem mirrorTransport_middle_one_two : MirrorTransport multi cfg middleCenter 1 2 := by
  unfold MirrorTransport BranchTransport
  refine ⟨flipAut, centerPerm_flipAut_middle, ligandPermAt_flipAut_middle_one, ?_⟩
  intro d hd
  have hd' : d = leftCenter := branchReaches_middle_one_center hd
  rw [hd']
  rw [cfg_sign_left, ligandPermAt_flipAut_left, centerPerm_flipAut_left, cfg_sign_right]
  norm_num [permHandedness_one]

theorem mirrorTransport_middle_two_one : MirrorTransport multi cfg middleCenter 2 1 := by
  unfold MirrorTransport BranchTransport
  refine ⟨flipAut, centerPerm_flipAut_middle, ligandPermAt_flipAut_middle_two, ?_⟩
  intro d hd
  have hd' : d = rightCenter := branchReaches_middle_two_center hd
  rw [hd']
  rw [cfg_sign_right, ligandPermAt_flipAut_right, centerPerm_flipAut_right, cfg_sign_left]
  norm_num [permHandedness_one]

/-- No proper transport of the left side branch to the right branch exists: every root-fixing
arm-exchange automorphism acts as the identity at the left terminal center, whose sign is `+1`,
while the right terminal center has sign `-1`. -/
theorem not_properTransport_middle_one_two : ¬ ProperTransport multi cfg middleCenter 1 2 := by
  intro h
  unfold ProperTransport BranchTransport at h
  rcases h with ⟨e, hefix, hmap, hcond⟩
  have hleft : multi.ligandPermAt e leftCenter = 1 :=
    ligandPermAt_leftCenter_eq_one_of_maps_middle_one_two e hefix hmap
  have hcenter : multi.centerPerm e leftCenter = rightCenter :=
    centerPerm_left_eq_right_of_maps_middle_one_two e hefix hmap
  have h := hcond leftCenter ligandBranchReaches_middle_one_leftCenter
  rw [hleft, hcenter, cfg_sign_left, cfg_sign_right] at h
  norm_num [permHandedness_one] at h

theorem not_properTransport_middle_two_one : ¬ ProperTransport multi cfg middleCenter 2 1 := by
  intro h
  unfold ProperTransport BranchTransport at h
  rcases h with ⟨e, hefix, hmap, hcond⟩
  have hright : multi.ligandPermAt e rightCenter = 1 :=
    ligandPermAt_rightCenter_eq_one_of_maps_middle_two_one e hefix hmap
  have hcenter : multi.centerPerm e rightCenter = leftCenter :=
    centerPerm_right_eq_left_of_maps_middle_two_one e hefix hmap
  have h := hcond rightCenter ligandBranchReaches_middle_two_rightCenter
  rw [hright, hcenter, cfg_sign_right, cfg_sign_left] at h
  norm_num [permHandedness_one] at h

/-- Exactly the two orientations of the unordered pair of middle side branches are
enantiomorphic in the original opposite-terminal configuration. -/
theorem enantiomorphic_middle_one_two : Enantiomorphic multi cfg middleCenter 1 2 := by
  unfold Enantiomorphic
  exact ⟨by decide, mirrorTransport_middle_one_two, not_properTransport_middle_one_two⟩

theorem enantiomorphic_middle_two_one : Enantiomorphic multi cfg middleCenter 2 1 := by
  unfold Enantiomorphic
  exact ⟨by decide, mirrorTransport_middle_two_one, not_properTransport_middle_two_one⟩

/-- The oxygen slot `0` and hydrogen slot `3` are fixed by every root-fixing automorphism, so the
only unordered enantiomorphic pair of middle branches is `{1, 2}`. -/
theorem enantiomorphic_middle_iff (i j : Fin 4) :
    Enantiomorphic multi cfg middleCenter i j ↔ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  constructor
  · intro h
    unfold Enantiomorphic MirrorTransport BranchTransport at h
    rcases h with ⟨hne, ⟨e, hefix, hmap, _⟩, _⟩
    exact perm_side_pair_of_fixes_zero_three (multi.ligandPermAt e middleCenter)
      (ligandPermAt_middle_fixes_zero_three e hefix).1
      (ligandPermAt_middle_fixes_zero_three e hefix).2 hmap hne
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact enantiomorphic_middle_one_two
    · exact enantiomorphic_middle_two_one

/-- The original configuration is mirror-related, not properly related, across the two side
branches. -/
theorem original_sideBranches_mirror_nonproper :
    MirrorTransport multi cfg middleCenter 1 2 ∧
      ¬ ProperTransport multi cfg middleCenter 1 2 ∧
        MirrorTransport multi cfg middleCenter 2 1 ∧
          ¬ ProperTransport multi cfg middleCenter 2 1 :=
  ⟨mirrorTransport_middle_one_two, not_properTransport_middle_one_two,
    mirrorTransport_middle_two_one, not_properTransport_middle_two_one⟩

/-! ### The same-terminal-sign regression

With both terminal signs equal, the half-turn symmetry is a proper transport of the side branches.
The half-turn induces the odd permutation `1 ↔ 2` at the attachment root, but that parity is not
part of the branch-transport condition, so it cannot block proper transport. -/

theorem sameTerminal_properTransport_middle_one_two :
    ProperTransport multi cfgSame middleCenter 1 2 := by
  unfold ProperTransport BranchTransport
  refine ⟨flipAut, centerPerm_flipAut_middle, ligandPermAt_flipAut_middle_one, ?_⟩
  intro d hd
  have hd' : d = leftCenter := branchReaches_middle_one_center hd
  rw [hd']
  rw [cfgSame_sign_left, ligandPermAt_flipAut_left, centerPerm_flipAut_left, cfgSame_sign_right]
  norm_num [permHandedness_one]

theorem sameTerminal_properTransport_middle_two_one :
    ProperTransport multi cfgSame middleCenter 2 1 := by
  unfold ProperTransport BranchTransport
  refine ⟨flipAut, centerPerm_flipAut_middle, ligandPermAt_flipAut_middle_two, ?_⟩
  intro d hd
  have hd' : d = rightCenter := branchReaches_middle_two_center hd
  rw [hd']
  rw [cfgSame_sign_right, ligandPermAt_flipAut_right, centerPerm_flipAut_right, cfgSame_sign_left]
  norm_num [permHandedness_one]

theorem sameTerminal_not_enantiomorphic_middle_one_two :
    ¬ Enantiomorphic multi cfgSame middleCenter 1 2 :=
  witness_not_enantiomorphic_of_properTransport cfgSame
    sameTerminal_properTransport_middle_one_two

theorem sameTerminal_not_enantiomorphic_middle_two_one :
    ¬ Enantiomorphic multi cfgSame middleCenter 2 1 :=
  witness_not_enantiomorphic_of_properTransport cfgSame
    sameTerminal_properTransport_middle_two_one

/-- Regression witness for the corrected semantics: proper branch transport holds in the
same-terminal-sign configuration even though the attachment root carries an odd induced ligand
permutation.  The old root-parity condition would have falsely rejected this case. -/
theorem sameTerminal_properTransport_with_odd_root :
    ProperTransport multi cfgSame middleCenter 1 2 ∧
      permHandedness (multi.ligandPermAt flipAut middleCenter) = -1 :=
  ⟨sameTerminal_properTransport_middle_one_two,
    permHandedness_ligandPermAt_flipAut_middle⟩

/-! ### Scope guard: whole-configuration achirality and pseudo mirror invariance

The corrected branch relation is a local statement about ligand branches.  It does not replace the
whole-configuration achirality result, nor the pseudoasymmetric descriptor's mirror invariance, and
it is not claimed to be a production CIP comparator by itself. -/

/-- The original fixture configuration remains achiral by the whole-configuration symmetry even
though the two middle side branches are enantiomorphic under the corrected branch relation. -/
theorem wholeConfiguration_achiral_with_enantiomorphic_sideBranches :
    multi.AchiralConfigurationBySymmetry cfg ∧ Enantiomorphic multi cfg middleCenter 1 2 :=
  ⟨achiralConfigurationBySymmetry, enantiomorphic_middle_one_two⟩

/-- The pseudoasymmetric descriptor's mirror invariance is preserved unchanged. -/
theorem pseudoDescriptor_mirror_invariant_preserved :
    pseudoDescriptor (-(multi.configurationSign cfg middleCenter))
        (RS.swap (multi.configurationRS cfg leftCenter))
        (RS.swap (multi.configurationRS cfg rightCenter)) =
      pseudoDescriptor (multi.configurationSign cfg middleCenter)
        (multi.configurationRS cfg leftCenter) (multi.configurationRS cfg rightCenter) :=
  middle_pseudoDescriptor_mirror_invariant

end TrihydroxyglutaricWitness

end RootedTetrahedralBranchSymmetry
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.WitnessBranchWalk.BranchWalk.start_ne_root
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.WitnessBranchWalk.BranchWalk.endpoint_ne_root
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.WitnessBranchWalk.BranchWalk.endpoint_mem_of_closed
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.WitnessBranchWalk.branchWalk_to_walk
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.WitnessBranchWalk.walk_to_branchWalk
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.WitnessBranchWalk.branchWalk_to_ligandBranchReaches
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.WitnessBranchWalk.ligandBranchReaches_iff_branchWalk
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.WitnessBranchWalk.ligandBranchReaches_not_root
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_left_zero
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_left_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_left_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_left_three
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_middle_zero
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_middle_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_middle_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_middle_three
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_right_zero
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_right_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_right_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandAtomAt_right_three
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.terminalZ
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.terminalZ_zero
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.terminalZ_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.terminalZ_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.terminalZ_three
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.atomZ_ligandAtomAt_left
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.atomZ_ligandAtomAt_middle
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.atomZ_ligandAtomAt_right
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.eq_zero_of_terminalZ
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.eq_three_of_terminalZ
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.eq_one_or_two_of_terminalZ
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.eq_two_of_right_ligand_eq_c3
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.eq_two_of_left_ligand_eq_c3
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.leftBranchAtoms
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.rightBranchAtoms
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.leftBranchAtoms_closed
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.rightBranchAtoms_closed
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.leftBranchAtoms_center_eq
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.rightBranchAtoms_center_eq
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.branchWalk_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.branchWalk_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandBranchReaches_middle_one_iff
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandBranchReaches_middle_two_iff
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.branchReaches_middle_one_center
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.branchReaches_middle_two_center
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandBranchReaches_middle_one_leftCenter
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandBranchReaches_middle_two_rightCenter
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.cfgSame
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.cfgSame_sign_left
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.cfgSame_sign_middle
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.cfgSame_sign_right
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.witness_not_enantiomorphic_of_properTransport
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.centerPerm_flipAut_middle
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.centerPerm_flipAut_left
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.centerPerm_flipAut_right
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandPermAt_flipAut_middle_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandPermAt_flipAut_middle_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandPermAt_middle_fixes_zero_three
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.perm_side_pair_of_fixes_zero_three
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.apply_leftCenter_eq_rightCenter_of_maps_middle_one_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.centerPerm_left_eq_right_of_maps_middle_one_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandPermAt_leftCenter_eq_one_of_maps_middle_one_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.apply_rightCenter_eq_leftCenter_of_maps_middle_two_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.centerPerm_right_eq_left_of_maps_middle_two_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.ligandPermAt_rightCenter_eq_one_of_maps_middle_two_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.mirrorTransport_middle_one_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.mirrorTransport_middle_two_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.not_properTransport_middle_one_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.not_properTransport_middle_two_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.enantiomorphic_middle_one_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.enantiomorphic_middle_two_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.enantiomorphic_middle_iff
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.original_sideBranches_mirror_nonproper
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.sameTerminal_properTransport_middle_one_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.sameTerminal_properTransport_middle_two_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.sameTerminal_not_enantiomorphic_middle_one_two
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.sameTerminal_not_enantiomorphic_middle_two_one
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.sameTerminal_properTransport_with_odd_root
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.wholeConfiguration_achiral_with_enantiomorphic_sideBranches
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.TrihydroxyglutaricWitness.pseudoDescriptor_mirror_invariant_preserved
