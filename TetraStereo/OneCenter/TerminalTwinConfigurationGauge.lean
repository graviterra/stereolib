import TetraStereo.OneCenter.MultiCenterConfiguration
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry

set_option autoImplicit false

/-!
# Terminal twins are a physical frame gauge

This module explains, inside the actual `MultiCenterMolecule` model, why a tetrahedral center that
carries two identical *terminal* ligands has no stereogenic descriptor: the absence is not missing
chemistry but a physical gauge.  Swapping the two terminal atoms is an automorphism of the complete
molecular graph (atom labels, charges, masses, and every bond order are preserved), it fixes every
distinguished center as a center, and it acts on the local frame at the twin center by an odd
ligand permutation.  Consequently the handedness sign at that center is not invariant, while every
other center is untouched.

No descriptor or comparator assertion is made here.  The sibling refusal module is responsible for
the claim that the localized descriptor model returns `none` on such physical twins; this module
supplies only the actual source-pair and gauge API that makes that refusal chemical rather than a
gap.

The main results are:

* `TerminalTwinPair.swapAut`: the actual atom swap as an `m.Aut`;
* `centerPerm_swapAut_apply`: the swap fixes every distinguished center;
* `ligandPermAt_swapAut_center`: at the twin center the local ligand permutation is the swap of the
  two actual ligand slots, hence `permHandedness = -1`;
* `ligandPermAt_swapAut_of_ne`: at every other center the local ligand permutation is the identity;
* `configurationSign_swapAut_apply`: the resulting sign law
  `sign (swapAut • cfg) d = if d = c then -sign cfg c else sign cfg d`;
* `configurationSign_familyAut_apply`: the finite correction law for a family of twin pairs at
  distinct centers, derived from leaf-neighbour uniqueness (disjoint supports), with no assumption
  of commutation and no assumed sign law;
* `configurationSign_familyAut_apply_subset` and `configurationSign_familyAut_subset`: the
  *subset* form needed by a consumer that corrects an arbitrary finite set of twin candidates:
  exactly the listed centers have their sign inverted, every unlisted center keeps its sign;
* `familyAut_achiralConfigurationBySymmetry`: if every center has a terminal twin, the mirror
  configuration's *sign pattern* is reached by an actual graph automorphism (sign-pattern equality,
  not literal configuration equality or a Cartesian isometry), so the absence of a stereogenic
  centre is a gauge phenomenon.
-/

namespace TetraStereo
namespace OneCenter
namespace TerminalTwinConfigurationGauge

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : MultiCenterMolecule V}
variable {c : m.Center} {a b : V}

/-! ### The actual source pair -/

/-- A pair of *terminal twin* atoms at a distinguished center.

All fields are read off the actual molecular graph: `a` and `b` are distinct, each has the center
`c` as its unique neighbour, they carry the same atomic number, mass number and formal charge, and
the two bonds to the center have the same order.  Positivity of that common bond order is *not*
assumed: it follows from `neighbor_a` (see `bond_pos_left`).  No distinguished-center membership of
`a` or `b` is assumed either; it is derived from the four distinct ligands of `m` (see
`not_mem_centers_of_terminal`). -/
structure TerminalTwinPair (m : MultiCenterMolecule V) (c : m.Center) (a b : V) : Prop where
  /-- The two terminal atoms are distinct. -/
  ne : a ≠ b
  /-- `a` has exactly one neighbour, the center. -/
  neighbor_a : m.mol.neighborFinset a = {c.1}
  /-- `b` has exactly one neighbour, the center. -/
  neighbor_b : m.mol.neighborFinset b = {c.1}
  /-- Equal atomic numbers. -/
  z_eq : m.mol.atomZ a = m.mol.atomZ b
  /-- Equal mass numbers. -/
  mass_eq : m.mol.atomMass a = m.mol.atomMass b
  /-- Equal formal charges. -/
  charge_eq : m.mol.formalCharge a = m.mol.formalCharge b
  /-- Equal (positive, in the single-bond initial domain) bond orders to the center. -/
  bond_eq : m.mol.bond c.1 a = m.mol.bond c.1 b

namespace TerminalTwinPair

variable (h : TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair m c a b)

include h

/-- The terminal atom `a` is adjacent to the center. -/
theorem adj_ca : m.mol.Adj c.1 a := by
  have hmem : c.1 ∈ m.mol.neighborFinset a := by
    rw [h.neighbor_a]
    exact Finset.mem_singleton_self c.1
  have hadj : m.mol.Adj a c.1 := (MoleculeGraph.mem_neighborFinset m.mol a c.1).1 hmem
  exact (m.mol.adj_symm (u := c.1) (v := a)).mpr hadj

/-- The terminal atom `b` is adjacent to the center. -/
theorem adj_cb : m.mol.Adj c.1 b := by
  have hmem : c.1 ∈ m.mol.neighborFinset b := by
    rw [h.neighbor_b]
    exact Finset.mem_singleton_self c.1
  have hadj : m.mol.Adj b c.1 := (MoleculeGraph.mem_neighborFinset m.mol b c.1).1 hmem
  exact (m.mol.adj_symm (u := c.1) (v := b)).mpr hadj

/-- The common bond order is positive.  This is *derived* from terminality, not assumed. -/
theorem bond_pos_left : 0 < m.mol.bond c.1 a :=
  h.adj_ca

/-- The bond order on the other twin is positive, derived from terminality. -/
theorem bond_pos_right : 0 < m.mol.bond c.1 b :=
  h.adj_cb

/-- The terminal twin bonds are equal and positive, as required by the source pair. -/
theorem bond_eq_positive :
    m.mol.bond c.1 a = m.mol.bond c.1 b ∧ 0 < m.mol.bond c.1 a :=
  ⟨h.bond_eq, h.bond_pos_left⟩

omit h in
/-- A terminal atom is not a distinguished center: if it were, the four ligand atoms of that
center would all have to lie in the singleton neighbour set, contradicting injectivity of the
ligand enumeration of `m`. -/
theorem not_mem_centers_of_terminal {v z : V}
    (hv : m.mol.neighborFinset v = {z}) : v ∉ m.centers := by
  intro hvc
  let d : m.Center := ⟨v, hvc⟩
  have hmem0 : m.ligandAtomAt d 0 ∈ m.mol.neighborFinset v := by
    have hadj := m.ligandAtomAt_adj d 0
    exact (MoleculeGraph.mem_neighborFinset m.mol v (m.ligandAtomAt d 0)).2 hadj
  have hmem1 : m.ligandAtomAt d 1 ∈ m.mol.neighborFinset v := by
    have hadj := m.ligandAtomAt_adj d 1
    exact (MoleculeGraph.mem_neighborFinset m.mol v (m.ligandAtomAt d 1)).2 hadj
  rw [hv] at hmem0 hmem1
  simp only [Finset.mem_singleton] at hmem0 hmem1
  have h01 : (0 : Fin 4) = 1 :=
    m.ligandAtomAt_injective d (hmem0.trans hmem1.symm)
  exact absurd h01 (by decide)

/-- The terminal atom `a` is not a distinguished center. -/
theorem leaf_not_mem_centers_a : a ∉ m.centers :=
  not_mem_centers_of_terminal h.neighbor_a

/-- The terminal atom `b` is not a distinguished center. -/
theorem leaf_not_mem_centers_b : b ∉ m.centers :=
  not_mem_centers_of_terminal h.neighbor_b

/-- The terminal atom `a` is not the center atom itself. -/
theorem leaf_ne_center_a : a ≠ c.1 :=
  fun he => h.leaf_not_mem_centers_a (he ▸ c.2)

/-- The terminal atom `b` is not the center atom itself. -/
theorem leaf_ne_center_b : b ≠ c.1 :=
  fun he => h.leaf_not_mem_centers_b (he ▸ c.2)

/-- A terminal atom at a different center is not any atom of this pair. -/
theorem leaf_ne_of_center_ne {d : m.Center} (_hdc : d ≠ c) : a ≠ d.1 ∧ b ≠ d.1 := by
  refine ⟨?_, ?_⟩
  · intro he
    exact h.leaf_not_mem_centers_a (he ▸ d.2)
  · intro he
    exact h.leaf_not_mem_centers_b (he ▸ d.2)

/-! ### Bond-order bookkeeping for the swap -/

omit h in
/-- If `v` is not the unique neighbour `z` of `x`, then the bond order `x`-`v` is zero. -/
theorem bond_eq_zero_of_neighborFinset_singleton {x v z : V}
    (hx : m.mol.neighborFinset x = {z}) (hv : v ≠ z) : m.mol.bond x v = 0 := by
  by_contra hne
  have hpos : 0 < m.mol.bond x v := Nat.pos_of_ne_zero hne
  have hmem : v ∈ m.mol.neighborFinset x :=
    (MoleculeGraph.mem_neighborFinset m.mol x v).2 hpos
  rw [hx] at hmem
  exact hv (by simpa using hmem)

/-- The bond order to the left twin equals the bond order to the right twin, away from the two
terminal atoms themselves. -/
theorem bond_b_eq_bond_a_of_ne {v : V} (hva : v ≠ a) (hvb : v ≠ b) :
    m.mol.bond b v = m.mol.bond a v := by
  by_cases hvc : v = c.1
  · subst hvc
    rw [m.mol.bond_symm b c.1, m.mol.bond_symm a c.1]
    exact h.bond_eq.symm
  · rw [bond_eq_zero_of_neighborFinset_singleton h.neighbor_b hvc,
      bond_eq_zero_of_neighborFinset_singleton h.neighbor_a hvc]

/-- Symmetric orientation of `bond_b_eq_bond_a_of_ne`. -/
theorem bond_a_eq_bond_b_of_ne {v : V} (hva : v ≠ a) (hvb : v ≠ b) :
    m.mol.bond a v = m.mol.bond b v :=
  (h.bond_b_eq_bond_a_of_ne hva hvb).symm

/-- In the first argument, the bond to the right twin equals the bond to the left twin, away from
the center. -/
theorem bond_u_b_eq_bond_u_a_of_ne {u : V} (hua : u ≠ a) (hub : u ≠ b) :
    m.mol.bond u b = m.mol.bond u a := by
  by_cases huc : u = c.1
  · subst huc
    exact h.bond_eq.symm
  · rw [m.mol.bond_symm u b, m.mol.bond_symm u a,
      bond_eq_zero_of_neighborFinset_singleton h.neighbor_b huc,
      bond_eq_zero_of_neighborFinset_singleton h.neighbor_a huc]

/-- Symmetric orientation of `bond_u_b_eq_bond_u_a_of_ne`. -/
theorem bond_u_a_eq_bond_u_b_of_ne {u : V} (hua : u ≠ a) (hub : u ≠ b) :
    m.mol.bond u a = m.mol.bond u b :=
  (h.bond_u_b_eq_bond_u_a_of_ne hua hub).symm

/-- The atom swap `a ↔ b` preserves every bond order. -/
theorem swap_apply_bond (u v : V) :
    m.mol.bond (Equiv.swap a b u) (Equiv.swap a b v) = m.mol.bond u v := by
  by_cases hua : u = a
  · rw [hua]
    by_cases hva : v = a
    · rw [hva, Equiv.swap_apply_left, m.mol.bond_self, m.mol.bond_self]
    · by_cases hvb : v = b
      · rw [hvb, Equiv.swap_apply_left, Equiv.swap_apply_right]
        exact m.mol.bond_symm b a
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hva hvb]
        exact (h.bond_a_eq_bond_b_of_ne hva hvb).symm
  · by_cases hub : u = b
    · rw [hub]
      by_cases hva : v = a
      · rw [hva, Equiv.swap_apply_right, Equiv.swap_apply_left]
        exact m.mol.bond_symm a b
      · by_cases hvb : v = b
        · rw [hvb, Equiv.swap_apply_right, m.mol.bond_self, m.mol.bond_self]
        · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hva hvb]
          exact h.bond_a_eq_bond_b_of_ne hva hvb
    · rw [Equiv.swap_apply_of_ne_of_ne hua hub]
      by_cases hva : v = a
      · rw [hva, Equiv.swap_apply_left]
        exact h.bond_u_b_eq_bond_u_a_of_ne hua hub
      · by_cases hvb : v = b
        · rw [hvb, Equiv.swap_apply_right]
          exact h.bond_u_a_eq_bond_u_b_of_ne hua hub
        · rw [Equiv.swap_apply_of_ne_of_ne hva hvb]

/-- The atom swap `a ↔ b` is an automorphism of the underlying molecular graph, because the two
atoms have the same labels and the same bond-order profile. -/
theorem swap_mem_molAut : Equiv.swap a b ∈ m.mol.Aut := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hva : v = a
    · subst hva
      rw [Equiv.swap_apply_left]
      exact h.z_eq.symm
    · by_cases hvb : v = b
      · subst hvb
        rw [Equiv.swap_apply_right]
        exact h.z_eq
      · rw [Equiv.swap_apply_of_ne_of_ne hva hvb]
  · intro v
    by_cases hva : v = a
    · subst hva
      rw [Equiv.swap_apply_left]
      exact h.mass_eq.symm
    · by_cases hvb : v = b
      · subst hvb
        rw [Equiv.swap_apply_right]
        exact h.mass_eq
      · rw [Equiv.swap_apply_of_ne_of_ne hva hvb]
  · intro v
    by_cases hva : v = a
    · subst hva
      rw [Equiv.swap_apply_left]
      exact h.charge_eq.symm
    · by_cases hvb : v = b
      · subst hvb
        rw [Equiv.swap_apply_right]
        exact h.charge_eq
      · rw [Equiv.swap_apply_of_ne_of_ne hva hvb]
  · intro u v
    exact h.swap_apply_bond u v

/-- The atom swap `a ↔ b` preserves the distinguished-center set: the two swapped atoms are not
centers at all. -/
theorem swap_preservesCenters : m.PreservesCenters (Equiv.swap a b) := by
  intro x
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left]
    exact iff_of_false h.leaf_not_mem_centers_a h.leaf_not_mem_centers_b
  · by_cases hxb : x = b
    · subst hxb
      rw [Equiv.swap_apply_right]
      exact iff_of_false h.leaf_not_mem_centers_b h.leaf_not_mem_centers_a
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- The actual source swap is an automorphism of the multi-center molecule. -/
theorem swap_mem_aut : Equiv.swap a b ∈ m.Aut :=
  ⟨h.swap_mem_molAut, h.swap_preservesCenters⟩

/-- The terminal twin swap, regarded as an actual multi-center automorphism. -/
def swapAut : m.Aut :=
  ⟨Equiv.swap a b, h.swap_mem_aut⟩

@[simp] theorem swapAut_coe : (h.swapAut : Equiv.Perm V) = Equiv.swap a b := rfl

/-- The twin swap fixes every distinguished center. -/
theorem centerPerm_swapAut_apply (d : m.Center) : m.centerPerm h.swapAut d = d := by
  apply Subtype.ext
  change Equiv.swap a b d.1 = d.1
  by_cases hda : d.1 = a
  · exact absurd (hda ▸ d.2) h.leaf_not_mem_centers_a
  · by_cases hdb : d.1 = b
    · exact absurd (hdb ▸ d.2) h.leaf_not_mem_centers_b
    · exact Equiv.swap_apply_of_ne_of_ne hda hdb

/-- Consequently the induced permutation of distinguished centers is the identity. -/
theorem centerPerm_swapAut : m.centerPerm h.swapAut = 1 := by
  refine Equiv.ext (fun d => ?_)
  exact h.centerPerm_swapAut_apply d

/-- A ligand atom at any *other* center is not one of the two terminal atoms. -/
theorem ligandAtomAt_ne_terminal_left {d : m.Center} (hdc : d ≠ c) (i : Fin 4) :
    m.ligandAtomAt d i ≠ a := by
  intro heq
  have hadj : m.mol.Adj d.1 a := by
    rw [← heq]
    exact m.ligandAtomAt_adj d i
  have hmem : d.1 ∈ m.mol.neighborFinset a :=
    (MoleculeGraph.mem_neighborFinset m.mol a d.1).2
      ((m.mol.adj_symm (u := a) (v := d.1)).mpr hadj)
  rw [h.neighbor_a] at hmem
  simp only [Finset.mem_singleton] at hmem
  exact hdc (Subtype.ext hmem)

/-- A ligand atom at any *other* center is not one of the two terminal atoms (right twin). -/
theorem ligandAtomAt_ne_terminal_right {d : m.Center} (hdc : d ≠ c) (i : Fin 4) :
    m.ligandAtomAt d i ≠ b := by
  intro heq
  have hadj : m.mol.Adj d.1 b := by
    rw [← heq]
    exact m.ligandAtomAt_adj d i
  have hmem : d.1 ∈ m.mol.neighborFinset b :=
    (MoleculeGraph.mem_neighborFinset m.mol b d.1).2
      ((m.mol.adj_symm (u := b) (v := d.1)).mpr hadj)
  rw [h.neighbor_b] at hmem
  simp only [Finset.mem_singleton] at hmem
  exact hdc (Subtype.ext hmem)

/-- At every center other than the twin center, the swap induces the identity ligand permutation:
the terminal atoms are not ligands of any other center. -/
theorem ligandPermAt_swapAut_of_ne {d : m.Center} (hdc : d ≠ c) :
    m.ligandPermAt h.swapAut d = 1 := by
  classical
  refine Equiv.ext (fun i => ?_)
  apply m.ligandAtomAt_injective d
  have hchar := m.ligandAtomAt_ligandPermAt (e := h.swapAut) (c := d) i
  rw [h.centerPerm_swapAut_apply] at hchar
  rw [hchar]
  show Equiv.swap a b (m.ligandAtomAt d i) = m.ligandAtomAt d i
  rw [Equiv.swap_apply_of_ne_of_ne (h.ligandAtomAt_ne_terminal_left hdc i)
    (h.ligandAtomAt_ne_terminal_right hdc i)]

/-! ### The two actual ligand slots of the twins -/

/-- The actual ligand slot at the center occupied by the terminal atom `a`. -/
def twinSlotA : Fin 4 :=
  Classical.choose (m.ligandAtomAt_surjective c a h.adj_ca)

/-- The actual ligand slot at the center occupied by the terminal atom `b`. -/
def twinSlotB : Fin 4 :=
  Classical.choose (m.ligandAtomAt_surjective c b h.adj_cb)

/-- Definitional unfolding of the left slot. -/
theorem twinSlotA_spec : m.ligandAtomAt c h.twinSlotA = a :=
  Classical.choose_spec (m.ligandAtomAt_surjective c a h.adj_ca)

/-- Definitional unfolding of the right slot. -/
theorem twinSlotB_spec : m.ligandAtomAt c h.twinSlotB = b :=
  Classical.choose_spec (m.ligandAtomAt_surjective c b h.adj_cb)

/-- The two actual slots are distinct. -/
theorem twinSlotA_ne_twinSlotB : h.twinSlotA ≠ h.twinSlotB := by
  intro heq
  apply h.ne
  calc
    a = m.ligandAtomAt c h.twinSlotA := h.twinSlotA_spec.symm
    _ = m.ligandAtomAt c h.twinSlotB := by rw [heq]
    _ = b := h.twinSlotB_spec

omit [Fintype V] [DecidableEq V] h in
/-- The sign of a transposition of two distinct ligand indices is `-1`. -/
theorem permHandedness_swap_of_ne {i j : Fin 4} (hij : i ≠ j) :
    permHandedness (Equiv.swap i j) = -1 := by
  norm_num [permHandedness, Equiv.Perm.sign_swap hij]

/-- At the twin center, the swap induces exactly the transposition of the two actual ligand slots
occupied by the terminal atoms. -/
theorem ligandPermAt_swapAut_center :
    m.ligandPermAt h.swapAut c = Equiv.swap h.twinSlotA h.twinSlotB := by
  classical
  refine Equiv.ext (fun i => ?_)
  apply m.ligandAtomAt_injective c
  have hchar := m.ligandAtomAt_ligandPermAt (e := h.swapAut) (c := c) i
  rw [h.centerPerm_swapAut_apply] at hchar
  rw [hchar]
  show Equiv.swap a b (m.ligandAtomAt c i) =
    m.ligandAtomAt c (Equiv.swap h.twinSlotA h.twinSlotB i)
  by_cases hiA : i = h.twinSlotA
  · subst hiA
    rw [h.twinSlotA_spec, Equiv.swap_apply_left, Equiv.swap_apply_left, h.twinSlotB_spec]
  · by_cases hiB : i = h.twinSlotB
    · subst hiB
      rw [h.twinSlotB_spec, Equiv.swap_apply_right, Equiv.swap_apply_right, h.twinSlotA_spec]
    · have hia : m.ligandAtomAt c i ≠ a := by
        intro heq
        exact hiA (m.ligandAtomAt_injective c (heq.trans h.twinSlotA_spec.symm))
      have hib : m.ligandAtomAt c i ≠ b := by
        intro heq
        exact hiB (m.ligandAtomAt_injective c (heq.trans h.twinSlotB_spec.symm))
      rw [Equiv.swap_apply_of_ne_of_ne hia hib,
        Equiv.swap_apply_of_ne_of_ne hiA hiB]

/-- The local handedness at the twin center is inverted by the physical swap. -/
theorem permHandedness_ligandPermAt_swapAut_center :
    permHandedness (m.ligandPermAt h.swapAut c) = -1 := by
  rw [h.ligandPermAt_swapAut_center]
  exact permHandedness_swap_of_ne h.twinSlotA_ne_twinSlotB

/-! ### The single-pair sign law -/

/-- The actual twin swap flips the configuration sign at the twin center and fixes it at every
other center. -/
theorem configurationSign_swapAut_apply (cfg : m.Configuration) (d : m.Center) :
    m.configurationSign (h.swapAut • cfg) d =
      if d = c then -m.configurationSign cfg c else m.configurationSign cfg d := by
  have hsign := m.configurationSign_smul (e := h.swapAut) (cfg := cfg) (c := d)
  rw [h.centerPerm_swapAut] at hsign
  simp only [inv_one, Equiv.Perm.one_apply] at hsign
  rw [hsign]
  by_cases hd : d = c
  · subst hd
    rw [if_pos rfl, h.ligandPermAt_swapAut_center,
      permHandedness_swap_of_ne h.twinSlotA_ne_twinSlotB]
    ring
  · rw [if_neg hd, h.ligandPermAt_swapAut_of_ne hd, permHandedness_one]
    ring

/-- Packaged gauge API: the actual atom swap, its centre action, its local ligand permutation, and
the resulting sign law. -/
theorem terminalTwin_gauge (cfg : m.Configuration) :
    ∃ e : m.Aut,
      (e : Equiv.Perm V) = Equiv.swap a b ∧
      m.centerPerm e c = c ∧
      m.ligandPermAt e c = Equiv.swap h.twinSlotA h.twinSlotB ∧
      permHandedness (m.ligandPermAt e c) = -1 ∧
      ∀ d : m.Center, m.configurationSign (e • cfg) d =
        if d = c then -m.configurationSign cfg c else m.configurationSign cfg d := by
  refine ⟨h.swapAut, rfl, h.centerPerm_swapAut_apply c,
    h.ligandPermAt_swapAut_center, h.permHandedness_ligandPermAt_swapAut_center, ?_⟩
  intro d
  exact h.configurationSign_swapAut_apply cfg d

end TerminalTwinPair

/-! ### Families of twins at distinct centers -/

section Family

variable {ι : Type*} {idx : ι → m.Center} {A B : ι → V}

/-- A finite family of terminal twin pairs, one at each of a family of *distinct* centers.

Distinctness of the centers is the only structural hypothesis of the family.  It is what makes the
supports of the individual atom swaps disjoint by leaf-neighbour uniqueness; commutation of the
swaps and the sign-correction law are derived below, never assumed. -/
structure TerminalTwinFamily (m : MultiCenterMolecule V) (idx : ι → m.Center)
    (A B : ι → V) : Prop where
  /-- Each index carries an actual terminal twin pair at its center. -/
  twin : ∀ i, TerminalTwinPair m (idx i) (A i) (B i)
  /-- The centers of the family are distinct. -/
  injective_center : Function.Injective idx

namespace TerminalTwinFamily

variable (h : TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinFamily m idx A B)

include h

/-- Leaf-neighbour uniqueness: the two atoms of a twin pair at one center are never atoms of a
twin pair at a different center.  This is the derived disjoint-support statement. -/
theorem twin_atoms_ne {i j : ι} (hij : i ≠ j) :
    A i ≠ A j ∧ A i ≠ B j ∧ B i ≠ A j ∧ B i ≠ B j := by
  have hcij : idx i ≠ idx j := fun hc => hij (h.injective_center hc)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    have hadj : m.mol.Adj (idx i).1 (A j) := by
      rw [← heq]
      exact (h.twin i).adj_ca
    have hmem : (idx i).1 ∈ m.mol.neighborFinset (A j) :=
      (MoleculeGraph.mem_neighborFinset m.mol (A j) (idx i).1).2
        ((m.mol.adj_symm (u := (idx i).1) (v := A j)).mp hadj)
    rw [(h.twin j).neighbor_a] at hmem
    simp only [Finset.mem_singleton] at hmem
    exact hcij (Subtype.ext hmem)
  · intro heq
    have hadj : m.mol.Adj (idx i).1 (B j) := by
      rw [← heq]
      exact (h.twin i).adj_ca
    have hmem : (idx i).1 ∈ m.mol.neighborFinset (B j) :=
      (MoleculeGraph.mem_neighborFinset m.mol (B j) (idx i).1).2
        ((m.mol.adj_symm (u := (idx i).1) (v := B j)).mp hadj)
    rw [(h.twin j).neighbor_b] at hmem
    simp only [Finset.mem_singleton] at hmem
    exact hcij (Subtype.ext hmem)
  · intro heq
    have hadj : m.mol.Adj (idx i).1 (A j) := by
      rw [← heq]
      exact (h.twin i).adj_cb
    have hmem : (idx i).1 ∈ m.mol.neighborFinset (A j) :=
      (MoleculeGraph.mem_neighborFinset m.mol (A j) (idx i).1).2
        ((m.mol.adj_symm (u := (idx i).1) (v := A j)).mp hadj)
    rw [(h.twin j).neighbor_a] at hmem
    simp only [Finset.mem_singleton] at hmem
    exact hcij (Subtype.ext hmem)
  · intro heq
    have hadj : m.mol.Adj (idx i).1 (B j) := by
      rw [← heq]
      exact (h.twin i).adj_cb
    have hmem : (idx i).1 ∈ m.mol.neighborFinset (B j) :=
      (MoleculeGraph.mem_neighborFinset m.mol (B j) (idx i).1).2
        ((m.mol.adj_symm (u := (idx i).1) (v := B j)).mp hadj)
    rw [(h.twin j).neighbor_b] at hmem
    simp only [Finset.mem_singleton] at hmem
    exact hcij (Subtype.ext hmem)

/-- At the center of a *different* family member, the swap belonging to member `j` acts as the
identity on the local frame. -/
theorem ligandPermAt_other_swapAut {i j : ι} (hij : i ≠ j) :
    m.ligandPermAt (h.twin j).swapAut (idx i) = 1 := by
  apply (h.twin j).ligandPermAt_swapAut_of_ne
  intro heq
  exact hij (h.injective_center heq)

/-- The composition of a list of family swaps, processed from the right. -/
def familyAut : List ι → m.Aut
  | [] => 1
  | i :: rest => (h.twin i).swapAut * familyAut rest

/-- Every family swap fixes each distinguished center, hence so does any composite. -/
theorem centerPerm_familyAut_apply (l : List ι) (d : m.Center) :
    m.centerPerm (h.familyAut l) d = d := by
  induction l with
  | nil =>
      show m.centerPerm (1 : m.Aut) d = d
      exact TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.centerPerm_one_apply m d
  | cons i rest ih =>
      have hfami : h.familyAut (i :: rest) = (h.twin i).swapAut * h.familyAut rest := rfl
      rw [hfami]
      rw [TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.centerPerm_mul_apply]
      rw [ih]
      exact (h.twin i).centerPerm_swapAut_apply d

/-- If a center is not the center of any family member in the list, the composite acts as the
identity on that center's local frame. -/
theorem ligandPermAt_familyAut_of_not_mem (l : List ι) (d : m.Center)
    (hd : d ∉ l.map idx) : m.ligandPermAt (h.familyAut l) d = 1 := by
  induction l with
  | nil =>
      show m.ligandPermAt (1 : m.Aut) d = 1
      exact m.ligandPermAt_one d
  | cons i rest ih =>
      have hfami : h.familyAut (i :: rest) = (h.twin i).swapAut * h.familyAut rest := rfl
      have hd_rest : d ∉ rest.map idx := by
        intro hmem
        exact hd (by
          rw [List.map_cons]
          exact List.mem_cons_of_mem _ hmem)
      have hd_head : d ≠ idx i := by
        intro hmem
        exact hd (by
          rw [List.map_cons, ← hmem]
          exact List.mem_cons_self)
      rw [hfami, m.ligandPermAt_mul, h.centerPerm_familyAut_apply]
      rw [(h.twin i).ligandPermAt_swapAut_of_ne hd_head, ih hd_rest, one_mul]

/-- At the center of a listed family member, the composite acts by exactly that member's actual
two-slot transposition. -/
theorem ligandPermAt_familyAut_at_index (l : List ι) (hnodup : l.Nodup) (i : ι) (hi : i ∈ l) :
    m.ligandPermAt (h.familyAut l) (idx i) =
      Equiv.swap (h.twin i).twinSlotA (h.twin i).twinSlotB := by
  induction l with
  | nil => simp at hi
  | cons j rest ih =>
      have hnot : j ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hfami : h.familyAut (j :: rest) = (h.twin j).swapAut * h.familyAut rest := rfl
      rw [hfami, m.ligandPermAt_mul, h.centerPerm_familyAut_apply]
      by_cases hij : i = j
      · subst hij
        have hd_rest : idx i ∉ rest.map idx := by
          intro hmem
          rw [List.mem_map] at hmem
          rcases hmem with ⟨k, hk, hik⟩
          exact hnot (h.injective_center hik ▸ hk)
        rw [(h.twin i).ligandPermAt_swapAut_center,
          h.ligandPermAt_familyAut_of_not_mem rest (idx i) hd_rest, mul_one]
      · have hi_rest : i ∈ rest := by
          rcases List.mem_cons.mp hi with hmem | hmem
          · exact absurd hmem hij
          · exact hmem
        have hne : idx i ≠ idx j := fun heq => hij (h.injective_center heq)
        rw [(h.twin j).ligandPermAt_swapAut_of_ne hne,
          ih hrest hi_rest, one_mul]

end TerminalTwinFamily

end Family

/-! ### The finite correction law -/

section Correction

variable {ι : Type*} {idx : ι → m.Center} {A B : ι → V}

/-- The finite sign-correction law for a family of twins at distinct centers.

The correction at a center `d` is the product of `-1` over the listed family members whose center
is `d` and `1` over all others.  The proof is by induction on the list and uses only the derived
per-member facts: every swap fixes all centers and acts as the identity away from its own center.
Neither commutation of the swaps nor the sign law is assumed. -/
theorem configurationSign_familyAut_apply (h : TerminalTwinFamily m idx A B) (l : List ι)
    (hnodup : l.Nodup) (cfg : m.Configuration) (d : m.Center) :
    m.configurationSign (h.familyAut l • cfg) d =
      (l.map (fun i => if idx i = d then (-1 : ℝ) else 1)).prod *
        m.configurationSign cfg d := by
  induction l generalizing cfg d with
  | nil =>
      show m.configurationSign ((1 : m.Aut) • cfg) d = (1 : ℝ) * m.configurationSign cfg d
      rw [one_smul, one_mul]
  | cons i rest ih =>
      have hnot : i ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hfami : h.familyAut (i :: rest) = (h.twin i).swapAut * h.familyAut rest := rfl
      rw [hfami, mul_smul]
      rw [(h.twin i).configurationSign_swapAut_apply]
      rw [ih hrest cfg (idx i), ih hrest cfg d]
      by_cases hd : d = idx i
      · subst d
        have hrest_one :
            (rest.map (fun j => if idx j = idx i then (-1 : ℝ) else 1)).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          rw [List.mem_map] at hx
          rcases hx with ⟨j, hj, rfl⟩
          have hji : j ≠ i := fun he => hnot (he ▸ hj)
          have hne : idx j ≠ idx i := fun he => hji (h.injective_center he)
          simp [hne]
        rw [if_pos rfl, List.map_cons, List.prod_cons, if_pos rfl, hrest_one]
        ring
      · have hne : ¬ idx i = d := fun he => hd he.symm
        rw [if_neg hd, List.map_cons, List.prod_cons, if_neg hne]
        ring

end Correction

/-! ### Achirality from a complete family of terminal twins -/

section Complete

variable {ι : Type*} {idx : ι → m.Center} {A B : ι → V}

/-- If a center occurs in the list of family centers, the correction product there is exactly
`-1`.  Distinctness of the centers (injectivity of `idx` together with `l.Nodup`) makes the
matching family member unique. -/
theorem familyCorrection_eq_neg_one_of_mem (h : TerminalTwinFamily m idx A B) (l : List ι)
    (hnodup : l.Nodup) (d : m.Center) (hd : d ∈ l.map idx) :
    (l.map (fun i => if idx i = d then (-1 : ℝ) else 1)).prod = -1 := by
  induction l with
  | nil => simp at hd
  | cons i rest ih =>
      have hnot : i ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hmem : d = idx i ∨ d ∈ rest.map idx := by
        simpa [List.map_cons] using hd
      by_cases hci : idx i = d
      · have hrest_one :
            (rest.map (fun j => if idx j = d then (-1 : ℝ) else 1)).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          rw [List.mem_map] at hx
          rcases hx with ⟨j, hj, rfl⟩
          have hji : j ≠ i := fun he => hnot (he ▸ hj)
          have hne : idx j ≠ d := fun he => hji (h.injective_center (he.trans hci.symm))
          simp [hne]
        rw [List.map_cons, List.prod_cons, if_pos hci, hrest_one]
        simp
      · have hd_rest : d ∈ rest.map idx := by
          rcases hmem with h | h
          · exact absurd h.symm hci
          · exact h
        rw [List.map_cons, List.prod_cons, if_neg hci, one_mul]
        exact ih hrest hd_rest

/-- If a center is not the center of any listed family member, the correction product there is
`1`: every factor in the product is `1`. -/
theorem familyCorrection_eq_one_of_not_mem (l : List ι) (d : m.Center)
    (hd : d ∉ l.map idx) :
    (l.map (fun i => if idx i = d then (-1 : ℝ) else 1)).prod = 1 := by
  apply List.prod_eq_one
  intro x hx
  rw [List.mem_map] at hx
  rcases hx with ⟨i, hi, rfl⟩
  have hne : idx i ≠ d := fun he => hd (List.mem_map.mpr ⟨i, hi, he⟩)
  simp [hne]

/-- Subset correction: for an arbitrary finite list of terminal-twin candidates at distinct
centers, the composite gauge flips exactly the signs at the listed centers and leaves every other
sign unchanged.  No commutation and no a priori sign law is used. -/
theorem configurationSign_familyAut_apply_subset (h : TerminalTwinFamily m idx A B)
    (l : List ι) (hnodup : l.Nodup) (cfg : m.Configuration) (d : m.Center) :
    m.configurationSign (h.familyAut l • cfg) d =
      if d ∈ l.map idx then -m.configurationSign cfg d else m.configurationSign cfg d := by
  rw [configurationSign_familyAut_apply h l hnodup cfg d]
  by_cases hd : d ∈ l.map idx
  · rw [if_pos hd, familyCorrection_eq_neg_one_of_mem h l hnodup d hd]
    ring
  · rw [if_neg hd, familyCorrection_eq_one_of_not_mem l d hd, one_mul]

/-- Sign-correction at a listed center: the composite family gauge flips the sign there. -/
theorem configurationSign_familyAut_apply_at_index (h : TerminalTwinFamily m idx A B)
    (l : List ι) (hnodup : l.Nodup) (cfg : m.Configuration) (i : ι) (hi : i ∈ l) :
    m.configurationSign (h.familyAut l • cfg) (idx i) =
      -m.configurationSign cfg (idx i) := by
  rw [configurationSign_familyAut_apply h l hnodup cfg (idx i),
    familyCorrection_eq_neg_one_of_mem h l hnodup (idx i)
      (List.mem_map.mpr ⟨i, hi, rfl⟩)]
  ring

/-- Unlisted centers are untouched by the composite family gauge. -/
theorem configurationSign_familyAut_apply_of_not_mem (h : TerminalTwinFamily m idx A B)
    (l : List ι) (hnodup : l.Nodup) (cfg : m.Configuration) (d : m.Center)
    (hd : d ∉ l.map idx) :
    m.configurationSign (h.familyAut l • cfg) d = m.configurationSign cfg d := by
  rw [configurationSign_familyAut_apply h l hnodup cfg d,
    familyCorrection_eq_one_of_not_mem l d hd, one_mul]

/-- Packaged subset gauge: exactly the listed centers have their configuration sign inverted,
while every unlisted center keeps its sign. -/
theorem configurationSign_familyAut_subset (h : TerminalTwinFamily m idx A B)
    (l : List ι) (hnodup : l.Nodup) (cfg : m.Configuration) :
    (∀ d : m.Center, d ∈ l.map idx →
      m.configurationSign (h.familyAut l • cfg) d = -m.configurationSign cfg d) ∧
    (∀ d : m.Center, d ∉ l.map idx →
      m.configurationSign (h.familyAut l • cfg) d = m.configurationSign cfg d) := by
  refine ⟨?_, ?_⟩
  · intro d hd
    rw [configurationSign_familyAut_apply h l hnodup cfg d,
      familyCorrection_eq_neg_one_of_mem h l hnodup d hd]
    ring
  · intro d hd
    exact configurationSign_familyAut_apply_of_not_mem h l hnodup cfg d hd

/-- If every distinguished center of the molecule carries a terminal twin pair, then the mirror
configuration's *sign pattern* is reached by an actual automorphism (sign-pattern equality under a
graph automorphism, not literal configuration equality).  The absence of a stereogenic descriptor
is therefore a physical frame gauge, not missing chemistry. -/
theorem familyAut_achiralConfigurationBySymmetry (h : TerminalTwinFamily m idx A B)
    (l : List ι) (hnodup : l.Nodup) (hcover : ∀ d : m.Center, d ∈ l.map idx)
    (cfg : m.Configuration) : m.AchiralConfigurationBySymmetry cfg := by
  refine ⟨h.familyAut l, ?_⟩
  funext d
  rw [configurationSign_familyAut_apply h l hnodup cfg d,
    familyCorrection_eq_neg_one_of_mem h l hnodup d (hcover d)]
  rw [m.configurationSign_mirrorConfiguration]
  ring

end Complete

/-! ### Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinFamily
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.adj_ca
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.adj_cb
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.bond_pos_left
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.bond_pos_right
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.bond_eq_positive
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.not_mem_centers_of_terminal
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.leaf_not_mem_centers_a
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.leaf_not_mem_centers_b
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.leaf_ne_center_a
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.leaf_ne_center_b
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.leaf_ne_of_center_ne
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.bond_eq_zero_of_neighborFinset_singleton
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.bond_b_eq_bond_a_of_ne
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.bond_a_eq_bond_b_of_ne
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.bond_u_b_eq_bond_u_a_of_ne
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.bond_u_a_eq_bond_u_b_of_ne
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.swap_apply_bond
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.swap_mem_molAut
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.swap_preservesCenters
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.swap_mem_aut
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.swapAut
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.swapAut_coe
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.centerPerm_swapAut_apply
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.centerPerm_swapAut
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.ligandAtomAt_ne_terminal_left
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.ligandAtomAt_ne_terminal_right
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.ligandPermAt_swapAut_of_ne
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.twinSlotA
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.twinSlotB
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.twinSlotA_spec
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.twinSlotB_spec
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.twinSlotA_ne_twinSlotB
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.permHandedness_swap_of_ne
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.ligandPermAt_swapAut_center
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.permHandedness_ligandPermAt_swapAut_center
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.configurationSign_swapAut_apply
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinPair.terminalTwin_gauge
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinFamily.twin_atoms_ne
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinFamily.ligandPermAt_other_swapAut
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinFamily.familyAut
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinFamily.centerPerm_familyAut_apply
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinFamily.ligandPermAt_familyAut_of_not_mem
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.TerminalTwinFamily.ligandPermAt_familyAut_at_index
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.configurationSign_familyAut_apply
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.familyCorrection_eq_neg_one_of_mem
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.familyCorrection_eq_one_of_not_mem
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.configurationSign_familyAut_apply_subset
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.configurationSign_familyAut_apply_at_index
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.configurationSign_familyAut_apply_of_not_mem
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.configurationSign_familyAut_subset
assert_kernel_only TetraStereo.OneCenter.TerminalTwinConfigurationGauge.familyAut_achiralConfigurationBySymmetry

end

end TerminalTwinConfigurationGauge
end OneCenter
end TetraStereo
