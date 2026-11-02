import TetraStereo.OneCenter.LocalizedRetainedCoherentSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Boundary component reconstruction from a full residual observation tree

`ResidualPathTreeEquiv e` is a two-sided equivalence of every self-avoiding residual walk from `v`
after deleting the ordered boundary `Bs` with every such walk from `w` after deleting `Bt`. It
preserves terminal labels, the bond to every indexed boundary vertex, every non-parent ancestor
bond and the immediate parent bond.

`exists_witnessedBoundaryComponentIso` constructs from `e` alone a boundary-preserving
isomorphism of the two residual components. It also gives one witness per source vertex: an
actual residual path to that vertex whose `e`-image is its pointwise image under the one
isomorphism. Other paths need not descend.

The proof inducts on the sum of the two component cardinalities. Deleting the entry splits its
component into the touched child components. Each child restriction of `e` is a strictly smaller
instance. Its isomorphism preserves the number of entries attached to the deleted vertex. The
normalized-entry Hall matching then pairs whole child components, each pair through one actual
matched entry. The isomorphism of that entry is glued. Its witnesses, prefixed by the deleted
entry, are witnesses for `e`.

`exists_sameBoundary_automorphism` and `root_outward_arm_automorphism` turn the component
isomorphism into a molecular automorphism. It fixes the boundary and sends `a` to `b`. On a common
component it is the isomorphism. On two different components it is the isomorphism and its
inverse. It is the identity elsewhere.

The only hypothesis is `v ∉ Bs`. Acyclicity, simple bonding, boundary `Nodup`, endpoint
consistency, descent of `e`, equal component cardinality and a desired isomorphism are not used.
The automorphisms are not claimed to preserve configuration or parity.
-/

namespace TetraStereo.OneCenter.BoundaryComponentReconstruction

noncomputable section

open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Residual components -/

lemma comp_eq_of_inComponent {m : MoleculeGraph V} {B : List V} {x y : V}
    (h : InComponent m B x y) :
    (residualGraph m B).connectedComponentMk y = (residualGraph m B).connectedComponentMk x :=
  (SimpleGraph.ConnectedComponent.eq.mpr h.2).symm

lemma inComponent_of_comp_eq {m : MoleculeGraph V} {B : List V} {x y : V} (hx : x ∉ B)
    (h : (residualGraph m B).connectedComponentMk y =
      (residualGraph m B).connectedComponentMk x) :
    InComponent m B x y :=
  ⟨hx, (SimpleGraph.ConnectedComponent.eq.mp h).symm⟩

lemma inComponent_of_bond_pos {m : MoleculeGraph V} {B : List V} {c x y : V}
    (hx : InComponent m B c x) (hy : y ∉ B) (hpos : 0 < m.bond x y) :
    InComponent m B c y := by
  have hadj : (residualGraph m B).Adj x y := ⟨inComponent_not_mem m hx, hy, hpos⟩
  exact ⟨hx.1, hx.2.trans hadj.reachable⟩

lemma bond_eq_zero_of_not_inComponent {m : MoleculeGraph V} {B : List V} {c x y : V}
    (hx : InComponent m B c x) (hy : y ∉ B) (hnot : ¬ InComponent m B c y) :
    m.bond x y = 0 := by
  by_contra hne
  exact hnot (inComponent_of_bond_pos hx hy (Nat.pos_of_ne_zero hne))

lemma reachable_of_bondedChain {m : MoleculeGraph V} {B : List V} :
    ∀ (a : V) (rest : List V), BondedChain m (a :: rest) → (∀ x ∈ a :: rest, x ∉ B) →
      ∀ u ∈ a :: rest, (residualGraph m B).Reachable a u
  | a, [], _, _, u, hu => by
      have hua : u = a := by simpa using hu
      subst hua
      exact SimpleGraph.Reachable.refl _
  | a, b :: rest, hchain, hout, u, hu => by
      have hab : 0 < m.bond a b ∧ BondedChain m (b :: rest) := by
        simpa [BondedChain] using hchain
      have hadj : (residualGraph m B).Adj a b := ⟨hout a (by simp), hout b (by simp), hab.1⟩
      rcases List.mem_cons.mp hu with hua | hu
      · subst hua
        exact SimpleGraph.Reachable.refl _
      · exact hadj.reachable.trans (reachable_of_bondedChain b rest hab.2
          (fun x hx => hout x (List.mem_cons_of_mem a hx)) u hu)

/-- Every vertex of a residual observation path lies in the residual component of its head. -/
lemma obsPath_mem_inComponent {m : MoleculeGraph V} {B : List V} {entry : V} {p : List V}
    (hp : ResidualObsPath m B entry p) {u : V} (hu : u ∈ p) : InComponent m B entry u := by
  cases p with
  | nil => exact absurd rfl hp.nonempty
  | cons a rest =>
      have ha : a = entry := by simpa using hp.head
      subst ha
      exact ⟨hp.outside a (by simp), reachable_of_bondedChain a rest hp.chain hp.outside u hu⟩

/-! ## The entry observation -/

lemma pathTerminal_eq_of_eq_singleton {l : List V} (hl : l ≠ []) {x : V} (h : l = [x]) :
    pathTerminal l hl = x := by
  subst h
  rfl

lemma entry_singleton_terminal {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) :
    pathTerminal (e.toEquiv ⟨[v], obs_singleton m hv⟩).1
        (e.toEquiv ⟨[v], obs_singleton m hv⟩).2.nonempty = w :=
  pathTerminal_eq_of_eq_singleton _ (singleton_image e hv)

lemma entry_atomZ_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) : m.atomZ w = m.atomZ v := by
  have h := e.atomZ_eq ⟨[v], obs_singleton m hv⟩
  rw [entry_singleton_terminal e hv] at h
  exact h

lemma entry_atomMass_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) : m.atomMass w = m.atomMass v := by
  have h := e.atomMass_eq ⟨[v], obs_singleton m hv⟩
  rw [entry_singleton_terminal e hv] at h
  exact h

lemma entry_formalCharge_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) :
    m.formalCharge w = m.formalCharge v := by
  have h := e.formalCharge_eq ⟨[v], obs_singleton m hv⟩
  rw [entry_singleton_terminal e hv] at h
  exact h

lemma entry_boundary_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) (i : Nat) (hi : i < Bs.length) :
    m.bond w (Bt.get ⟨i, e.len_eq ▸ hi⟩) = m.bond v (Bs.get ⟨i, hi⟩) := by
  have h := e.boundaryBond_eq ⟨[v], obs_singleton m hv⟩ i hi
  rw [entry_singleton_terminal e hv] at h
  exact h

/-! ## Child component isomorphisms at the deleted entry -/

/-- The last boundary slot of a child isomorphism carries the bond to the deleted entry. -/
lemma childIso_last_bond {m : MoleculeGraph V} {Bs Bt : List V} {v w x y : V}
    (iso : BoundaryComponentIso m (Bs ++ [v]) (Bt ++ [w]) x y) (hlen : Bs.length = Bt.length)
    {z : V} (hz : InComponent m (Bs ++ [v]) x z) :
    m.bond (iso.toFun z) w = m.bond z v := by
  have hb := iso.boundary_eq z hz Bs.length (by simp)
  have hidx : (⟨Bs.length, by rw [← iso.len_eq]; simp⟩ : Fin (Bt ++ [w]).length) =
      ⟨Bt.length, by simp⟩ := Fin.ext hlen
  rw [hidx, get_append_last, get_append_last] at hb
  exact hb

/-- The earlier boundary slots of a child isomorphism are the ancestor boundary slots. -/
lemma childIso_boundary_bond {m : MoleculeGraph V} {Bs Bt : List V} {v w x y : V}
    (iso : BoundaryComponentIso m (Bs ++ [v]) (Bt ++ [w]) x y) (hlen : Bs.length = Bt.length)
    {z : V} (hz : InComponent m (Bs ++ [v]) x z) (i : Nat) (hi : i < Bs.length) :
    m.bond (iso.toFun z) (Bt.get ⟨i, hlen ▸ hi⟩) = m.bond z (Bs.get ⟨i, hi⟩) := by
  have hb := iso.boundary_eq z hz i (by simp; omega)
  rw [get_append_left Bt w i (hlen ▸ hi), get_append_left Bs v i hi] at hb
  exact hb

/-! ## Gluing matched child components -/

/-- Child components touched by the deleted entry. -/
abbrev Touched (m : MoleculeGraph V) (B : List V) (v : V) :=
  {c : (residualGraph m (B ++ [v])).ConnectedComponent // c ∈ touchedComponents m B v}

/-- Neighbours of the deleted entry outside the boundary. -/
abbrev Entries (m : MoleculeGraph V) (B : List V) (v : V) := {x : V // m.Adj v x ∧ x ∉ B}

/-- A bijection of touched child components, one entry in each matched pair, and a
boundary-preserving isomorphism of the two pointed child components. -/
structure ChildGlueData (m : MoleculeGraph V) (Bs Bt : List V) (v w : V) where
  pair : Touched m Bs v ≃ Touched m Bt w
  src : Touched m Bs v → V
  tgt : Touched m Bs v → V
  src_entry : ∀ a, m.Adj v (src a) ∧ src a ∉ Bs
  tgt_entry : ∀ a, m.Adj w (tgt a) ∧ tgt a ∉ Bt
  src_comp : ∀ a, (residualGraph m (Bs ++ [v])).connectedComponentMk (src a) = a.1
  tgt_comp : ∀ a, (residualGraph m (Bt ++ [w])).connectedComponentMk (tgt a) = (pair a).1
  iso : ∀ a, BoundaryComponentIso m (Bs ++ [v]) (Bt ++ [w]) (src a) (tgt a)

namespace ChildGlueData

variable {m : MoleculeGraph V} {Bs Bt : List V} {v w : V} (D : ChildGlueData m Bs Bt v w)

/-- The glued map: the matched child isomorphism on each touched child component, the entry to
the target entry, and the identity elsewhere. -/
def toFun (y : V) : V :=
  if h : y ∉ Bs ++ [v] ∧
      (residualGraph m (Bs ++ [v])).connectedComponentMk y ∈ touchedComponents m Bs v then
    (D.iso ⟨_, h.2⟩).toFun y
  else if y = v then w else y

/-- The glued inverse. -/
def invFun (z : V) : V :=
  if h : z ∉ Bt ++ [w] ∧
      (residualGraph m (Bt ++ [w])).connectedComponentMk z ∈ touchedComponents m Bt w then
    (D.iso (D.pair.symm ⟨_, h.2⟩)).invFun z
  else if z = w then v else z

lemma src_out (a : Touched m Bs v) : D.src a ∉ Bs ++ [v] := by
  rw [not_mem_append_singleton]
  exact ⟨(D.src_entry a).2, (ne_of_adj m (D.src_entry a).1).symm⟩

lemma tgt_out (a : Touched m Bs v) : D.tgt a ∉ Bt ++ [w] := by
  rw [not_mem_append_singleton]
  exact ⟨(D.tgt_entry a).2, (ne_of_adj m (D.tgt_entry a).1).symm⟩

lemma src_child (hv : v ∉ Bs) {a : Touched m Bs v} {y : V}
    (hy : InComponent m (Bs ++ [v]) (D.src a) y) : InComponent m Bs v y ∧ y ≠ v :=
  child_subset_erase hv ⟨hv, (D.src_entry a).2, (D.src_entry a).1⟩ hy

lemma tgt_child (hw : w ∉ Bt) {a : Touched m Bs v} {z : V}
    (hz : InComponent m (Bt ++ [w]) (D.tgt a) z) : InComponent m Bt w z ∧ z ≠ w :=
  child_subset_erase hw ⟨hw, (D.tgt_entry a).2, (D.tgt_entry a).1⟩ hz

lemma src_owner_unique {a b : Touched m Bs v} {y : V}
    (ha : InComponent m (Bs ++ [v]) (D.src a) y)
    (hb : InComponent m (Bs ++ [v]) (D.src b) y) : a = b :=
  Subtype.ext ((D.src_comp a).symm.trans ((comp_eq_of_inComponent ha).symm.trans
    ((comp_eq_of_inComponent hb).trans (D.src_comp b))))

lemma tgt_owner_unique {a b : Touched m Bs v} {z : V}
    (ha : InComponent m (Bt ++ [w]) (D.tgt a) z)
    (hb : InComponent m (Bt ++ [w]) (D.tgt b) z) : a = b :=
  D.pair.injective (Subtype.ext ((D.tgt_comp a).symm.trans ((comp_eq_of_inComponent ha).symm.trans
    ((comp_eq_of_inComponent hb).trans (D.tgt_comp b)))))

lemma toFun_eq_child (a : Touched m Bs v) {y : V}
    (hy : InComponent m (Bs ++ [v]) (D.src a) y) :
    D.toFun y = (D.iso a).toFun y := by
  have hcomp : (residualGraph m (Bs ++ [v])).connectedComponentMk y = a.1 :=
    (comp_eq_of_inComponent hy).trans (D.src_comp a)
  have hcond : y ∉ Bs ++ [v] ∧
      (residualGraph m (Bs ++ [v])).connectedComponentMk y ∈ touchedComponents m Bs v :=
    ⟨inComponent_not_mem m hy, by rw [hcomp]; exact a.2⟩
  have howner : (⟨_, hcond.2⟩ : Touched m Bs v) = a := Subtype.ext hcomp
  unfold ChildGlueData.toFun
  rw [dif_pos hcond]
  exact congrArg (fun t => (D.iso t).toFun y) howner

lemma invFun_eq_child (a : Touched m Bs v) {z : V}
    (hz : InComponent m (Bt ++ [w]) (D.tgt a) z) :
    D.invFun z = (D.iso a).invFun z := by
  have hcomp : (residualGraph m (Bt ++ [w])).connectedComponentMk z = (D.pair a).1 :=
    (comp_eq_of_inComponent hz).trans (D.tgt_comp a)
  have hcond : z ∉ Bt ++ [w] ∧
      (residualGraph m (Bt ++ [w])).connectedComponentMk z ∈ touchedComponents m Bt w :=
    ⟨inComponent_not_mem m hz, by rw [hcomp]; exact (D.pair a).2⟩
  have howner : D.pair.symm (⟨_, hcond.2⟩ : Touched m Bt w) = a := by
    rw [show (⟨_, hcond.2⟩ : Touched m Bt w) = D.pair a from Subtype.ext hcomp]
    exact D.pair.symm_apply_apply a
  unfold ChildGlueData.invFun
  rw [dif_pos hcond]
  exact congrArg (fun t => (D.iso t).invFun z) howner

lemma toFun_entry : D.toFun v = w := by
  unfold ChildGlueData.toFun
  rw [dif_neg (fun h => h.1 (by simp)), if_pos rfl]

lemma invFun_entry : D.invFun w = v := by
  unfold ChildGlueData.invFun
  rw [dif_neg (fun h => h.1 (by simp)), if_pos rfl]

/-- Every non-entry vertex of the source component lies in a touched child component. -/
lemma exists_src_owner (hv : v ∉ Bs) {x : V} (hx : InComponent m Bs v x) (hxv : x ≠ v) :
    ∃ a : Touched m Bs v, InComponent m (Bs ++ [v]) (D.src a) x := by
  obtain ⟨y0, hy0, hxy⟩ := exists_child_bridge hv hx hxv
  have hmem : (residualGraph m (Bs ++ [v])).connectedComponentMk y0 ∈
      touchedComponents m Bs v :=
    Finset.mem_image_of_mem _ ((neighborOutside_mem m Bs v y0).2 ⟨hy0.2.2, hy0.2.1⟩)
  refine ⟨⟨_, hmem⟩, inComponent_of_comp_eq (D.src_out _) ?_⟩
  exact (comp_eq_of_inComponent hxy).trans (D.src_comp ⟨_, hmem⟩).symm

/-- Every non-entry vertex of the target component lies in a matched child component. -/
lemma exists_tgt_owner (hw : w ∉ Bt) {z : V} (hz : InComponent m Bt w z) (hzw : z ≠ w) :
    ∃ a : Touched m Bs v, InComponent m (Bt ++ [w]) (D.tgt a) z := by
  obtain ⟨y0, hy0, hzy⟩ := exists_child_bridge hw hz hzw
  have hmem : (residualGraph m (Bt ++ [w])).connectedComponentMk y0 ∈
      touchedComponents m Bt w :=
    Finset.mem_image_of_mem _ ((neighborOutside_mem m Bt w y0).2 ⟨hy0.2.2, hy0.2.1⟩)
  refine ⟨D.pair.symm ⟨_, hmem⟩, inComponent_of_comp_eq (D.tgt_out _) ?_⟩
  rw [D.tgt_comp, D.pair.apply_symm_apply]
  exact comp_eq_of_inComponent hzy

lemma glue_left_inv (hv : v ∉ Bs) {x : V} (hx : InComponent m Bs v x) :
    D.invFun (D.toFun x) = x := by
  by_cases hxv : x = v
  · rw [hxv, D.toFun_entry, D.invFun_entry]
  · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
    rw [D.toFun_eq_child a ha, D.invFun_eq_child a ((D.iso a).maps_to x ha)]
    exact (D.iso a).left_inv x ha

lemma glue_right_inv (hw : w ∉ Bt) {z : V} (hz : InComponent m Bt w z) :
    D.toFun (D.invFun z) = z := by
  by_cases hzw : z = w
  · rw [hzw, D.invFun_entry, D.toFun_entry]
  · obtain ⟨a, ha⟩ := D.exists_tgt_owner hw hz hzw
    rw [D.invFun_eq_child a ha, D.toFun_eq_child a ((D.iso a).maps_inv z ha)]
    exact (D.iso a).right_inv z ha

lemma glue_maps_to (hv : v ∉ Bs) (hw : w ∉ Bt) {x : V} (hx : InComponent m Bs v x) :
    InComponent m Bt w (D.toFun x) := by
  by_cases hxv : x = v
  · rw [hxv, D.toFun_entry]
    exact inComponent_self m hw
  · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
    rw [D.toFun_eq_child a ha]
    exact (D.tgt_child hw ((D.iso a).maps_to x ha)).1

lemma glue_maps_inv (hv : v ∉ Bs) (hw : w ∉ Bt) {z : V} (hz : InComponent m Bt w z) :
    InComponent m Bs v (D.invFun z) := by
  by_cases hzw : z = w
  · rw [hzw, D.invFun_entry]
    exact inComponent_self m hv
  · obtain ⟨a, ha⟩ := D.exists_tgt_owner hw hz hzw
    rw [D.invFun_eq_child a ha]
    exact (D.src_child hv ((D.iso a).maps_inv z ha)).1

lemma glue_atomZ (hv : v ∉ Bs) (hZ : m.atomZ w = m.atomZ v) {x : V}
    (hx : InComponent m Bs v x) : m.atomZ (D.toFun x) = m.atomZ x := by
  by_cases hxv : x = v
  · rw [hxv, D.toFun_entry]
    exact hZ
  · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
    rw [D.toFun_eq_child a ha]
    exact (D.iso a).atomZ_eq x ha

lemma glue_atomMass (hv : v ∉ Bs) (hMass : m.atomMass w = m.atomMass v) {x : V}
    (hx : InComponent m Bs v x) : m.atomMass (D.toFun x) = m.atomMass x := by
  by_cases hxv : x = v
  · rw [hxv, D.toFun_entry]
    exact hMass
  · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
    rw [D.toFun_eq_child a ha]
    exact (D.iso a).atomMass_eq x ha

lemma glue_formalCharge (hv : v ∉ Bs) (hCharge : m.formalCharge w = m.formalCharge v) {x : V}
    (hx : InComponent m Bs v x) : m.formalCharge (D.toFun x) = m.formalCharge x := by
  by_cases hxv : x = v
  · rw [hxv, D.toFun_entry]
    exact hCharge
  · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
    rw [D.toFun_eq_child a ha]
    exact (D.iso a).formalCharge_eq x ha

/-- Bonds inside one child, to the entry, and between two different children are preserved;
the last two are zero on both sides. -/
lemma glue_bond (hv : v ∉ Bs) (hlen : Bs.length = Bt.length) {x y : V}
    (hx : InComponent m Bs v x) (hy : InComponent m Bs v y) :
    m.bond (D.toFun x) (D.toFun y) = m.bond x y := by
  by_cases hxv : x = v
  · by_cases hyv : y = v
    · rw [hxv, hyv, D.toFun_entry, m.bond_self, m.bond_self]
    · obtain ⟨b, hb⟩ := D.exists_src_owner hv hy hyv
      rw [hxv, D.toFun_entry, D.toFun_eq_child b hb, m.bond_symm w,
        childIso_last_bond (D.iso b) hlen hb, m.bond_symm]
  · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
    by_cases hyv : y = v
    · rw [hyv, D.toFun_entry, D.toFun_eq_child a ha, childIso_last_bond (D.iso a) hlen ha]
    · obtain ⟨b, hb⟩ := D.exists_src_owner hv hy hyv
      rw [D.toFun_eq_child a ha, D.toFun_eq_child b hb]
      by_cases hab : a = b
      · subst hab
        exact (D.iso a).bond_eq x y ha hb
      · have hx' := (D.iso a).maps_to x ha
        have hy' := (D.iso b).maps_to y hb
        rw [bond_eq_zero_of_not_inComponent ha (inComponent_not_mem m hb)
            (fun h => hab (D.src_owner_unique h hb)),
          bond_eq_zero_of_not_inComponent hx' (inComponent_not_mem m hy')
            (fun h => hab (D.tgt_owner_unique h hy'))]

lemma glue_boundary (hv : v ∉ Bs) (hlen : Bs.length = Bt.length)
    (hBoundary : ∀ i (hi : i < Bs.length),
      m.bond w (Bt.get ⟨i, hlen ▸ hi⟩) = m.bond v (Bs.get ⟨i, hi⟩))
    {x : V} (hx : InComponent m Bs v x) (i : Nat) (hi : i < Bs.length) :
    m.bond (D.toFun x) (Bt.get ⟨i, hlen ▸ hi⟩) = m.bond x (Bs.get ⟨i, hi⟩) := by
  by_cases hxv : x = v
  · rw [hxv, D.toFun_entry]
    exact hBoundary i hi
  · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
    rw [D.toFun_eq_child a ha]
    exact childIso_boundary_bond (D.iso a) hlen ha i hi

/-- The glued boundary-preserving component isomorphism. The entry data are the singleton
observations of the parent equivalence. -/
def glue (hv : v ∉ Bs) (hw : w ∉ Bt) (hlen : Bs.length = Bt.length)
    (hZ : m.atomZ w = m.atomZ v) (hMass : m.atomMass w = m.atomMass v)
    (hCharge : m.formalCharge w = m.formalCharge v)
    (hBoundary : ∀ i (hi : i < Bs.length),
      m.bond w (Bt.get ⟨i, hlen ▸ hi⟩) = m.bond v (Bs.get ⟨i, hi⟩)) :
    BoundaryComponentIso m Bs Bt v w where
  len_eq := hlen
  toFun := D.toFun
  invFun := D.invFun
  left_inv := fun x hx => D.glue_left_inv hv hx
  right_inv := fun z hz => D.glue_right_inv hw hz
  maps_to := fun x hx => D.glue_maps_to hv hw hx
  maps_inv := fun z hz => D.glue_maps_inv hv hw hz
  entry := D.toFun_entry
  inv_entry := D.invFun_entry
  atomZ_eq := fun x hx => D.glue_atomZ hv hZ hx
  atomMass_eq := fun x hx => D.glue_atomMass hv hMass hx
  formalCharge_eq := fun x hx => D.glue_formalCharge hv hCharge hx
  bond_eq := fun x y hx hy => D.glue_bond hv hlen hx hy
  boundary_eq := fun x hx i hi => D.glue_boundary hv hlen hBoundary hx i hi

end ChildGlueData

/-! ## Entry owners and the component matching -/

lemma comp_mem_touched (m : MoleculeGraph V) (B : List V) (v : V) (x : Entries m B v) :
    (residualGraph m (B ++ [v])).connectedComponentMk x.1 ∈ touchedComponents m B v :=
  Finset.mem_image_of_mem _ ((neighborOutside_mem m B v x.1).2 x.2)

/-- The touched child component of an entry. -/
def entryOwner (m : MoleculeGraph V) (B : List V) (v : V) (x : Entries m B v) :
    Touched m B v :=
  ⟨_, comp_mem_touched m B v x⟩

lemma entryOwner_fiber_pos (m : MoleculeGraph V) (B : List V) (v : V) (a : Touched m B v) :
    0 < (Finset.univ.filter fun x : Entries m B v => entryOwner m B v x = a).card := by
  obtain ⟨c, hc⟩ := a
  have hc' : c ∈ (neighborOutside m B v).image fun x =>
      (residualGraph m (B ++ [v])).connectedComponentMk x := hc
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hc'
  apply Finset.card_pos.mpr
  refine ⟨⟨x0, (neighborOutside_mem m B v x0).1 hx0⟩, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- A child isomorphism at one entry pair gives equal owner fibers. -/
lemma entryOwner_fiber_card_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (x : Entries m Bs v) (y : Entries m Bt w)
    (iso : BoundaryComponentIso m (Bs ++ [v]) (Bt ++ [w]) x.1 y.1) :
    (Finset.univ.filter fun z => entryOwner m Bs v z = entryOwner m Bs v x).card =
      (Finset.univ.filter fun z => entryOwner m Bt w z = entryOwner m Bt w y).card := by
  let source : {z : Entries m Bs v // entryOwner m Bs v z = entryOwner m Bs v x} ≃
      {z : Entries m Bs v // (residualGraph m (Bs ++ [v])).connectedComponentMk z.1 =
        (residualGraph m (Bs ++ [v])).connectedComponentMk x.1} :=
    Equiv.subtypeEquivRight fun z => Subtype.ext_iff
  let target : {z : Entries m Bt w // (residualGraph m (Bt ++ [w])).connectedComponentMk z.1 =
        (residualGraph m (Bt ++ [w])).connectedComponentMk y.1} ≃
      {z : Entries m Bt w // entryOwner m Bt w z = entryOwner m Bt w y} :=
    Equiv.subtypeEquivRight fun z => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  exact owner_fiber_card_eq_of_equiv (entryOwner m Bs v) (entryOwner m Bt w) x y
    (source.trans ((componentOwnerFiberEquiv iso x.2).trans target))

/-! ## The reconstruction induction -/

/-- Bounded form of the reconstruction, by induction on a bound for the sum of the two
component cardinalities. -/
theorem exists_witnessedBoundaryComponentIso_le (m : MoleculeGraph V) (n : Nat) :
    ∀ {Bs Bt : List V} {v w : V} (e : ResidualPathTreeEquiv m Bs Bt v w), v ∉ Bs →
      compCard m Bs v + compCard m Bt w ≤ n → Nonempty (WitnessedBoundaryComponentIso e) := by
  induction n with
  | zero =>
      intro Bs Bt v w e hv hn
      have := compCard_pos m hv
      omega
  | succ n ih =>
      intro Bs Bt v w e hv hn
      have hw : w ∉ Bt := target_root_outside e hv
      have hcs := compCard_pos m hv
      have hct := compCard_pos m hw
      have hchild : ∀ x : Entries m Bs v,
          Nonempty (WitnessedBoundaryComponentIso (childResidualPathTreeEquiv e hv x.2)) := by
        intro x
        have hy := childOf_adj e hv x.2
        have h1 := compCard_child_le m hv
          (show (residualGraph m Bs).Adj v x.1 from ⟨hv, x.2.2, x.2.1⟩)
        have h2 := compCard_child_le m hw
          (show (residualGraph m Bt).Adj w (childOf e hv x.1) from ⟨hw, hy.2, hy.1⟩)
        exact ih (childResidualPathTreeEquiv e hv x.2)
          (by
            rw [not_mem_append_singleton]
            exact ⟨x.2.2, (ne_of_adj m x.2.1).symm⟩)
          (by omega)
      let W : ∀ x : Entries m Bs v,
          WitnessedBoundaryComponentIso (childResidualPathTreeEquiv e hv x.2) :=
        fun x => Classical.choice (hchild x)
      obtain ⟨f, hf⟩ := exists_component_bijection_of_entryEquiv
        (entryOwner m Bs v) (entryOwner m Bt w) (childEntryEquiv e hv)
        (entryOwner_fiber_pos m Bs v) (entryOwner_fiber_pos m Bt w)
        (fun x => entryOwner_fiber_card_eq x (childEntryEquiv e hv x) (W x).iso)
      choose wit hwitE hwitF using hf
      let D : ChildGlueData m Bs Bt v w :=
        { pair := f
          src := fun a => (wit a).1
          tgt := fun a => childOf e hv (wit a).1
          src_entry := fun a => (wit a).2
          tgt_entry := fun a => childOf_adj e hv (wit a).2
          src_comp := fun a => congrArg Subtype.val (hwitE a)
          tgt_comp := fun a => congrArg Subtype.val (hwitF a)
          iso := fun a => (W (wit a)).iso }
      refine ⟨⟨D.glue hv hw e.len_eq (entry_atomZ_eq e hv) (entry_atomMass_eq e hv)
        (entry_formalCharge_eq e hv) (entry_boundary_eq e hv), ?_⟩⟩
      intro x hx
      by_cases hxv : x = v
      · refine ⟨⟨[v], obs_singleton m hv⟩, (pathTerminal_singleton v).trans hxv.symm, ?_⟩
        show (e.toEquiv ⟨[v], obs_singleton m hv⟩).1 = [v].map D.toFun
        rw [singleton_image e hv, List.map_cons, List.map_nil, D.toFun_entry]
      · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
        obtain ⟨q, hqterm, hqimg⟩ := (W (wit a)).witnessPath x ha
        refine ⟨⟨v :: q.1, obs_cons_child m hv (wit a).2.1 (wit a).2.2 q.2⟩,
          (pathTerminal_cons_ne v q.1 q.2.nonempty).trans hqterm, ?_⟩
        show (e.toEquiv ⟨v :: q.1, obs_cons_child m hv (wit a).2.1 (wit a).2.2 q.2⟩).1 =
          (v :: q.1).map D.toFun
        rw [childPathMap_parent_image e hv (wit a).2 q, List.map_cons, D.toFun_entry]
        congr 1
        change (childPathMap e hv (wit a).2 q).1 = q.1.map (W (wit a)).iso.toFun at hqimg
        rw [hqimg]
        apply List.map_congr_left
        intro u hu
        exact (D.toFun_eq_child a (obsPath_mem_inComponent q.2 hu)).symm

/-- **Witnessed boundary component reconstruction.** A full residual observation-tree
equivalence `e` yields a boundary-preserving isomorphism of the two residual components. Each
source vertex is the terminal of an actual residual path whose `e`-image is its pointwise image
under that one isomorphism. -/
theorem exists_witnessedBoundaryComponentIso {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) :
    Nonempty (WitnessedBoundaryComponentIso e) :=
  exists_witnessedBoundaryComponentIso_le m _ e hv le_rfl

/-- A chosen witnessed reconstruction. -/
def witnessedBoundaryComponentIso {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) :
    WitnessedBoundaryComponentIso e :=
  Classical.choice (exists_witnessedBoundaryComponentIso e hv)

/-- The ordinary boundary-preserving component isomorphism. -/
theorem boundaryComponentIso_of_pathTreeEquiv {m : MoleculeGraph V} {Bs Bt : List V}
    {v w : V} (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) :
    Nonempty (BoundaryComponentIso m Bs Bt v w) :=
  ⟨(witnessedBoundaryComponentIso e hv).iso⟩

/-! ## Molecular automorphism at a common boundary -/

section Automorphism

variable {m : MoleculeGraph V} {Bs Bt B : List V} {v w a b : V}

lemma iso_inv_atomZ (iso : BoundaryComponentIso m Bs Bt v w) {z : V}
    (hz : InComponent m Bt w z) : m.atomZ (iso.invFun z) = m.atomZ z := by
  have h := iso.atomZ_eq _ (iso.maps_inv z hz)
  rw [iso.right_inv z hz] at h
  exact h.symm

lemma iso_inv_atomMass (iso : BoundaryComponentIso m Bs Bt v w) {z : V}
    (hz : InComponent m Bt w z) : m.atomMass (iso.invFun z) = m.atomMass z := by
  have h := iso.atomMass_eq _ (iso.maps_inv z hz)
  rw [iso.right_inv z hz] at h
  exact h.symm

lemma iso_inv_formalCharge (iso : BoundaryComponentIso m Bs Bt v w) {z : V}
    (hz : InComponent m Bt w z) : m.formalCharge (iso.invFun z) = m.formalCharge z := by
  have h := iso.formalCharge_eq _ (iso.maps_inv z hz)
  rw [iso.right_inv z hz] at h
  exact h.symm

lemma iso_inv_bond (iso : BoundaryComponentIso m Bs Bt v w) {x y : V}
    (hx : InComponent m Bt w x) (hy : InComponent m Bt w y) :
    m.bond (iso.invFun x) (iso.invFun y) = m.bond x y := by
  have h := iso.bond_eq _ _ (iso.maps_inv x hx) (iso.maps_inv y hy)
  rw [iso.right_inv x hx, iso.right_inv y hy] at h
  exact h.symm

lemma iso_bond_mem_boundary (iso : BoundaryComponentIso m B B a b) {x z : V}
    (hx : InComponent m B a x) (hz : z ∈ B) :
    m.bond (iso.toFun x) z = m.bond x z := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hz
  subst hi
  exact iso.boundary_eq x hx i.1 i.2

lemma iso_inv_bond_mem_boundary (iso : BoundaryComponentIso m B B a b) {y z : V}
    (hy : InComponent m B b y) (hz : z ∈ B) :
    m.bond (iso.invFun y) z = m.bond y z := by
  have h := iso_bond_mem_boundary iso (iso.maps_inv y hy) hz
  rw [iso.right_inv y hy] at h
  exact h.symm

/-- On one common boundary, two residual components either coincide or are disjoint. -/
lemma inComponent_same_or_disjoint (ha : a ∉ B) (hb : b ∉ B) :
    (∀ x, InComponent m B a x ↔ InComponent m B b x) ∨
      (∀ x, ¬ (InComponent m B a x ∧ InComponent m B b x)) := by
  by_cases hab : InComponent m B a b
  · left
    intro x
    exact ⟨fun hx => ⟨hb, hab.2.symm.trans hx.2⟩, fun hx => ⟨ha, hab.2.trans hx.2⟩⟩
  · right
    rintro x ⟨hxa, hxb⟩
    exact hab ⟨ha, hxa.2.trans hxb.2.symm⟩

/-- The isomorphism on the component of `a`, its inverse on a different component of `b`, and
the identity elsewhere. -/
def componentExchange (iso : BoundaryComponentIso m B B a b) (x : V) : V :=
  if InComponent m B a x then iso.toFun x
  else if InComponent m B b x then iso.invFun x else x

/-- The inverse of `componentExchange`. -/
def componentExchangeInv (iso : BoundaryComponentIso m B B a b) (y : V) : V :=
  if InComponent m B b y then iso.invFun y
  else if InComponent m B a y then iso.toFun y else y

lemma exchange_of_a (iso : BoundaryComponentIso m B B a b) {x : V}
    (hx : InComponent m B a x) : componentExchange iso x = iso.toFun x := by
  unfold componentExchange
  rw [if_pos hx]

lemma exchange_of_b (iso : BoundaryComponentIso m B B a b) {x : V}
    (hxa : ¬ InComponent m B a x) (hxb : InComponent m B b x) :
    componentExchange iso x = iso.invFun x := by
  unfold componentExchange
  rw [if_neg hxa, if_pos hxb]

lemma exchange_of_none (iso : BoundaryComponentIso m B B a b) {x : V}
    (hxa : ¬ InComponent m B a x) (hxb : ¬ InComponent m B b x) :
    componentExchange iso x = x := by
  unfold componentExchange
  rw [if_neg hxa, if_neg hxb]

lemma exchangeInv_of_b (iso : BoundaryComponentIso m B B a b) {y : V}
    (hy : InComponent m B b y) : componentExchangeInv iso y = iso.invFun y := by
  unfold componentExchangeInv
  rw [if_pos hy]

lemma exchangeInv_of_a (iso : BoundaryComponentIso m B B a b) {y : V}
    (hyb : ¬ InComponent m B b y) (hya : InComponent m B a y) :
    componentExchangeInv iso y = iso.toFun y := by
  unfold componentExchangeInv
  rw [if_neg hyb, if_pos hya]

lemma exchangeInv_of_none (iso : BoundaryComponentIso m B B a b) {y : V}
    (hyb : ¬ InComponent m B b y) (hya : ¬ InComponent m B a y) :
    componentExchangeInv iso y = y := by
  unfold componentExchangeInv
  rw [if_neg hyb, if_neg hya]

lemma exchange_left_inv (iso : BoundaryComponentIso m B B a b) (ha : a ∉ B) (hb : b ∉ B)
    (x : V) : componentExchangeInv iso (componentExchange iso x) = x := by
  by_cases hxa : InComponent m B a x
  · rw [exchange_of_a iso hxa, exchangeInv_of_b iso (iso.maps_to x hxa)]
    exact iso.left_inv x hxa
  · by_cases hxb : InComponent m B b x
    · have hinv := iso.maps_inv x hxb
      rcases inComponent_same_or_disjoint ha hb with hsame | hdisj
      · exact absurd ((hsame x).2 hxb) hxa
      · rw [exchange_of_b iso hxa hxb,
          exchangeInv_of_a iso (fun h => hdisj _ ⟨hinv, h⟩) hinv]
        exact iso.right_inv x hxb
    · rw [exchange_of_none iso hxa hxb, exchangeInv_of_none iso hxb hxa]

lemma exchange_right_inv (iso : BoundaryComponentIso m B B a b) (ha : a ∉ B) (hb : b ∉ B)
    (y : V) : componentExchange iso (componentExchangeInv iso y) = y := by
  by_cases hyb : InComponent m B b y
  · rw [exchangeInv_of_b iso hyb, exchange_of_a iso (iso.maps_inv y hyb)]
    exact iso.right_inv y hyb
  · by_cases hya : InComponent m B a y
    · have hmap := iso.maps_to y hya
      rcases inComponent_same_or_disjoint ha hb with hsame | hdisj
      · exact absurd ((hsame y).1 hya) hyb
      · rw [exchangeInv_of_a iso hyb hya,
          exchange_of_b iso (fun h => hdisj _ ⟨h, hmap⟩) hmap]
        exact iso.left_inv y hya
    · rw [exchangeInv_of_none iso hyb hya, exchange_of_none iso hya hyb]

/-- The component exchange as a permutation. -/
def componentExchangePerm (iso : BoundaryComponentIso m B B a b) (ha : a ∉ B) (hb : b ∉ B) :
    Equiv.Perm V where
  toFun := componentExchange iso
  invFun := componentExchangeInv iso
  left_inv := exchange_left_inv iso ha hb
  right_inv := exchange_right_inv iso ha hb

lemma componentExchangePerm_apply (iso : BoundaryComponentIso m B B a b) (ha : a ∉ B)
    (hb : b ∉ B) (x : V) : componentExchangePerm iso ha hb x = componentExchange iso x :=
  rfl

lemma exchange_atomZ (iso : BoundaryComponentIso m B B a b) (x : V) :
    m.atomZ (componentExchange iso x) = m.atomZ x := by
  by_cases hxa : InComponent m B a x
  · rw [exchange_of_a iso hxa]
    exact iso.atomZ_eq x hxa
  · by_cases hxb : InComponent m B b x
    · rw [exchange_of_b iso hxa hxb]
      exact iso_inv_atomZ iso hxb
    · rw [exchange_of_none iso hxa hxb]

lemma exchange_atomMass (iso : BoundaryComponentIso m B B a b) (x : V) :
    m.atomMass (componentExchange iso x) = m.atomMass x := by
  by_cases hxa : InComponent m B a x
  · rw [exchange_of_a iso hxa]
    exact iso.atomMass_eq x hxa
  · by_cases hxb : InComponent m B b x
    · rw [exchange_of_b iso hxa hxb]
      exact iso_inv_atomMass iso hxb
    · rw [exchange_of_none iso hxa hxb]

lemma exchange_formalCharge (iso : BoundaryComponentIso m B B a b) (x : V) :
    m.formalCharge (componentExchange iso x) = m.formalCharge x := by
  by_cases hxa : InComponent m B a x
  · rw [exchange_of_a iso hxa]
    exact iso.formalCharge_eq x hxa
  · by_cases hxb : InComponent m B b x
    · rw [exchange_of_b iso hxa hxb]
      exact iso_inv_formalCharge iso hxb
    · rw [exchange_of_none iso hxa hxb]

/-- A vertex of either exchanged component keeps its bond to every other vertex. -/
lemma exchange_bond_of_left (iso : BoundaryComponentIso m B B a b) (ha : a ∉ B) (hb : b ∉ B)
    {u : V} (hu : InComponent m B a u ∨ InComponent m B b u) (y : V) :
    m.bond (componentExchange iso u) (componentExchange iso y) = m.bond u y := by
  by_cases hua : InComponent m B a u
  · have hu' := iso.maps_to u hua
    rw [exchange_of_a iso hua]
    by_cases hya : InComponent m B a y
    · rw [exchange_of_a iso hya]
      exact iso.bond_eq u y hua hya
    · by_cases hyb : InComponent m B b y
      · -- `y` lies only in the second component, so the two components are disjoint.
        have hyinv := iso.maps_inv y hyb
        rcases inComponent_same_or_disjoint ha hb with hsame | hdisj
        · exact absurd ((hsame y).2 hyb) hya
        · rw [exchange_of_b iso hya hyb,
            bond_eq_zero_of_not_inComponent hua (inComponent_not_mem m hyb) hya,
            bond_eq_zero_of_not_inComponent hu' (inComponent_not_mem m hyinv)
              (fun h => hdisj _ ⟨hyinv, h⟩)]
      · rw [exchange_of_none iso hya hyb]
        by_cases hyB : y ∈ B
        · exact iso_bond_mem_boundary iso hua hyB
        · rw [bond_eq_zero_of_not_inComponent hua hyB hya,
            bond_eq_zero_of_not_inComponent hu' hyB hyb]
  · have hub : InComponent m B b u := hu.resolve_left hua
    have hdisj : ∀ x, ¬ (InComponent m B a x ∧ InComponent m B b x) := by
      rcases inComponent_same_or_disjoint ha hb with hsame | hdisj
      · exact absurd ((hsame u).2 hub) hua
      · exact hdisj
    have hu' := iso.maps_inv u hub
    rw [exchange_of_b iso hua hub]
    by_cases hya : InComponent m B a y
    · have hy' := iso.maps_to y hya
      rw [exchange_of_a iso hya,
        bond_eq_zero_of_not_inComponent hub (inComponent_not_mem m hya)
          (fun h => hdisj _ ⟨hya, h⟩),
        bond_eq_zero_of_not_inComponent hu' (inComponent_not_mem m hy')
          (fun h => hdisj _ ⟨h, hy'⟩)]
    · by_cases hyb : InComponent m B b y
      · rw [exchange_of_b iso hya hyb]
        exact iso_inv_bond iso hub hyb
      · rw [exchange_of_none iso hya hyb]
        by_cases hyB : y ∈ B
        · exact iso_inv_bond_mem_boundary iso hub hyB
        · rw [bond_eq_zero_of_not_inComponent hub hyB hyb,
            bond_eq_zero_of_not_inComponent hu' hyB hya]

lemma exchange_bond (iso : BoundaryComponentIso m B B a b) (ha : a ∉ B) (hb : b ∉ B)
    (u y : V) :
    m.bond (componentExchange iso u) (componentExchange iso y) = m.bond u y := by
  by_cases hu : InComponent m B a u ∨ InComponent m B b u
  · exact exchange_bond_of_left iso ha hb hu y
  · by_cases hy : InComponent m B a y ∨ InComponent m B b y
    · rw [m.bond_symm, exchange_bond_of_left iso ha hb hy u, m.bond_symm]
    · rw [exchange_of_none iso (fun h => hu (Or.inl h)) (fun h => hu (Or.inr h)),
        exchange_of_none iso (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h))]

lemma componentExchangePerm_isAutomorphism (iso : BoundaryComponentIso m B B a b)
    (ha : a ∉ B) (hb : b ∉ B) : m.IsAutomorphism (componentExchangePerm iso ha hb) :=
  ⟨exchange_atomZ iso, exchange_atomMass iso, exchange_formalCharge iso,
    exchange_bond iso ha hb⟩

end Automorphism

/-- **Boundary-fixing automorphism.** On one common ordered boundary, a full residual
observation-tree equivalence from `a` to `b` yields a molecular automorphism. It fixes every
boundary vertex, sends `a` to `b` and is the identity outside the two residual components. Each
vertex of the component of `a` is the terminal of an actual residual path whose `e`-image is its
pointwise image under that automorphism. -/
theorem exists_sameBoundary_automorphism {m : MoleculeGraph V} {B : List V} {a b : V}
    (e : ResidualPathTreeEquiv m B B a b) (ha : a ∉ B) :
    ∃ π : Equiv.Perm V, m.IsAutomorphism π ∧ (∀ z ∈ B, π z = z) ∧ π a = b ∧
      (∀ x, ¬ InComponent m B a x → ¬ InComponent m B b x → π x = x) ∧
      ∀ x, InComponent m B a x → ∃ p : {p : List V // ResidualObsPath m B a p},
        pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map π := by
  let W := witnessedBoundaryComponentIso e ha
  have hb : b ∉ B := target_root_outside e ha
  refine ⟨componentExchangePerm W.iso ha hb,
    componentExchangePerm_isAutomorphism W.iso ha hb, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [componentExchangePerm_apply]
    exact exchange_of_none W.iso (fun h => inComponent_not_mem m h hz)
      (fun h => inComponent_not_mem m h hz)
  · rw [componentExchangePerm_apply, exchange_of_a W.iso (inComponent_self m ha)]
    exact W.iso.entry
  · intro x hxa hxb
    rw [componentExchangePerm_apply]
    exact exchange_of_none W.iso hxa hxb
  · intro x hx
    obtain ⟨p, hterm, himg⟩ := W.witnessPath x hx
    refine ⟨p, hterm, ?_⟩
    rw [himg]
    apply List.map_congr_left
    intro u hu
    rw [componentExchangePerm_apply, exchange_of_a W.iso (obsPath_mem_inComponent p.2 hu)]

/-- **Original-root outward-arm automorphism.** For two outward arms `a` and `b` of `root`, a
full residual observation-tree equivalence after deleting `root` yields a molecular
automorphism fixing `root` and sending `a` to `b`. It is the identity outside the two residual
components, and its witness paths cover the component of `a`. -/
theorem root_outward_arm_automorphism {m : MoleculeGraph V} {root a b : V}
    (hra : m.Adj root a) (e : ResidualPathTreeEquiv m [root] [root] a b) :
    ∃ π : Equiv.Perm V, m.IsAutomorphism π ∧ π root = root ∧ π a = b ∧
      (∀ x, ¬ InComponent m [root] a x → ¬ InComponent m [root] b x → π x = x) ∧
      ∀ x, InComponent m [root] a x →
        ∃ p : {p : List V // ResidualObsPath m [root] a p},
          pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map π := by
  have ha : a ∉ [root] := by simpa using (ne_of_adj m hra).symm
  obtain ⟨π, hπ, hfix, hab, hout, hwit⟩ := exists_sameBoundary_automorphism e ha
  exact ⟨π, hπ, hfix root (by simp), hab, hout, hwit⟩

end

end TetraStereo.OneCenter.BoundaryComponentReconstruction

assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.ChildGlueData.glue
assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.exists_witnessedBoundaryComponentIso_le
assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.exists_witnessedBoundaryComponentIso
assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.witnessedBoundaryComponentIso
assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.boundaryComponentIso_of_pathTreeEquiv
assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.componentExchangePerm
assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.componentExchangePerm_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.exists_sameBoundary_automorphism
assert_kernel_only TetraStereo.OneCenter.BoundaryComponentReconstruction.root_outward_arm_automorphism
