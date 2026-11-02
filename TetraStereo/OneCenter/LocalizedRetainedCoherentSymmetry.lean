import TetraStereo.OneCenter.LocalizedRetainedRingSymmetryReconstruction
import TetraStereo.OneCenter.MoleculeGraph
import TetraStereo.OneCenter.Symmetry
import TetraStereo.KernelOnly
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Residual components of a full observation tree

`ResidualPathTreeEquiv` records a two-sided equivalence of every self-avoiding residual walk,
including terminal labels, ordered boundary-index bonds, non-parent ancestor bonds, and the
immediate parent bond. This file proves the finite normalized-entry mass and Hall matching
lemmas, the length-two induced bijection on deleted-entry neighbors, and the restriction of the
full equivalence to each deleted-entry child. `DeclarativeCIPBoundaryComponentReconstruction`
uses them to construct the witnessed boundary-preserving component isomorphism and the
boundary-fixing molecular automorphism. The path bijection is not asserted to descend to a vertex
map on every path.

Primitive graph automorphisms are separate from configuration/parity preservation. The latter
requires the corresponding physical color-compatible inverse and is not established here.
-/

namespace TetraStereo.OneCenter.RetainedCoherentSymmetry

noncomputable section

open Classical
open RetainedRingSymmetryReconstruction
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Residual graph after deleting an ordered ancestor boundary. -/
def residualGraph (m : MoleculeGraph V) (B : List V) : SimpleGraph V where
  Adj x y := x ∉ B ∧ y ∉ B ∧ m.Adj x y
  symm := by
    intro x y h
    exact ⟨h.2.1, h.1, (m.adj_symm).1 h.2.2⟩
  loopless := by
    constructor
    intro x h
    have := h.2.2
    simp [MoleculeGraph.Adj, m.bond_self] at this

instance residualGraph_decidableRel (m : MoleculeGraph V) (B : List V) :
    DecidableRel (residualGraph m B).Adj := by
  intro x y
  dsimp [residualGraph]
  infer_instance

/-- Equality of connected components is the decidable reachability relation on chosen representatives. -/
noncomputable instance instDecidableEqConnectedComponent (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableEq G.ConnectedComponent := fun c d =>
  decidable_of_iff (G.Reachable (Quot.out c) (Quot.out d)) <| by
    rw [← SimpleGraph.ConnectedComponent.eq]
    simp [SimpleGraph.connectedComponentMk, Quot.out_eq]

/-- A vertex of the residual component of `v` after deleting `B`. -/
def InComponent (m : MoleculeGraph V) (B : List V) (v x : V) : Prop :=
  v ∉ B ∧ (residualGraph m B).Reachable v x

instance (m : MoleculeGraph V) (B : List V) (v x : V) : Decidable (InComponent m B v x) := by
  unfold InComponent
  infer_instance

def compSet (m : MoleculeGraph V) (B : List V) (v : V) : Set V :=
  {x | InComponent m B v x}

def compCard (m : MoleculeGraph V) (B : List V) (v : V) : Nat :=
  (compSet m B v).ncard

lemma residual_adj_iff (m : MoleculeGraph V) (B : List V) (x y : V) :
    (residualGraph m B).Adj x y ↔ x ∉ B ∧ y ∉ B ∧ m.Adj x y := Iff.rfl

lemma inComponent_self (m : MoleculeGraph V) {B : List V} {v : V} (hv : v ∉ B) :
    InComponent m B v v :=
  ⟨hv, SimpleGraph.Reachable.refl v⟩

lemma walk_end_outside {m : MoleculeGraph V} {B : List V} {y z : V}
    (p : (residualGraph m B).Walk y z) (hy : y ∉ B) : z ∉ B := by
  induction p with
  | nil => exact hy
  | cons h q ih => exact ih h.2.1

lemma walk_support_outside {m : MoleculeGraph V} {B : List V} {y z : V}
    (p : (residualGraph m B).Walk y z) (hy : y ∉ B) :
    ∀ u, u ∈ p.support → u ∉ B := by
  induction p with
  | nil =>
      intro u hu
      simp at hu
      simpa [hu] using hy
  | cons h q ih =>
      intro u hu
      simp at hu
      rcases hu with rfl | hu
      · exact hy
      · exact ih h.2.1 u hu

lemma inComponent_not_mem (m : MoleculeGraph V) {B : List V} {v x : V}
    (hx : InComponent m B v x) : x ∉ B := by
  rcases hx with ⟨hv, ⟨p⟩⟩
  exact walk_end_outside p hv

lemma inComponent_entry (m : MoleculeGraph V) {B : List V} {v x : V}
    (hx : InComponent m B v x) : v ∉ B :=
  hx.1

lemma not_mem_append_singleton {B : List V} {v x : V} :
    x ∉ B ++ [v] ↔ x ∉ B ∧ x ≠ v := by
  simp

lemma reachable_extended_of_walk {m : MoleculeGraph V} {B : List V} {v y z : V}
    (p : (residualGraph m B).Walk y z)
    (h : ∀ u, u ∈ p.support → u ∉ B ∧ u ≠ v) :
    (residualGraph m (B ++ [v])).Reachable y z := by
  induction p with
  | nil =>
      exact SimpleGraph.Reachable.refl _
  | cons hadj q ih =>
      rename_i u y z
      have hu : u ∉ B ∧ u ≠ v := h u (by simp)
      have hy : y ∉ B ∧ y ≠ v := h y (by simp)
      have htail : ∀ t, t ∈ q.support → t ∉ B ∧ t ≠ v := by
        intro t ht
        exact h t (by simp [ht])
      have hadj' : (residualGraph m (B ++ [v])).Adj u y := by
        refine ⟨?_, ?_, hadj.2.2⟩
        · simpa using And.intro hu.1 hu.2
        · simpa using And.intro hy.1 hy.2
      exact hadj'.reachable.trans (ih htail)

lemma extended_adj_mono {m : MoleculeGraph V} {B : List V} {v a b : V} :
    (residualGraph m (B ++ [v])).Adj a b → (residualGraph m B).Adj a b := by
  intro h
  rcases h with ⟨ha, hb, hadj⟩
  simp at ha hb
  exact ⟨ha.1, hb.1, hadj⟩

lemma reachable_of_extended {m : MoleculeGraph V} {B : List V} {v y z : V}
    (h : (residualGraph m (B ++ [v])).Reachable y z) :
    (residualGraph m B).Reachable y z := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj q ih => exact (extended_adj_mono hadj).reachable.trans ih

lemma exists_child_bridge {m : MoleculeGraph V} {B : List V} {v x : V}
    (hv : v ∉ B) (hx : InComponent m B v x) (hne : x ≠ v) :
    ∃ y, (residualGraph m B).Adj v y ∧ InComponent m (B ++ [v]) y x := by
  refine (show InComponent m B v x from ⟨hv, hx.2⟩).2.elim_path ?_
  intro p
  have hvx : v ≠ x := ne_comm.mp hne
  obtain ⟨y, hvy, q, hq⟩ := (p : (residualGraph m B).Walk v x).exists_eq_cons_of_ne hvx
  have hnodup : (p : (residualGraph m B).Walk v x).support.Nodup := p.nodup_support
  have hsupport : (p : (residualGraph m B).Walk v x).support = v :: q.support := by
    rw [hq]
    simp
  have hvq : v ∉ q.support := by
    have := (List.nodup_cons.mp (hsupport ▸ hnodup)).1
    simpa using this
  have hyB : y ∉ B := hvy.2.1
  have hyv : y ≠ v := by
    intro hyv
    exact hvq (by simpa [hyv] using q.start_mem_support)
  have hout : ∀ u, u ∈ q.support → u ∉ B ∧ u ≠ v := by
    intro u hu
    exact ⟨walk_support_outside q hyB u hu, fun hvu => hvq (hvu ▸ hu)⟩
  exact ⟨y, hvy, ⟨by simpa using And.intro hyB hyv, reachable_extended_of_walk q hout⟩⟩

lemma child_subset_erase {m : MoleculeGraph V} {B : List V} {v y x : V}
    (hv : v ∉ B) (hy : (residualGraph m B).Adj v y)
    (hx : InComponent m (B ++ [v]) y x) :
    InComponent m B v x ∧ x ≠ v := by
  have hxB : x ∉ B ++ [v] := inComponent_not_mem m hx
  have hxv : x ≠ v := by
    intro hxv
    exact hxB (by simp [hxv])
  have hreach : (residualGraph m B).Reachable y x := reachable_of_extended hx.2
  exact ⟨⟨hv, hy.reachable.trans hreach⟩, hxv⟩

lemma nodup_append_singleton {B : List V} {v : V} (hB : B.Nodup) (hv : v ∉ B) :
    (B ++ [v]).Nodup := by
  rw [List.nodup_append']
  refine ⟨hB, by simp, ?_⟩
  intro a ha hv'
  simp at hv'
  exact hv (hv' ▸ ha)

lemma length_append_singleton (B : List V) (v : V) : (B ++ [v]).length = B.length + 1 := by
  simp

lemma get_append_left (B : List V) (a : V) (i : Nat) (hi : i < B.length) :
    (B ++ [a]).get ⟨i, by simp; omega⟩ = B.get ⟨i, hi⟩ := by
  induction B generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp
          exact ih i (by simp at hi; omega)

lemma get_append_last (B : List V) (a : V) :
    (B ++ [a]).get ⟨B.length, by simp⟩ = a := by
  induction B with
  | nil => simp
  | cons _ _ _ => simp

lemma compCard_pos (m : MoleculeGraph V) {B : List V} {v : V} (hv : v ∉ B) :
    0 < compCard m B v := by
  unfold compCard
  exact (Set.ncard_pos).2 ⟨v, inComponent_self m hv⟩

lemma compSet_child_subset (m : MoleculeGraph V) {B : List V} {v y : V}
    (hv : v ∉ B) (hy : (residualGraph m B).Adj v y) :
    compSet m (B ++ [v]) y ⊆ compSet m B v \ {v} := by
  intro x hx
  have h := child_subset_erase hv hy hx
  exact ⟨h.1, h.2⟩

lemma compCard_child_le (m : MoleculeGraph V) {B : List V} {v y : V}
    (hv : v ∉ B) (hy : (residualGraph m B).Adj v y) :
    compCard m (B ++ [v]) y ≤ compCard m B v - 1 := by
  unfold compCard
  have hsub := compSet_child_subset m hv hy
  have hle := Set.ncard_le_ncard hsub
  have hdiff : (compSet m B v \ {v}).ncard = (compSet m B v).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem (inComponent_self m hv)
  exact hle.trans (by rw [hdiff])

lemma mem_take_imp {α : Type*} {p : List α} {k : Nat} {x : α} (hx : x ∈ p.take k) : x ∈ p := by
  induction p generalizing k with
  | nil => simp at hx
  | cons a as ih =>
      cases k with
      | zero => simp at hx
      | succ k =>
          simp at hx
          rcases hx with rfl | hx
          · simp
          · exact List.mem_cons_of_mem a (ih hx)

lemma nodup_take {α : Type*} {p : List α} (h : p.Nodup) (k : Nat) : (p.take k).Nodup := by
  induction p generalizing k with
  | nil => simp
  | cons a as ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [List.nodup_cons] at h
          simp
          exact ⟨fun ha => h.1 (mem_take_imp ha), ih h.2 k⟩

lemma dropLast_take_succ {α : Type*} :
    ∀ (p : List α) (k : Nat), k < p.length → (p.take (k + 1)).dropLast = p.take k
  | [], _, hk => by simp at hk
  | _ :: _, 0, _ => by simp
  | a :: as, k + 1, hk => by
      have hk' : k < as.length := by
        simp at hk
        exact hk
      have htail := dropLast_take_succ as k hk'
      have hne : as.take (k + 1) ≠ [] := by
        intro hempty
        have hlen : (as.take (k + 1)).length = k + 1 := by
          rw [List.length_take, Nat.min_eq_left (by omega)]
        simp [hempty] at hlen
      calc
        ((a :: as).take ((k + 1) + 1)).dropLast
            = (a :: as.take (k + 1)).dropLast := by simp
        _ = a :: (as.take (k + 1)).dropLast := List.dropLast_cons_of_ne_nil hne
        _ = a :: as.take k := by rw [htail]
        _ = (a :: as).take (k + 1) := by simp

lemma head?_take_of_pos {α : Type*} (p : List α) {k : Nat} (hk : 0 < k) :
    (p.take k).head? = p.head? := by
  cases p with
  | nil => simp
  | cons a as =>
      cases k with
      | zero => omega
      | succ k => simp

lemma bondedChain_take (m : MoleculeGraph V) (p : List V) (k : Nat) (h : BondedChain m p) :
    BondedChain m (p.take k) := by
  induction p generalizing k with
  | nil => simp [BondedChain]
  | cons x xs ih =>
      cases k with
      | zero => simp [BondedChain]
      | succ k =>
          cases xs with
          | nil => simp [BondedChain]
          | cons y ys =>
              have hxy : 0 < m.bond x y ∧ BondedChain m (y :: ys) := by
                simpa [BondedChain] using h
              cases k with
              | zero => simp [BondedChain]
              | succ k =>
                  have htail := ih (k + 1) hxy.2
                  simpa [List.take, BondedChain] using And.intro hxy.1 htail

lemma head?_dropLast_of_lt {α : Type*} (p : List α) (hp : 1 < p.length) :
    p.dropLast.head? = p.head? := by
  cases p with
  | nil => simp at hp
  | cons a as =>
      cases as with
      | nil => simp at hp
      | cons b bs => simp

lemma mem_dropLast_imp {α : Type*} {p : List α} {x : α} (hx : x ∈ p.dropLast) : x ∈ p := by
  induction p with
  | nil => simp at hx
  | cons a as ih =>
      cases as with
      | nil => simp at hx
      | cons b bs =>
          simp at hx
          rcases hx with rfl | hx
          · simp
          · exact List.mem_cons_of_mem a (ih hx)

lemma nodup_dropLast {α : Type*} {p : List α} (h : p.Nodup) : p.dropLast.Nodup := by
  induction p with
  | nil => simp
  | cons a as ih =>
      cases as with
      | nil => simp
      | cons b bs =>
          rw [List.nodup_cons] at h
          simp
          exact ⟨fun ha => h.1 (mem_dropLast_imp ha), ih h.2⟩

lemma length_dropLast_eq {α : Type*} (p : List α) (hp : p ≠ []) :
    p.dropLast.length = p.length - 1 := by
  cases p with
  | nil => contradiction
  | cons a as =>
      cases as with
      | nil => simp
      | cons b bs => simp

lemma ne_of_adj (m : MoleculeGraph V) {u v : V} (h : m.Adj u v) : u ≠ v := by
  intro heq
  subst heq
  simp [MoleculeGraph.Adj, m.bond_self] at h

/-- A self-avoiding residual walk. Ring returns are bonds to earlier indices, not extra vertices. -/
structure ResidualObsPath (m : MoleculeGraph V) (B : List V) (entry : V) (p : List V) : Prop where
  nonempty : p ≠ []
  head : p.head? = some entry
  nodup : p.Nodup
  outside : ∀ x ∈ p, x ∉ B
  chain : BondedChain m p

lemma obs_singleton (m : MoleculeGraph V) {B : List V} {entry : V} (h : entry ∉ B) :
    ResidualObsPath m B entry [entry] where
  nonempty := by simp
  head := by simp
  nodup := by simp
  outside := by
    intro x hx
    simp at hx
    simpa [hx] using h
  chain := by simp [BondedChain]

lemma obs_pair (m : MoleculeGraph V) {B : List V} {v x : V}
    (hv : v ∉ B) (hx : m.Adj v x) (hxB : x ∉ B) :
    ResidualObsPath m B v [v, x] where
  nonempty := by simp
  head := by simp
  nodup := by
    simp
    exact ne_of_adj m hx
  outside := by
    intro y hy
    simp at hy
    rcases hy with rfl | rfl
    · exact hv
    · exact hxB
  chain := by simpa [BondedChain] using hx

lemma obs_take (m : MoleculeGraph V) {B : List V} {entry : V} {p : List V}
    (hp : ResidualObsPath m B entry p) {k : Nat} (hk : k ≤ p.length) (hk0 : 0 < k) :
    ResidualObsPath m B entry (p.take k) where
  nonempty := by
    intro hempty
    cases p with
    | nil =>
        simp at hk
        omega
    | cons a as =>
        cases k with
        | zero => omega
        | succ k => simp at hempty
  head := by
    rw [head?_take_of_pos p hk0, hp.head]
  nodup := nodup_take hp.nodup k
  outside := by
    intro x hx
    exact hp.outside x (mem_take_imp hx)
  chain := bondedChain_take m p k hp.chain

lemma obs_dropLast (m : MoleculeGraph V) {B : List V} {entry : V} {p : List V}
    (hp : ResidualObsPath m B entry p) (hlen : 1 < p.length) :
    ResidualObsPath m B entry p.dropLast where
  nonempty := by
    intro hempty
    have hlen0 : p.dropLast.length = 0 := by simp [hempty]
    rw [length_dropLast_eq p hp.nonempty] at hlen0
    omega
  head := by rw [head?_dropLast_of_lt p hlen, hp.head]
  nodup := nodup_dropLast hp.nodup
  outside := by
    intro x hx
    exact hp.outside x (mem_dropLast_imp hx)
  chain := bondedChain_dropLast hp.chain

lemma obs_cons_child (m : MoleculeGraph V) {B : List V} {v x : V} {p : List V}
    (hv : v ∉ B) (hx : m.Adj v x) (hxB : x ∉ B)
    (hp : ResidualObsPath m (B ++ [v]) x p) :
    ResidualObsPath m B v (v :: p) where
  nonempty := by simp
  head := by simp
  nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, hp.nodup⟩
    intro hvmem
    exact (not_mem_append_singleton.mp (hp.outside v hvmem)).2 rfl
  outside := by
    intro y hy
    simp at hy
    rcases hy with rfl | hy
    · exact hv
    · exact (not_mem_append_singleton.mp (hp.outside y hy)).1
  chain := by
    have hhead : p.head? = some x := hp.head
    cases p with
    | nil => exact (hp.nonempty rfl).elim
    | cons y ys =>
        have hy : y = x := by simpa using hhead
        subst hy
        simpa [BondedChain] using And.intro hx hp.chain

lemma obs_tail (m : MoleculeGraph V) {B : List V} {v : V} {p : List V}
    (hp : ResidualObsPath m B v p) (hlen : 1 < p.length) :
    ResidualObsPath m (B ++ [v]) (p.get ⟨1, by omega⟩) p.tail where
  nonempty := by
    intro h
    cases p with
    | nil => simp at hlen
    | cons a as =>
        cases as with
        | nil => simp at hlen
        | cons b bs => simp at h
  head := by
    cases p with
    | nil => simp at hlen
    | cons a as =>
        cases as with
        | nil => simp at hlen
        | cons b bs => simp
  nodup := by
    cases p with
    | nil => simp at hlen
    | cons a as =>
        have hnodup := hp.nodup
        rw [List.nodup_cons] at hnodup
        simpa using hnodup.2
  outside := by
    intro y hy
    have hyB : y ∉ B := hp.outside y (by
      cases p with
      | nil => simp at hlen
      | cons a as => exact List.mem_cons_of_mem a hy)
    have hyv : y ≠ v := by
      intro hyv
      cases p with
      | nil => simp at hlen
      | cons a as =>
          have hnodup := hp.nodup
          rw [List.nodup_cons] at hnodup
          have : v ∈ as := by simpa [hyv] using hy
          have hvhead : a = v := by
            have := hp.head
            simpa using this
          exact hnodup.1 (by simpa [hvhead] using this)
    simpa using And.intro hyB hyv
  chain := by
    cases p with
    | nil => simp at hlen
    | cons a as =>
        cases as with
        | nil => simp at hlen
        | cons b bs =>
            have hchain : 0 < m.bond a b ∧ BondedChain m (b :: bs) := by
              simpa [BondedChain] using hp.chain
            simpa using hchain.2

def pathTerminal (p : List V) (hp : p ≠ []) : V := p.getLast hp

lemma pathTerminal_cons_ne (x : V) (xs : List V) (hxs : xs ≠ []) :
    pathTerminal (x :: xs) (by simp) = pathTerminal xs hxs := by
  cases xs with
  | nil => contradiction
  | cons y ys => simp [pathTerminal]

lemma pathTerminal_singleton (x : V) : pathTerminal [x] (by simp) = x := by
  simp [pathTerminal]

lemma nat_index_lt_of_add {n i : Nat} (h : i + 2 < n) : i < n := by omega

lemma nat_image_index_lt {n m i : Nat} (hlen : n = m) (h : i + 2 < m) : i < n := by omega

lemma nat_parent_index_lt {n : Nat} (h : 1 < n) : n - 2 < n := by omega

lemma nat_image_parent_index_lt {n m : Nat} (hlen : n = m) (h : 1 < m) : n - 2 < n := by omega

/-- Full two-sided observation equivalence of residual components pointed at `v` and `w`. -/
structure ResidualPathTreeEquiv (m : MoleculeGraph V) (Bs Bt : List V) (v w : V) where
  len_eq : Bs.length = Bt.length
  toEquiv : {p : List V // ResidualObsPath m Bs v p} ≃ {p : List V // ResidualObsPath m Bt w p}
  length_eq : ∀ p : {p : List V // ResidualObsPath m Bs v p},
    (toEquiv p).1.length = p.1.length
  dropLast_eq : ∀ (p : {p : List V // ResidualObsPath m Bs v p}) (hp : 1 < p.1.length),
    (toEquiv ⟨p.1.dropLast, obs_dropLast m p.2 hp⟩).1 = (toEquiv p).1.dropLast
  atomZ_eq : ∀ p : {p : List V // ResidualObsPath m Bs v p},
    m.atomZ (pathTerminal (toEquiv p).1 (toEquiv p).2.nonempty) =
      m.atomZ (pathTerminal p.1 p.2.nonempty)
  atomMass_eq : ∀ p : {p : List V // ResidualObsPath m Bs v p},
    m.atomMass (pathTerminal (toEquiv p).1 (toEquiv p).2.nonempty) =
      m.atomMass (pathTerminal p.1 p.2.nonempty)
  formalCharge_eq : ∀ p : {p : List V // ResidualObsPath m Bs v p},
    m.formalCharge (pathTerminal (toEquiv p).1 (toEquiv p).2.nonempty) =
      m.formalCharge (pathTerminal p.1 p.2.nonempty)
  boundaryBond_eq : ∀ p : {p : List V // ResidualObsPath m Bs v p}, ∀ i : Nat,
    (hi : i < Bs.length) →
    m.bond (pathTerminal (toEquiv p).1 (toEquiv p).2.nonempty)
        (Bt.get ⟨i, by rw [← len_eq]; exact hi⟩) =
      m.bond (pathTerminal p.1 p.2.nonempty) (Bs.get ⟨i, hi⟩)
  /-- Bonds to earlier path vertices except the immediate parent. -/
  ancestorBond_eq : ∀ (p : {p : List V // ResidualObsPath m Bs v p}) (i : Nat)
    (hi : i + 2 < p.1.length),
    m.bond (pathTerminal (toEquiv p).1 (toEquiv p).2.nonempty)
        ((toEquiv p).1.get ⟨i, nat_image_index_lt (length_eq p) hi⟩) =
      m.bond (pathTerminal p.1 p.2.nonempty) (p.1.get ⟨i, nat_index_lt_of_add hi⟩)
  /-- The omitted immediate-parent edge, restored explicitly. -/
  parentBond_eq : ∀ (p : {p : List V // ResidualObsPath m Bs v p}) (hp : 1 < p.1.length),
    m.bond (pathTerminal (toEquiv p).1 (toEquiv p).2.nonempty)
        ((toEquiv p).1.get ⟨(toEquiv p).1.length - 2,
          nat_image_parent_index_lt (length_eq p) hp⟩) =
      m.bond (pathTerminal p.1 p.2.nonempty)
        (p.1.get ⟨p.1.length - 2, nat_parent_index_lt hp⟩)

/-- Reverse a full observation-tree equivalence. -/
noncomputable def ResidualPathTreeEquiv.symm {m : MoleculeGraph V} {Bs Bt : List V}
    {v w : V} (e : ResidualPathTreeEquiv m Bs Bt v w) :
    ResidualPathTreeEquiv m Bt Bs w v where
  len_eq := e.len_eq.symm
  toEquiv := e.toEquiv.symm
  length_eq := by
    intro p
    let q := e.toEquiv.symm p
    have hqp : e.toEquiv q = p := e.toEquiv.apply_symm_apply p
    have h := e.length_eq q
    simpa [q, hqp] using h.symm
  dropLast_eq := by
    intro p hp
    let q := e.toEquiv.symm p
    have hqp : e.toEquiv q = p := e.toEquiv.apply_symm_apply p
    have hq : 1 < q.1.length := by
      have h := e.length_eq q
      rw [hqp] at h
      omega
    have hdrop := e.dropLast_eq q hq
    have hmapEq :
        e.toEquiv (e.toEquiv.symm ⟨p.1.dropLast, obs_dropLast m p.2 hp⟩) =
          e.toEquiv ⟨q.1.dropLast, obs_dropLast m q.2 hq⟩ := by
      apply Subtype.ext
      calc
        (e.toEquiv (e.toEquiv.symm ⟨p.1.dropLast, obs_dropLast m p.2 hp⟩)).1 = p.1.dropLast :=
          congrArg Subtype.val (e.toEquiv.apply_symm_apply _)
        _ = (e.toEquiv q).1.dropLast := by rw [hqp]
        _ = (e.toEquiv ⟨q.1.dropLast, obs_dropLast m q.2 hq⟩).1 := hdrop.symm
    exact congrArg Subtype.val (e.toEquiv.injective hmapEq)
  atomZ_eq := by
    intro p
    let q := e.toEquiv.symm p
    have hqp : e.toEquiv q = p := e.toEquiv.apply_symm_apply p
    have h := e.atomZ_eq q
    simpa [q, hqp] using h.symm
  atomMass_eq := by
    intro p
    let q := e.toEquiv.symm p
    have hqp : e.toEquiv q = p := e.toEquiv.apply_symm_apply p
    have h := e.atomMass_eq q
    simpa [q, hqp] using h.symm
  formalCharge_eq := by
    intro p
    let q := e.toEquiv.symm p
    have hqp : e.toEquiv q = p := e.toEquiv.apply_symm_apply p
    have h := e.formalCharge_eq q
    simpa [q, hqp] using h.symm
  boundaryBond_eq := by
    intro p i hi
    let q := e.toEquiv.symm p
    have hqp : e.toEquiv q = p := e.toEquiv.apply_symm_apply p
    have hi' : i < Bs.length := by rw [e.len_eq]; exact hi
    have h := e.boundaryBond_eq q i hi'
    simpa [q, hqp] using h.symm
  ancestorBond_eq := by
    intro p i hi
    let q := e.toEquiv.symm p
    have hqp : e.toEquiv q = p := e.toEquiv.apply_symm_apply p
    have hlen : q.1.length = p.1.length := by
      have h := e.length_eq q
      rw [hqp] at h
      exact h.symm
    have h := e.ancestorBond_eq q i (by rw [hlen]; exact hi)
    simpa [q, hqp, hlen] using h.symm
  parentBond_eq := by
    intro p hp
    let q := e.toEquiv.symm p
    have hqp : e.toEquiv q = p := e.toEquiv.apply_symm_apply p
    have hlen : q.1.length = p.1.length := by
      have h := e.length_eq q
      rw [hqp] at h
      exact h.symm
    have h := e.parentBond_eq q (by rw [hlen]; exact hp)
    simpa [q, hqp, hlen] using h.symm

/-- Boundary-preserving isomorphism of two residual components. -/
structure BoundaryComponentIso (m : MoleculeGraph V) (Bs Bt : List V) (v w : V) where
  len_eq : Bs.length = Bt.length
  toFun : V → V
  invFun : V → V
  left_inv : ∀ x, InComponent m Bs v x → invFun (toFun x) = x
  right_inv : ∀ y, InComponent m Bt w y → toFun (invFun y) = y
  maps_to : ∀ x, InComponent m Bs v x → InComponent m Bt w (toFun x)
  maps_inv : ∀ y, InComponent m Bt w y → InComponent m Bs v (invFun y)
  entry : toFun v = w
  inv_entry : invFun w = v
  atomZ_eq : ∀ x, InComponent m Bs v x → m.atomZ (toFun x) = m.atomZ x
  atomMass_eq : ∀ x, InComponent m Bs v x → m.atomMass (toFun x) = m.atomMass x
  formalCharge_eq : ∀ x, InComponent m Bs v x → m.formalCharge (toFun x) = m.formalCharge x
  bond_eq : ∀ x y, InComponent m Bs v x → InComponent m Bs v y →
    m.bond (toFun x) (toFun y) = m.bond x y
  boundary_eq : ∀ x, InComponent m Bs v x → ∀ i : Nat, (hi : i < Bs.length) →
    m.bond (toFun x) (Bt.get ⟨i, by rw [← len_eq]; exact hi⟩) =
      m.bond x (Bs.get ⟨i, hi⟩)

/-- A boundary-preserving component isomorphism carries the neighbors attached through its
last ordered boundary slot bijectively to the target neighbors at that slot. -/
noncomputable def componentEntryEquiv {m : MoleculeGraph V} {Bs Bt : List V} {v w x y : V}
    (iso : BoundaryComponentIso m (Bs ++ [v]) (Bt ++ [w]) x y) :
    {z // InComponent m (Bs ++ [v]) x z ∧ m.Adj v z} ≃
      {z // InComponent m (Bt ++ [w]) y z ∧ m.Adj w z} := by
  classical
  have hbase : Bs.length = Bt.length := by
    have hlen := iso.len_eq
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  let f : {z // InComponent m (Bs ++ [v]) x z ∧ m.Adj v z} →
      {z // InComponent m (Bt ++ [w]) y z ∧ m.Adj w z} := fun z => by
    have hb := iso.boundary_eq z.1 z.2.1 Bs.length (by simp)
    have hidx : (⟨Bs.length, by rw [List.length_append, List.length_singleton]; omega⟩ : Fin (Bt ++ [w]).length) =
        ⟨Bt.length, by simp⟩ := by
      apply Fin.ext
      exact hbase
    have hb' : m.bond (iso.toFun z.1) w = m.bond z.1 v := by
      rw [hidx, get_append_last, get_append_last] at hb
      exact hb
    have hadj : m.Adj w (iso.toFun z.1) := by
      have hpos := z.2.2
      change 0 < m.bond w (iso.toFun z.1)
      rw [m.bond_symm, hb', m.bond_symm]
      exact hpos
    exact ⟨iso.toFun z.1, iso.maps_to z.1 z.2.1, hadj⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hval : iso.toFun a.1 = iso.toFun b.1 := congrArg Subtype.val hab
    calc
      a.1 = iso.invFun (iso.toFun a.1) := (iso.left_inv a.1 a.2.1).symm
      _ = iso.invFun (iso.toFun b.1) := congrArg iso.invFun hval
      _ = b.1 := iso.left_inv b.1 b.2.1
  have hsurj : Function.Surjective f := by
    intro z
    let hb := iso.boundary_eq (iso.invFun z.1) (iso.maps_inv z.1 z.2.1) Bs.length (by simp)
    have hidx : (⟨Bs.length, by rw [List.length_append, List.length_singleton]; omega⟩ : Fin (Bt ++ [w]).length) =
        ⟨Bt.length, by simp⟩ := by
      apply Fin.ext
      exact hbase
    have hb' : m.bond z.1 w = m.bond (iso.invFun z.1) v := by
      rw [hidx, get_append_last, get_append_last] at hb
      simpa [iso.right_inv z.1 z.2.1] using hb
    have hadj : m.Adj v (iso.invFun z.1) := by
      change 0 < m.bond v (iso.invFun z.1)
      rw [m.bond_symm, ← hb', m.bond_symm]
      exact z.2.2
    refine ⟨⟨iso.invFun z.1, iso.maps_inv z.1 z.2.1, hadj⟩, ?_⟩
    apply Subtype.ext
    exact iso.right_inv z.1 z.2.1
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

/-- An owner fiber of global attachment entries is equivalent to the entries packaged as
neighbors inside its pointed residual component. -/
noncomputable def ownerEntryFiberEquivRooted
    {m : MoleculeGraph V} {B : List V} {v x : V}
    (hx : m.Adj v x ∧ x ∉ B) :
    {z : {z // m.Adj v z ∧ z ∉ B} //
      (residualGraph m (B ++ [v])).connectedComponentMk z.1 =
        (residualGraph m (B ++ [v])).connectedComponentMk x} ≃
    {z // InComponent m (B ++ [v]) x z ∧ m.Adj v z} := by
  classical
  have hxout : x ∉ B ++ [v] := by
    rw [not_mem_append_singleton]
    exact ⟨hx.2, ne_comm.mp (ne_of_adj m hx.1)⟩
  let f :
      {z : {z // m.Adj v z ∧ z ∉ B} //
        (residualGraph m (B ++ [v])).connectedComponentMk z.1 =
          (residualGraph m (B ++ [v])).connectedComponentMk x} →
      {z // InComponent m (B ++ [v]) x z ∧ m.Adj v z} := fun z => by
    have hreach : (residualGraph m (B ++ [v])).Reachable x z.1.1 :=
      (SimpleGraph.ConnectedComponent.eq.mp z.2).symm
    exact ⟨z.1.1, ⟨hxout, hreach⟩, z.1.2.1⟩
  let g :
      {z // InComponent m (B ++ [v]) x z ∧ m.Adj v z} →
      {z : {z // m.Adj v z ∧ z ∉ B} //
        (residualGraph m (B ++ [v])).connectedComponentMk z.1 =
          (residualGraph m (B ++ [v])).connectedComponentMk x} := fun z => by
    have hzout := inComponent_not_mem m z.2.1
    exact ⟨⟨z.1, z.2.2, (not_mem_append_singleton.mp hzout).1⟩,
      SimpleGraph.ConnectedComponent.eq.mpr z.2.1.2.symm⟩
  have hleft : ∀ z, g (f z) = z := by
    intro z
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hright : ∀ z, f (g z) = z := by
    intro z
    apply Subtype.ext
    rfl
  exact Equiv.ofBijective f ⟨fun a b h => by
      have := congrArg g h
      simpa [hleft] using this,
    fun z => ⟨g z, hright z⟩⟩

/-- A child component isomorphism gives an equivalence of the corresponding global owner
fibers: first pass to component-rooted attachment entries, then use its boundary-preserving
entry equivalence, and finally forget the root-reachability packaging. -/
noncomputable def componentOwnerFiberEquiv
    {m : MoleculeGraph V} {Bs Bt : List V} {v w x y : V}
    (iso : BoundaryComponentIso m (Bs ++ [v]) (Bt ++ [w]) x y)
    (hx : m.Adj v x ∧ x ∉ Bs) :
    {z : {z // m.Adj v z ∧ z ∉ Bs} //
      (residualGraph m (Bs ++ [v])).connectedComponentMk z.1 =
        (residualGraph m (Bs ++ [v])).connectedComponentMk x} ≃
    {z : {z // m.Adj w z ∧ z ∉ Bt} //
      (residualGraph m (Bt ++ [w])).connectedComponentMk z.1 =
        (residualGraph m (Bt ++ [w])).connectedComponentMk y} := by
  let src := ownerEntryFiberEquivRooted hx
  let dst := ownerEntryFiberEquivRooted (by
    have hxout : x ∉ Bs ++ [v] := by
      rw [not_mem_append_singleton]
      exact ⟨hx.2, ne_comm.mp (ne_of_adj m hx.1)⟩
    have hyroot := iso.maps_to x (inComponent_self m hxout)
    have hyout : y ∉ Bt ++ [w] := by
      have hroot : InComponent m (Bt ++ [w]) y y := by
        simpa [iso.entry] using hyroot
      exact inComponent_not_mem m hroot
    -- The last boundary slot carries the root-to-entry bond.
    have hbase : Bs.length = Bt.length := by
      have hlen := iso.len_eq
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hb := iso.boundary_eq x (inComponent_self m hxout) Bs.length (by simp)
    have hidx : (⟨Bs.length, by simp [hbase]⟩ : Fin (Bt ++ [w]).length) = ⟨Bt.length, by simp⟩ := by
      apply Fin.ext
      exact hbase
    have hb' : m.bond y w = m.bond x v := by
      rw [hidx, get_append_last, get_append_last] at hb
      simpa [iso.entry] using hb
    have hadj : m.Adj w y := by
      change 0 < m.bond w y
      rw [m.bond_symm, hb', m.bond_symm]
      exact hx.1
    exact ⟨hadj, (not_mem_append_singleton.mp hyout).1⟩)
  exact src.trans ((componentEntryEquiv iso).trans dst.symm)

/-- A component reconstruction carries a graph isomorphism together with one realizing
full-history witness per vertex for the original path equivalence. This intentionally does not
require the original path equivalence to descend on every path. -/
structure WitnessedBoundaryComponentIso {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) where
  iso : BoundaryComponentIso m Bs Bt v w
  witnessPath : ∀ x, InComponent m Bs v x →
    ∃ p : {p : List V // ResidualObsPath m Bs v p},
      pathTerminal p.1 p.2.nonempty = x ∧
      (e.toEquiv p).1 = p.1.map iso.toFun

lemma take_image {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w)
    (p : {p : List V // ResidualObsPath m Bs v p}) (k : Nat)
    (hk : k ≤ p.1.length) (hk0 : 0 < k) :
    (e.toEquiv ⟨p.1.take k, obs_take m p.2 hk hk0⟩).1 = (e.toEquiv p).1.take k := by
  induction hdiff : p.1.length - k using Nat.strongRecOn generalizing k p with
  | ind d ih =>
      by_cases hklen : k = p.1.length
      · subst hklen
        have htake : p.1.take p.1.length = p.1 := List.take_of_length_le (le_refl _)
        have hsub : (⟨p.1.take p.1.length, obs_take m p.2 (le_refl _) hk0⟩ :
            {q : List V // ResidualObsPath m Bs v q}) = p := by
          apply Subtype.ext
          exact htake
        rw [hsub]
        exact (List.take_of_length_le (le_of_eq (e.length_eq p))).symm
      · have hklt : k < p.1.length := by omega
        have hk1 : k + 1 ≤ p.1.length := by omega
        have hk1pos : 0 < k + 1 := by omega
        have hd : p.1.length - (k + 1) < d := by
          have : p.1.length - k = d := hdiff
          omega
        have ih1 := ih (p.1.length - (k + 1)) hd p (k + 1) hk1 hk1pos rfl
        have hdropPath : (p.1.take (k + 1)).dropLast = p.1.take k := dropLast_take_succ p.1 k hklt
        have hlenTake : 1 < (p.1.take (k + 1)).length := by
          have : (p.1.take (k + 1)).length = k + 1 := by
            rw [List.length_take, Nat.min_eq_left hk1]
          omega
        have hdropEq := e.dropLast_eq ⟨p.1.take (k + 1), obs_take m p.2 hk1 hk1pos⟩ hlenTake
        have hsubDrop :
            (⟨(p.1.take (k + 1)).dropLast, obs_dropLast m (obs_take m p.2 hk1 hk1pos) hlenTake⟩ :
              {q // ResidualObsPath m Bs v q}) =
            ⟨p.1.take k, obs_take m p.2 hk hk0⟩ := by
          apply Subtype.ext
          exact hdropPath
        rw [hsubDrop] at hdropEq
        rw [ih1] at hdropEq
        have himgLen : k < (e.toEquiv p).1.length := by
          rw [e.length_eq p]
          exact hklt
        have hdropImg : ((e.toEquiv p).1.take (k + 1)).dropLast = (e.toEquiv p).1.take k :=
          dropLast_take_succ (e.toEquiv p).1 k himgLen
        simpa [hdropImg] using hdropEq

lemma singleton_image {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) :
    (e.toEquiv ⟨[v], obs_singleton m hv⟩).1 = [w] := by
  have hlen := e.length_eq ⟨[v], obs_singleton m hv⟩
  have hp := (e.toEquiv ⟨[v], obs_singleton m hv⟩).2
  have hhead := hp.head
  have hne := hp.nonempty
  cases hlist : (e.toEquiv ⟨[v], obs_singleton m hv⟩).1 with
  | nil => exact (hne (by simp [hlist])).elim
  | cons a as =>
      have ha : a = w := by simpa [hlist] using hhead
      have has : as = [] := by
        have : (a :: as).length = 1 := by simpa [hlist] using hlen
        simp at this
        exact this
      simp [ha, has]

noncomputable def childOf {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) (x : V) : V :=
  if hx : m.Adj v x ∧ x ∉ Bs then
    (e.toEquiv ⟨[v, x], obs_pair m hv hx.1 hx.2⟩).1.get ⟨1, by
      have hlen := e.length_eq ⟨[v, x], obs_pair m hv hx.1 hx.2⟩
      simp at hlen
      omega⟩
  else
    x

lemma pair_image {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    {x : V} (hx : m.Adj v x ∧ x ∉ Bs) :
    (e.toEquiv ⟨[v, x], obs_pair m hv hx.1 hx.2⟩).1 = [w, childOf e hv x] := by
  set img := e.toEquiv ⟨[v, x], obs_pair m hv hx.1 hx.2⟩
  have hlen : img.1.length = 2 := by
    simpa using e.length_eq ⟨[v, x], obs_pair m hv hx.1 hx.2⟩
  have htake := take_image e ⟨[v, x], obs_pair m hv hx.1 hx.2⟩ 1 (by simp) (by decide)
  have hsub : (⟨[v, x].take 1, obs_take m (obs_pair m hv hx.1 hx.2) (by simp) (by decide)⟩ :
      {p // ResidualObsPath m Bs v p}) = ⟨[v], obs_singleton m hv⟩ := by
    apply Subtype.ext
    simp
  have hsing := singleton_image e hv
  have hhead : img.1.take 1 = [w] := by
    have htake' :
        (e.toEquiv ⟨[v, x].take 1, obs_take m (obs_pair m hv hx.1 hx.2) (by simp) (by decide)⟩).1 =
          img.1.take 1 := by
      simpa [img] using htake
    rw [hsub] at htake'
    rw [hsing] at htake'
    exact htake'.symm
  have hchild : img.1.get ⟨1, by omega⟩ = childOf e hv x := by
    simp [img, childOf, dif_pos hx]
  match himg : img.1 with
  | [] => simp [himg] at hlen
  | a :: as =>
      have ha : a = w := by
        have htake1 : (a :: as).take 1 = [a] := by simp
        have : [a] = [w] := by simpa [himg, htake1] using hhead
        simpa using this
      have hasLen : as.length = 1 := by
        have : (a :: as).length = 2 := by simpa [himg] using hlen
        simp at this
        exact this
      cases as with
      | nil => simp at hasLen
      | cons b bs =>
          have hbs : bs = [] := by
            simp at hasLen
            exact hasLen
          have hb : b = childOf e hv x := by
            have hidx : img.1.get ⟨1, by omega⟩ = b := by simp [himg, hbs]
            exact hidx.symm.trans hchild
          simp [ha, hbs, hb]

/-- The image of a child path, after adjoining its deleted entry, has the prescribed
matched entry as its second vertex. -/
lemma child_parent_prefix {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).1.take 2 =
      [w, childOf e hv x] := by
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  have hlen : 2 ≤ p.1.length := by
    have hqne := q.2.nonempty
    cases hq : q.1 with
    | nil => exact (hqne hq).elim
    | cons a rest => simp [p, hq]
  have hprefix :
      (⟨p.1.take 2, obs_take m p.2 hlen (by decide)⟩ :
        {r : List V // ResidualObsPath m Bs v r}) =
      ⟨[v, x], obs_pair m hv hx.1 hx.2⟩ := by
    apply Subtype.ext
    have hh := q.2.head
    cases hq : q.1 with
    | nil => exact (q.2.nonempty hq).elim
    | cons a rest =>
        have ha : a = x := by simpa [hq] using hh
        subst a
        cases rest <;> simp [p, hq]
  have htake := take_image e p 2 hlen (by decide)
  rw [hprefix] at htake
  exact htake.symm.trans (pair_image e hv hx)

lemma get_one_eq_of_take_two {l : List V} {a b : V}
    (hlen : 1 < l.length) (htake : l.take 2 = [a, b]) :
    l.get ⟨1, by omega⟩ = b := by
  cases l with
  | nil => simp at hlen
  | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y ys =>
          have hxy : x = a ∧ y = b := by simpa using htake
          simpa [hxy.2]

/-- Restrict the original path equivalence to a chosen first-entry branch. The target path is
the tail of the image of the path prefixed by the deleted entry; thus this construction retains
the original `toEquiv` on full histories. -/
noncomputable def childPathMap {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    {q : List V // ResidualObsPath m (Bt ++ [w]) (childOf e hv x) q} := by
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  let r := e.toEquiv p
  have hlen : 1 < r.1.length := by
    have hq : 0 < q.1.length := List.length_pos_iff.mpr q.2.nonempty
    have hp : 1 < p.1.length := by simp [p]; omega
    rw [e.length_eq p]
    simp [p]
    omega
  have hprefix := child_parent_prefix e hv hx q
  have hsecond : r.1.get ⟨1, by omega⟩ = childOf e hv x :=
    get_one_eq_of_take_two hlen hprefix
  have htail := obs_tail m r.2 hlen
  exact ⟨r.1.tail, by
    rw [← hsecond]
    exact htail⟩

lemma eq_cons_tail_of_head? {l : List V} {a : V}
    (h : l.head? = some a) : l = a :: l.tail := by
  cases l with
  | nil => simp at h
  | cons x xs =>
      have hx : x = a := by simpa using h
      subst x
      rfl

lemma childPathMap_parent_image {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).1 =
      w :: (childPathMap e hv hx q).1 := by
  have hh := (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).2.head
  simpa [childPathMap] using (eq_cons_tail_of_head? hh)

lemma childPathMap_injective {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs) :
    Function.Injective (childPathMap e hv hx) := by
  intro q₁ q₂ heq
  apply Subtype.ext
  have himg :
      e.toEquiv ⟨v :: q₁.1, obs_cons_child m hv hx.1 hx.2 q₁.2⟩ =
      e.toEquiv ⟨v :: q₂.1, obs_cons_child m hv hx.1 hx.2 q₂.2⟩ := by
    calc
      e.toEquiv ⟨v :: q₁.1, obs_cons_child m hv hx.1 hx.2 q₁.2⟩ =
          ⟨w :: (childPathMap e hv hx q₁).1,
            by rw [← childPathMap_parent_image e hv hx q₁]; exact
              (e.toEquiv ⟨v :: q₁.1, obs_cons_child m hv hx.1 hx.2 q₁.2⟩).2⟩ := by
              apply Subtype.ext
              exact childPathMap_parent_image e hv hx q₁
      _ = ⟨w :: (childPathMap e hv hx q₂).1,
            by rw [← childPathMap_parent_image e hv hx q₂]; exact
              (e.toEquiv ⟨v :: q₂.1, obs_cons_child m hv hx.1 hx.2 q₂.2⟩).2⟩ := by
              apply Subtype.ext
              exact congrArg (fun z : {q : List V // _} => w :: z.1) heq
      _ = e.toEquiv ⟨v :: q₂.1, obs_cons_child m hv hx.1 hx.2 q₂.2⟩ := by
              apply Subtype.ext
              exact (childPathMap_parent_image e hv hx q₂).symm
  have hsrc := e.toEquiv.injective himg
  have hlist := congrArg Subtype.val hsrc
  have htails := congrArg List.tail hlist
  simpa using htails

lemma childOf_adj {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    {x : V} (hx : m.Adj v x ∧ x ∉ Bs) :
    m.Adj w (childOf e hv x) ∧ childOf e hv x ∉ Bt := by
  have himg := pair_image e hv hx
  have hp := (e.toEquiv ⟨[v, x], obs_pair m hv hx.1 hx.2⟩).2
  have hchain := hp.chain
  rw [himg] at hchain
  have hadj : m.Adj w (childOf e hv x) := by simpa [BondedChain] using hchain
  have hout := hp.outside (childOf e hv x)
  rw [himg] at hout
  exact ⟨hadj, hout (by simp)⟩

/-- Distinct source entries cannot have the same target entry: length-two paths are genuine
members of the full path equivalence, even though longer-path endpoint choices need not cohere. -/
lemma childOf_injective {m : MoleculeGraph V} {Bs Bt : List V} {v w x₁ x₂ : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx₁ : m.Adj v x₁ ∧ x₁ ∉ Bs) (hx₂ : m.Adj v x₂ ∧ x₂ ∉ Bs)
    (heq : childOf e hv x₁ = childOf e hv x₂) : x₁ = x₂ := by
  have hpaths :
      e.toEquiv ⟨[v, x₁], obs_pair m hv hx₁.1 hx₁.2⟩ =
        e.toEquiv ⟨[v, x₂], obs_pair m hv hx₂.1 hx₂.2⟩ := by
    apply Subtype.ext
    rw [pair_image e hv hx₁, pair_image e hv hx₂, heq]
  have hsource := e.toEquiv.injective hpaths
  have hlist := congrArg Subtype.val hsource
  simpa using congrArg (fun p : List V => p.getLast?) hlist

/-- Every target entry comes from a source entry. -/
lemma childOf_surjective {m : MoleculeGraph V} {Bs Bt : List V} {v w y : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hy : m.Adj w y ∧ y ∉ Bt) :
    ∃ x, m.Adj v x ∧ x ∉ Bs ∧ childOf e hv x = y := by
  let q := e.toEquiv.symm ⟨[w, y], obs_pair m (by
    have hp := (e.toEquiv ⟨[v], obs_singleton m hv⟩).2
    have hsing := singleton_image e hv
    exact hp.outside w (by rw [hsing]; simp)) hy.1 hy.2⟩
  have hlen : q.1.length = 2 := by
    have := e.length_eq q
    simpa [q] using this.symm
  have hhead : q.1.head? = some v := q.2.head
  have hchain : BondedChain m q.1 := q.2.chain
  cases hq : q.1 with
  | nil => simp [hq] at hlen
  | cons a rest =>
      cases rest with
      | nil => simp [hq] at hlen
      | cons x tail =>
          have ha : a = v := by simpa [hq] using hhead
          have htail : tail = [] := by
            have : (a :: x :: tail).length = 2 := by simpa [hq] using hlen
            simp at this
            exact this
          subst a
          subst tail
          have hchain' : 0 < m.bond v x := by simpa [BondedChain, hq] using hchain
          have hadj : m.Adj v x := by exact hchain'
          have hxB : x ∉ Bs := q.2.outside x (by simp [hq])
          have hqsub : q = ⟨[v, x], obs_pair m hv hadj hxB⟩ := by
            apply Subtype.ext
            simpa [hq]
          have hpair := pair_image e hv ⟨hadj, hxB⟩
          have hpair' : (e.toEquiv q).1 = [w, childOf e hv x] := by
            rw [hqsub]
            exact hpair
          have hsourceImage : e.toEquiv q = ⟨[w, y], obs_pair m (by
              have hp := (e.toEquiv ⟨[v], obs_singleton m hv⟩).2
              have hsing := singleton_image e hv
              exact hp.outside w (by rw [hsing]; simp)) hy.1 hy.2⟩ := by
            simp [q]
          have hEqImg : [w, childOf e hv x] = [w, y] := by
            calc
              [w, childOf e hv x] = (e.toEquiv q).1 := hpair'.symm
              _ = [w, y] := congrArg Subtype.val hsourceImage
          have hxy := congrArg (fun p : List V => p[1]?) hEqImg
          have : some (childOf e hv x) = some y := by simpa using hxy
          exact ⟨x, hadj, hxB, Option.some.inj this⟩

/-- The length-two part of a full path equivalence is a bijection of the deleted-entry
neighbor sets. -/
noncomputable def childEntryEquiv {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) :
    {x // m.Adj v x ∧ x ∉ Bs} ≃ {y // m.Adj w y ∧ y ∉ Bt} := by
  classical
  let f : {x // m.Adj v x ∧ x ∉ Bs} → {y // m.Adj w y ∧ y ∉ Bt} := fun x =>
    ⟨childOf e hv x.1, childOf_adj e hv x.2⟩
  have hinj : Function.Injective f := by
    intro x₁ x₂ h
    apply Subtype.ext
    apply childOf_injective e hv x₁.2 x₂.2
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hAdj, hOutside, hImage⟩ := childOf_surjective e hv y.2
    exact ⟨⟨x, hAdj, hOutside⟩, Subtype.ext hImage⟩
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

lemma target_root_outside {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs) : w ∉ Bt := by
  have hp := (e.toEquiv ⟨[v], obs_singleton m hv⟩).2
  have hsing := singleton_image e hv
  exact hp.outside w (by rw [hsing]; simp)

lemma childOf_symm_left {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs) :
    childOf (e.symm) (target_root_outside e hv) (childOf e hv x) = x := by
  let y := childOf e hv x
  have hy := childOf_adj e hv hx
  have hpair := pair_image e hv hx
  have hp : e.toEquiv ⟨[v, x], obs_pair m hv hx.1 hx.2⟩ =
      ⟨[w, y], obs_pair m (target_root_outside e hv) hy.1 hy.2⟩ := by
    apply Subtype.ext
    simpa [y] using hpair
  have hinv := congrArg e.toEquiv.symm hp
  have hback := pair_image e.symm (target_root_outside e hv) hy
  have hlist : [v, childOf (e.symm) (target_root_outside e hv) y] = [v, x] := by
    calc
      [v, childOf (e.symm) (target_root_outside e hv) y] =
          (e.symm.toEquiv ⟨[w, y], obs_pair m (target_root_outside e hv) hy.1 hy.2⟩).1 := hback.symm
      _ = [v, x] := by
        have hvEq : e.toEquiv.symm ⟨[w, y], obs_pair m (target_root_outside e hv) hy.1 hy.2⟩ =
            ⟨[v, x], obs_pair m hv hx.1 hx.2⟩ := by
          simpa [ResidualPathTreeEquiv.symm] using hinv.symm
        exact congrArg Subtype.val hvEq
  have h := congrArg (fun p : List V => p[1]?) hlist
  have : some (childOf (e.symm) (target_root_outside e hv) y) = some x := by simpa using h
  simpa [y] using Option.some.inj this

lemma childPathMap_surjective {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs) :
    Function.Surjective (childPathMap e hv hx) := by
  intro qTarget
  let y := childOf e hv x
  have hw := target_root_outside e hv
  have hy := childOf_adj e hv hx
  let qBack := childPathMap (e.symm) hw hy qTarget
  have hroot : childOf (e.symm) hw y = x := by
    simpa [y] using childOf_symm_left e hv hx
  let qSource : {q : List V // ResidualObsPath m (Bs ++ [v]) x q} :=
    ⟨qBack.1, by simpa [y, hroot] using qBack.2⟩
  let pTarget : {p : List V // ResidualObsPath m Bt w p} :=
    ⟨w :: qTarget.1, obs_cons_child m hw hy.1 hy.2 qTarget.2⟩
  let pSource : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: qSource.1, obs_cons_child m hv hx.1 hx.2 qSource.2⟩
  have hback := childPathMap_parent_image (e.symm) hw hy qTarget
  have hpre : e.symm.toEquiv pTarget = pSource := by
    apply Subtype.ext
    exact hback
  have hmain : e.toEquiv pSource = pTarget := by
    have h := congrArg e.toEquiv hpre
    simpa [pTarget, pSource, ResidualPathTreeEquiv.symm] using h.symm
  have hfwd := childPathMap_parent_image e hv hx qSource
  have hfull : w :: (childPathMap e hv hx qSource).1 = w :: qTarget.1 := by
    calc
      w :: (childPathMap e hv hx qSource).1 = (e.toEquiv pSource).1 := hfwd.symm
      _ = pTarget.1 := congrArg Subtype.val hmain
      _ = w :: qTarget.1 := rfl
  have htail := List.cons.inj hfull
  exact ⟨qSource, by apply Subtype.ext; exact htail.2⟩


/-- The restricted branch maps are bijections: every target child history is obtained by
applying the original F to its deleted-entry prefix and taking the tail. -/
noncomputable def childPathEquiv {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs) :
    {q : List V // ResidualObsPath m (Bs ++ [v]) x q} ≃
      {q : List V // ResidualObsPath m (Bt ++ [w]) (childOf e hv x) q} :=
  Equiv.ofBijective (childPathMap e hv hx)
    ⟨childPathMap_injective e hv hx, childPathMap_surjective e hv hx⟩

lemma childPathMap_length {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    (childPathMap e hv hx q).1.length = q.1.length := by
  have hlen := e.length_eq ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  have hparent := childPathMap_parent_image e hv hx q
  have hqpos : 0 < q.1.length := List.length_pos_iff.mpr q.2.nonempty
  have hq : (v :: q.1).length = q.1.length + 1 := by simp
  have hr : (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).1.length =
      (childPathMap e hv hx q).1.length + 1 := by rw [hparent]; simp
  rw [hlen, hq] at hr
  omega


lemma getLast?_cons_eq_of_ne_nil {l : List V} {a : V} (hl : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => contradiction
  | cons b bs => simp

lemma childPathMap_terminal_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    pathTerminal (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).1
        (by intro h; have hn := (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).2.nonempty; exact hn h) =
      pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty := by
  have hcons := childPathMap_parent_image e hv hx q
  have hopt := congrArg List.getLast? hcons
  have hparent := List.getLast?_eq_some_getLast
    (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).2.nonempty
  have hchild := List.getLast?_eq_some_getLast (childPathMap e hv hx q).2.nonempty
  have htail := getLast?_cons_eq_of_ne_nil (a := w) (childPathMap e hv hx q).2.nonempty
  have hs : some (pathTerminal (e.toEquiv ⟨v :: q.1,
      obs_cons_child m hv hx.1 hx.2 q.2⟩).1
        (by intro h; have hn := (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).2.nonempty; exact hn h)) =
      some (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) := by
    calc
      _ = (e.toEquiv ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩).1.getLast? := hparent.symm
      _ = (w :: (childPathMap e hv hx q).1).getLast? := hopt
      _ = (childPathMap e hv hx q).1.getLast? := htail
      _ = _ := hchild
  exact Option.some.inj hs

lemma childSource_terminal_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    pathTerminal (v :: q.1) (by simp) = pathTerminal q.1 q.2.nonempty :=
  pathTerminal_cons_ne v q.1 q.2.nonempty

lemma get_append_singleton_left {l : List V} {a : V} {i : Nat}
    (hi : i < l.length) :
    (l ++ [a]).get ⟨i, by simp; omega⟩ = l.get ⟨i, hi⟩ := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_left]

lemma get_append_singleton_at_length {l : List V} {a : V} :
    (l ++ [a]).get ⟨l.length, by simp⟩ = a := by
  rw [List.get_eq_getElem, List.getElem_append_right] <;> simp

lemma childPathMap_dropLast_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) (hq : 1 < q.1.length) :
    (childPathMap e hv hx ⟨q.1.dropLast, obs_dropLast m q.2 hq⟩).1 =
      (childPathMap e hv hx q).1.dropLast := by
  let qd : {q : List V // ResidualObsPath m (Bs ++ [v]) x q} :=
    ⟨q.1.dropLast, obs_dropLast m q.2 hq⟩
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  let pd : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: qd.1, obs_cons_child m hv hx.1 hx.2 qd.2⟩
  have hp : 1 < p.1.length := by simp [p]; omega
  have hdrop :
      (⟨p.1.dropLast, obs_dropLast m p.2 hp⟩ :
        {p : List V // ResidualObsPath m Bs v p}) = pd := by
    apply Subtype.ext
    cases hqList : q.1 with
    | nil => simp [hqList] at hq
    | cons a rest => simp [p, pd, qd, hqList]
  have hparent := e.dropLast_eq p hp
  have hmap : (e.toEquiv pd).1 = (e.toEquiv p).1.dropLast := by
    calc
      (e.toEquiv pd).1 =
          (e.toEquiv ⟨p.1.dropLast, obs_dropLast m p.2 hp⟩).1 := by
            exact congrArg Subtype.val (congrArg e.toEquiv hdrop.symm)
      _ = (e.toEquiv p).1.dropLast := hparent
  have hlenOut : 1 < (childPathMap e hv hx q).1.length := by
    rw [childPathMap_length]
    exact hq
  have hdropCons :
      (w :: (childPathMap e hv hx q).1).dropLast =
        w :: (childPathMap e hv hx q).1.dropLast := by
    cases hc : (childPathMap e hv hx q).1 with
    | nil => simp [hc] at hlenOut
    | cons a rest => simp [hc]
  have hcons : w :: (childPathMap e hv hx qd).1 =
      w :: (childPathMap e hv hx q).1.dropLast := by
    calc
      w :: (childPathMap e hv hx qd).1 = (e.toEquiv pd).1 :=
        (childPathMap_parent_image e hv hx qd).symm
      _ = (e.toEquiv p).1.dropLast := hmap
      _ = (w :: (childPathMap e hv hx q).1).dropLast := by
        rw [childPathMap_parent_image e hv hx q]
      _ = w :: (childPathMap e hv hx q).1.dropLast := hdropCons
  exact (List.cons.inj hcons).2

lemma childPathMap_ancestorBond_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q})
    (i : Nat) (hi : i + 2 < q.1.length) :
    m.bond (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty)
        ((childPathMap e hv hx q).1.get ⟨i,
          (childPathMap_length e hv hx q).symm ▸ nat_index_lt_of_add hi⟩) =
      m.bond (pathTerminal q.1 q.2.nonempty) (q.1.get ⟨i, nat_index_lt_of_add hi⟩) := by
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  have htermT := childPathMap_terminal_eq e hv hx q
  have htermS := childSource_terminal_eq e hv hx q
  have hpidx : i + 1 + 2 < p.1.length := by simpa [p] using hi
  have hout : i < (childPathMap e hv hx q).1.length := by
    rw [childPathMap_length e hv hx q]
    exact nat_index_lt_of_add hi
  have hb := e.ancestorBond_eq p (i + 1) hpidx
  have htargetIdx :
      (e.toEquiv p).1.get ⟨i + 1, nat_image_index_lt (e.length_eq p) hpidx⟩ =
        (childPathMap e hv hx q).1.get ⟨i, hout⟩ := by
    have h := List.get_of_eq (childPathMap_parent_image e hv hx q)
      ⟨i + 1, nat_image_index_lt (e.length_eq p) hpidx⟩
    simpa using h
  have hsourceIdx : p.1.get ⟨i + 1, by simp [p]; omega⟩ =
      q.1.get ⟨i, nat_index_lt_of_add hi⟩ := by
    simpa [p] using (List.get_cons_succ (a := v) (as := q.1))
  calc
    m.bond (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty)
        ((childPathMap e hv hx q).1.get ⟨i, hout⟩) =
      m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty)
        ((childPathMap e hv hx q).1.get ⟨i, hout⟩) :=
      congrArg (fun z => m.bond z ((childPathMap e hv hx q).1.get ⟨i, hout⟩)) htermT.symm
    _ = m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty)
        ((e.toEquiv p).1.get ⟨i + 1, nat_image_index_lt (e.length_eq p) hpidx⟩) := by
      rw [htargetIdx]
    _ = m.bond (pathTerminal p.1 p.2.nonempty) (p.1.get ⟨i + 1,
        by simp [p]; omega⟩) := hb
    _ = m.bond (pathTerminal q.1 q.2.nonempty) (q.1.get ⟨i, nat_index_lt_of_add hi⟩) := by
      rw [hsourceIdx]
      exact congrArg (fun z => m.bond z (q.1.get ⟨i, nat_index_lt_of_add hi⟩)) htermS

lemma childPathMap_parentBond_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) (hq : 1 < q.1.length) :
    m.bond (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty)
        ((childPathMap e hv hx q).1.get ⟨q.1.length - 2,
          (childPathMap_length e hv hx q).symm ▸ nat_parent_index_lt hq⟩) =
      m.bond (pathTerminal q.1 q.2.nonempty)
        (q.1.get ⟨q.1.length - 2, nat_parent_index_lt hq⟩) := by
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  let j := q.1.length - 2
  have htermT := childPathMap_terminal_eq e hv hx q
  have htermS := childSource_terminal_eq e hv hx q
  have hqj : j + 1 < q.1.length := by dsimp [j]; omega
  have hq0 : j < q.1.length := by omega
  have hpj : j + 1 < p.1.length := by simp [p, j]; omega
  have hparentIdx : p.1.length - 2 = j + 1 := by simp [p, j]; omega
  have himgIdx : (e.toEquiv p).1.length - 2 = j + 1 := by
    rw [e.length_eq p]
    simp [p, j]
    omega
  have htargetBound : j + 1 < (e.toEquiv p).1.length := by
    rw [e.length_eq p]
    exact hpj
  have hsourceBound : j + 1 < p.1.length := hpj
  have htargetIdx :
      (e.toEquiv p).1.get ⟨j + 1, htargetBound⟩ =
        (childPathMap e hv hx q).1.get ⟨j,
          (childPathMap_length e hv hx q).symm ▸ hq0⟩ := by
    have h := List.get_of_eq (childPathMap_parent_image e hv hx q)
      ⟨j + 1, htargetBound⟩
    simpa using h
  have hsourceIdx : p.1.get ⟨j + 1, by simpa [p] using hpj⟩ =
      q.1.get ⟨j, hq0⟩ := by
    simpa [p] using (List.get_cons_succ (a := v) (as := q.1))
  have hb := e.parentBond_eq p (by simp [p]; omega)
  have hb' : m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty)
        ((e.toEquiv p).1.get ⟨j + 1, htargetBound⟩) =
      m.bond (pathTerminal p.1 p.2.nonempty) (p.1.get ⟨j + 1, by simpa [p] using hpj⟩) := by
    simpa [hparentIdx, himgIdx] using hb
  calc
    m.bond (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty)
        ((childPathMap e hv hx q).1.get ⟨j,
          (childPathMap_length e hv hx q).symm ▸ hq0⟩) =
      m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty)
        ((childPathMap e hv hx q).1.get ⟨j,
          (childPathMap_length e hv hx q).symm ▸ hq0⟩) :=
      congrArg (fun z => m.bond z _) htermT.symm
    _ = m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty)
        ((e.toEquiv p).1.get ⟨j + 1, htargetBound⟩) := by rw [htargetIdx]
    _ = m.bond (pathTerminal p.1 p.2.nonempty)
        (p.1.get ⟨j + 1, by simpa [p] using hpj⟩) := hb'
    _ = m.bond (pathTerminal q.1 q.2.nonempty) (q.1.get ⟨j, hq0⟩) := by
      rw [hsourceIdx]
      exact congrArg (fun z => m.bond z (q.1.get ⟨j, hq0⟩)) htermS

lemma childPathMap_boundaryBond_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q})
    (i : Nat) (hi : i < (Bs ++ [v]).length) :
    m.bond (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty)
        ((Bt ++ [w]).get ⟨i, by simpa [List.length_append, e.len_eq] using hi⟩) =
      m.bond (pathTerminal q.1 q.2.nonempty)
        ((Bs ++ [v]).get ⟨i, hi⟩) := by
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  have hterm := childPathMap_terminal_eq e hv hx q
  have hle : i ≤ Bs.length := by simpa using hi
  by_cases hold : i < Bs.length
  · have htarget : i < Bt.length := e.len_eq ▸ hold
    rw [← hterm, ← childSource_terminal_eq e hv hx q,
      get_append_singleton_left htarget, get_append_singleton_left hold]
    simpa [p] using e.boundaryBond_eq p i hold
  · have heq : i = Bs.length := by omega
    subst i
    have hbound : Bs.length < (Bt ++ [w]).length := by
      rw [List.length_append, ← e.len_eq]
      simp
    have hidx : (⟨Bs.length, hbound⟩ : Fin (Bt ++ [w]).length) =
        ⟨Bt.length, by simp⟩ := by
      apply Fin.ext
      exact e.len_eq
    rw [hidx, get_append_singleton_at_length, get_append_singleton_at_length]
    by_cases hq : q.1.length = 1
    · have hp : 1 < p.1.length := by simp [p, hq]
      have hb := e.parentBond_eq p hp
      have hplen : p.1.length = 2 := by simp [p, hq]
      have hrlen : (e.toEquiv p).1.length = 2 := by rw [e.length_eq p, hplen]
      have ht0 : (e.toEquiv p).1.get ⟨0, List.length_pos_iff.mpr (e.toEquiv p).2.nonempty⟩ = w := by
        have hh := (e.toEquiv p).2.head
        have hhead := List.head?_eq_some_head (e.toEquiv p).2.nonempty
        rw [List.get_mk_zero (List.length_pos_iff.mpr (e.toEquiv p).2.nonempty)]
        exact Option.some.inj (hhead.symm.trans hh)
      have hs0 : p.1.get ⟨0, by simp [p]⟩ = v := by simp [p, List.get_cons_zero]
      have hb0 : m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty)
          ((e.toEquiv p).1.get ⟨0, List.length_pos_iff.mpr (e.toEquiv p).2.nonempty⟩) =
          m.bond (pathTerminal p.1 p.2.nonempty) (p.1.get ⟨0, by simp [p]⟩) := by
        simpa [hplen, hrlen] using hb
      calc
        m.bond (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) w =
            m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty) w :=
          congrArg (fun z => m.bond z w) (childPathMap_terminal_eq e hv hx q).symm
        _ = m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty)
            ((e.toEquiv p).1.get ⟨0, List.length_pos_iff.mpr (e.toEquiv p).2.nonempty⟩) := by rw [ht0]
        _ = m.bond (pathTerminal p.1 p.2.nonempty) (p.1.get ⟨0, by simp [p]⟩) := hb0
        _ = m.bond (pathTerminal q.1 q.2.nonempty) v := by
          rw [hs0]
          exact congrArg (fun z => m.bond z v) (childSource_terminal_eq e hv hx q)
    · have hq2 : 1 < q.1.length := by
        have hqpos : 0 < q.1.length := List.length_pos_iff.mpr q.2.nonempty
        omega
      have hp : 2 < p.1.length := by simp [p]; omega
      have hb := e.ancestorBond_eq p 0 (by simpa [p] using hp)
      have himgpos : 0 < (e.toEquiv p).1.length :=
        List.length_pos_iff.mpr (e.toEquiv p).2.nonempty
      have ht0 : (e.toEquiv p).1.get ⟨0, himgpos⟩ = w := by
        rw [List.get_mk_zero himgpos]
        have hh := (e.toEquiv p).2.head
        have hhead := List.head?_eq_some_head (e.toEquiv p).2.nonempty
        exact Option.some.inj (hhead.symm.trans hh)
      have hs0 : p.1.get ⟨0, by simp [p]⟩ = v := by simp [p, List.get_cons_zero]
      calc
        m.bond (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) w =
            m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty) w :=
          congrArg (fun z => m.bond z w) (childPathMap_terminal_eq e hv hx q).symm
        _ = m.bond (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty)
            ((e.toEquiv p).1.get ⟨0, List.length_pos_iff.mpr (e.toEquiv p).2.nonempty⟩) := by rw [ht0]
        _ = m.bond (pathTerminal p.1 p.2.nonempty) (p.1.get ⟨0, by simp [p]⟩) := hb
        _ = m.bond (pathTerminal q.1 q.2.nonempty) v := by
          rw [hs0]
          exact congrArg (fun z => m.bond z v) (childSource_terminal_eq e hv hx q)

lemma childPathMap_atomZ_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    m.atomZ (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) =
      m.atomZ (pathTerminal q.1 q.2.nonempty) := by
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  calc
    m.atomZ (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) =
        m.atomZ (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty) :=
      congrArg m.atomZ (childPathMap_terminal_eq e hv hx q).symm
    _ = m.atomZ (pathTerminal p.1 p.2.nonempty) := e.atomZ_eq p
    _ = m.atomZ (pathTerminal q.1 q.2.nonempty) :=
      congrArg m.atomZ (childSource_terminal_eq e hv hx q)

lemma childPathMap_atomMass_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    m.atomMass (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) =
      m.atomMass (pathTerminal q.1 q.2.nonempty) := by
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  calc
    m.atomMass (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) =
        m.atomMass (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty) :=
      congrArg m.atomMass (childPathMap_terminal_eq e hv hx q).symm
    _ = m.atomMass (pathTerminal p.1 p.2.nonempty) := e.atomMass_eq p
    _ = m.atomMass (pathTerminal q.1 q.2.nonempty) :=
      congrArg m.atomMass (childSource_terminal_eq e hv hx q)

lemma childPathMap_formalCharge_eq {m : MoleculeGraph V} {Bs Bt : List V} {v w x : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs)
    (q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q}) :
    m.formalCharge (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) =
      m.formalCharge (pathTerminal q.1 q.2.nonempty) := by
  let p : {p : List V // ResidualObsPath m Bs v p} :=
    ⟨v :: q.1, obs_cons_child m hv hx.1 hx.2 q.2⟩
  calc
    m.formalCharge (pathTerminal (childPathMap e hv hx q).1 (childPathMap e hv hx q).2.nonempty) =
        m.formalCharge (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty) :=
      congrArg m.formalCharge (childPathMap_terminal_eq e hv hx q).symm
    _ = m.formalCharge (pathTerminal p.1 p.2.nonempty) := e.formalCharge_eq p
    _ = m.formalCharge (pathTerminal q.1 q.2.nonempty) :=
      congrArg m.formalCharge (childSource_terminal_eq e hv hx q)

/-- Full residual observations restrict to a matched child entry without replacing the
original path equivalence. The equivalence on every child history is exactly `F(v :: q).tail`.
-/
noncomputable def childResidualPathTreeEquiv {m : MoleculeGraph V} {Bs Bt : List V}
    {v w x : V} (e : ResidualPathTreeEquiv m Bs Bt v w) (hv : v ∉ Bs)
    (hx : m.Adj v x ∧ x ∉ Bs) :
    ResidualPathTreeEquiv m (Bs ++ [v]) (Bt ++ [w]) x (childOf e hv x) where
  len_eq := by simpa [List.length_append, e.len_eq]
  toEquiv := childPathEquiv e hv hx
  length_eq := by
    intro q
    exact childPathMap_length e hv hx q
  dropLast_eq := by
    intro q hq
    exact childPathMap_dropLast_eq e hv hx q hq
  atomZ_eq := by
    intro q
    exact childPathMap_atomZ_eq e hv hx q
  atomMass_eq := by
    intro q
    exact childPathMap_atomMass_eq e hv hx q
  formalCharge_eq := by
    intro q
    exact childPathMap_formalCharge_eq e hv hx q
  boundaryBond_eq := by
    intro q i hi
    exact childPathMap_boundaryBond_eq e hv hx q i hi
  ancestorBond_eq := by
    intro q i hi
    exact childPathMap_ancestorBond_eq e hv hx q i hi
  parentBond_eq := by
    intro q hq
    simpa [childPathEquiv, Equiv.ofBijective, childPathMap_length] using
      childPathMap_parentBond_eq e hv hx q hq

/-! ## Attachment counts and finite component matching -/

def neighborOutside (m : MoleculeGraph V) (B : List V) (v : V) : Finset V :=
  (m.neighborFinset v).filter fun x => x ∉ B

def touchedComponents (m : MoleculeGraph V) (B : List V) (v : V) :
    Finset (residualGraph m (B ++ [v])).ConnectedComponent :=
  (neighborOutside m B v).image fun x =>
    (residualGraph m (B ++ [v])).connectedComponentMk x

def entryFinset (m : MoleculeGraph V) (B : List V) (v : V)
    (c : (residualGraph m (B ++ [v])).ConnectedComponent) : Finset V :=
  (neighborOutside m B v).filter fun x =>
    (residualGraph m (B ++ [v])).connectedComponentMk x = c

def entryCard (m : MoleculeGraph V) (B : List V) (v : V)
    (c : (residualGraph m (B ++ [v])).ConnectedComponent) : Nat :=
  (entryFinset m B v c).card

lemma neighborOutside_mem (m : MoleculeGraph V) (B : List V) (v x : V) :
    x ∈ neighborOutside m B v ↔ m.Adj v x ∧ x ∉ B := by
  simp [neighborOutside, MoleculeGraph.mem_neighborFinset]

lemma entryFinset_mem (m : MoleculeGraph V) (B : List V) (v : V)
    (c : (residualGraph m (B ++ [v])).ConnectedComponent) (x : V) :
    x ∈ entryFinset m B v c ↔
      m.Adj v x ∧ x ∉ B ∧ (residualGraph m (B ++ [v])).connectedComponentMk x = c := by
  simp [entryFinset, neighborOutside_mem, and_assoc]

/-- A boundary-preserving child component iso preserves the number of neighbors attached to
its deleted parent. This is the fiber-cardinality fact used by the normalized Hall mass. -/
theorem entryCard_eq_of_childIso
    {m : MoleculeGraph V} {Bs Bt : List V} {v w x y : V}
    (iso : BoundaryComponentIso m (Bs ++ [v]) (Bt ++ [w]) x y)
    (hx : m.Adj v x ∧ x ∉ Bs) :
    entryCard m Bs v ((residualGraph m (Bs ++ [v])).connectedComponentMk x) =
      entryCard m Bt w ((residualGraph m (Bt ++ [w])).connectedComponentMk y) := by
  classical
  let E := {z // m.Adj v z ∧ z ∉ Bs}
  let F := {z // m.Adj w z ∧ z ∉ Bt}
  let ownerE : E → (residualGraph m (Bs ++ [v])).ConnectedComponent :=
    fun z => (residualGraph m (Bs ++ [v])).connectedComponentMk z.1
  let ownerF : F → (residualGraph m (Bt ++ [w])).ConnectedComponent :=
    fun z => (residualGraph m (Bt ++ [w])).connectedComponentMk z.1
  let xE : E := ⟨x, hx⟩
  let hxout : x ∉ Bs ++ [v] := by
    rw [not_mem_append_singleton]
    exact ⟨hx.2, ne_comm.mp (ne_of_adj m hx.1)⟩
  let yRooted := componentEntryEquiv iso ⟨x, ⟨inComponent_self m hxout, hx.1⟩⟩
  have hy : yRooted.1 = y := iso.entry
  have hyout0 : yRooted.1 ∉ Bt ++ [w] := inComponent_not_mem m yRooted.2.1
  have hyout : y ∉ Bt ++ [w] := by simpa [hy] using hyout0
  have hyAdj : m.Adj w y := by simpa [hy] using yRooted.2.2
  let yF : F := ⟨y, ⟨hyAdj, (not_mem_append_singleton.mp hyout).1⟩⟩
  have hcard : Fintype.card {z : E // ownerE z = ownerE xE} =
      Fintype.card {z : F // ownerF z = ownerF yF} := by
    exact Fintype.card_congr (componentOwnerFiberEquiv iso hx)
  have hsrc : Fintype.card {z : E // ownerE z = ownerE xE} =
      entryCard m Bs v (ownerE xE) := by
    let s := entryFinset m Bs v (ownerE xE)
    let f : {z : E // ownerE z = ownerE xE} → {z : V // z ∈ s} := fun z => by
      have hz := (entryFinset_mem m Bs v (ownerE xE) z.1.1).2
        ⟨z.1.2.1, z.1.2.2, z.2⟩
      exact ⟨z.1.1, by simpa [s] using hz⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact (congrArg (fun q : {z : V // z ∈ s} => q.1) h)
      · intro z
        have hz := (entryFinset_mem m Bs v (ownerE xE) z.1).1 (by simpa [s] using z.2)
        refine ⟨⟨⟨z.1, hz.1, hz.2.1⟩, ?_⟩, ?_⟩
        · exact hz.2.2
        · apply Subtype.ext
          rfl
    calc
      Fintype.card {z : E // ownerE z = ownerE xE} = Fintype.card {z : V // z ∈ s} :=
        Fintype.card_congr (Equiv.ofBijective f hf)
      _ = s.card := Fintype.card_coe s
      _ = entryCard m Bs v (ownerE xE) := rfl
  have htgt : Fintype.card {z : F // ownerF z = ownerF yF} =
      entryCard m Bt w (ownerF yF) := by
    let s := entryFinset m Bt w (ownerF yF)
    let f : {z : F // ownerF z = ownerF yF} → {z : V // z ∈ s} := fun z => by
      have hz := (entryFinset_mem m Bt w (ownerF yF) z.1.1).2
        ⟨z.1.2.1, z.1.2.2, z.2⟩
      exact ⟨z.1.1, by simpa [s] using hz⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact (congrArg (fun q : {z : V // z ∈ s} => q.1) h)
      · intro z
        have hz := (entryFinset_mem m Bt w (ownerF yF) z.1).1 (by simpa [s] using z.2)
        refine ⟨⟨⟨z.1, hz.1, hz.2.1⟩, ?_⟩, ?_⟩
        · exact hz.2.2
        · apply Subtype.ext
          rfl
    calc
      Fintype.card {z : F // ownerF z = ownerF yF} = Fintype.card {z : V // z ∈ s} :=
        Fintype.card_congr (Equiv.ofBijective f hf)
      _ = s.card := Fintype.card_coe s
      _ = entryCard m Bt w (ownerF yF) := rfl
  rw [← hsrc, hcard, htgt]

lemma entryCard_pos_of_touched (m : MoleculeGraph V) (B : List V) (v : V)
    {c : (residualGraph m (B ++ [v])).ConnectedComponent}
    (hc : c ∈ touchedComponents m B v) : 0 < entryCard m B v c := by
  unfold entryCard
  refine Finset.card_pos.mpr ?_
  simp [touchedComponents] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  refine ⟨x, ?_⟩
  simp [entryFinset, hx]

lemma entryFinset_disjoint (m : MoleculeGraph V) (B : List V) (v : V)
    {c d : (residualGraph m (B ++ [v])).ConnectedComponent} (hcd : c ≠ d) :
    Disjoint (entryFinset m B v c) (entryFinset m B v d) := by
  rw [Finset.disjoint_left]
  intro x hx hd
  have hc := (entryFinset_mem m B v c x).1 hx
  have hd' := (entryFinset_mem m B v d x).1 hd
  exact hcd (hc.2.2.symm.trans hd'.2.2)

lemma neighborOutside_biUnion (m : MoleculeGraph V) (B : List V) (v : V) :
    neighborOutside m B v =
      (touchedComponents m B v).biUnion (entryFinset m B v) := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(residualGraph m (B ++ [v])).connectedComponentMk x, ?_, ?_⟩
    · change (residualGraph m (B ++ [v])).connectedComponentMk x ∈
        (neighborOutside m B v).image fun y =>
          (residualGraph m (B ++ [v])).connectedComponentMk y
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · rw [entryFinset_mem]
      rw [neighborOutside_mem] at hx
      exact ⟨hx.1, hx.2, rfl⟩
  · intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨c, hc, hentry⟩ := hx
    rw [entryFinset_mem] at hentry
    rw [neighborOutside_mem]
    exact ⟨hentry.1, hentry.2.1⟩

lemma card_neighborOutside (m : MoleculeGraph V) (B : List V) (v : V) :
    (neighborOutside m B v).card =
      ∑ c ∈ touchedComponents m B v, entryCard m B v c := by
  rw [neighborOutside_biUnion]
  unfold entryCard
  refine Finset.card_biUnion ?_
  intro c hc d hd hcd
  exact entryFinset_disjoint m B v hcd

/- The finite Hall construction below is adapted from
`Mathlib/Combinatorics/Hall/Finite.lean` (Apache 2.0, copyright 2021 Alena Gusakov,
Bhavik Mehta, and Kyle Miller). It is kept local because the shared Mathlib build cache
does not contain that module and is read-only. -/
namespace HallMarriageTheorem

open Finset
universe u v

variable {ι : Type u} {α : Type v} [DecidableEq α] {t : ι → Finset α}

section Fintype

variable [Fintype ι]

theorem hall_cond_of_erase {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t))
    (s' : Finset { x' : ι | x' ≠ x }) : #s' ≤ #(s'.biUnion fun x' => (t x').erase a) := by
  haveI := Classical.decEq ι
  specialize ha (s'.image fun z => z.1)
  rw [image_nonempty, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases! he : s'.Nonempty
  · have ha' : #s' < #(s'.biUnion fun x => t x) := by
      convert ha he fun h => by simpa [← h] using mem_univ x using 2
      ext x
      simp only [mem_image, mem_biUnion, SetCoe.exists, exists_and_right,
        exists_eq_right]
    rw [← erase_biUnion]
    by_cases hb : a ∈ s'.biUnion fun x => t x
    · rw [card_erase_of_mem hb]
      exact Nat.le_sub_one_of_lt ha'
    · rw [erase_eq_of_notMem hb]
      exact Nat.le_of_lt ha'
  · subst s'
    simp

/-- First case of the inductive step: assuming that
`∀ (s : Finset ι), s.Nonempty → s ≠ univ → #s < #(s.biUnion t)`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
theorem hall_hard_inductive_step_A {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos _)
  haveI := Classical.decEq ι
  -- Choose an arbitrary element `x : ι` and `y : t x`.
  let x := Classical.arbitrary ι
  have tx_ne : (t x).Nonempty := by
    rw [← Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ ≤ #(.biUnion {x} t) := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]
  choose y hy using tx_ne
  -- Restrict to everything except `x` and `y`.
  let ι' := { x' : ι | x' ≠ x }
  let t' : ι' → Finset α := fun x' => (t x').erase y
  have card_ι' : Fintype.card ι' = n :=
    calc
      Fintype.card ι' = Fintype.card ι - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]
  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩
  -- Extend the resulting function.
  refine ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, ?_, ?_⟩
  · rintro z₁ z₂
    have key : ∀ {x}, y ≠ f' x := by
      intro x h
      simpa [t', ← h] using hfr x
    by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x <;>
      simp [h₁, h₂, hfinj.eq_iff, key, key.symm]
  · intro z
    simp only
    split_ifs with hz
    · rwa [hz]
    · specialize hfr ⟨z, hz⟩
      rw [mem_erase] at hfr
      exact hfr.2

theorem hall_cond_of_restrict {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (s' : Finset (s : Set ι)) :
    #s' ≤ #(s'.biUnion fun a' => t a') := by
  classical
    rw [← card_image_of_injective s' Subtype.coe_injective]
    convert ht (s'.image fun z => z.1) using 1
    apply congr_arg
    ext y
    simp

theorem hall_cond_of_compl {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (hus : #s = #(s.biUnion t)) (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (s' : Finset (sᶜ : Set ι)) : #s' ≤ #(s'.biUnion fun x' => t x' \ s.biUnion t) := by
  haveI := Classical.decEq ι
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, SetCoe.exists, exists_and_right,
      exists_eq_right]
    intro x hx hc _
    exact absurd hx hc
  have : #s' = #(s ∪ s'.image fun z => z.1) - #s := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective, Nat.add_sub_cancel_left]
  rw [this, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [← card_sdiff_of_subset]
  · gcongr
    intro t
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
      exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs
    · exact False.elim <| (hs x) <| And.intro hx rat
    · use x', hx', rat, hs
  · apply biUnion_subset_biUnion_of_subset_left
    apply subset_union_left

/-- Second case of the inductive step: assuming that
`∃ (s : Finset ι), s ≠ univ → #s = #(s.biUnion t)`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
theorem hall_hard_inductive_step_B {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (s : Finset ι) (hs : s.Nonempty) (hns : s ≠ univ) (hus : #s = #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  haveI := Classical.decEq ι
  -- Restrict to `s`
  rw [Nat.add_one] at hn
  have card_ι'_le : Fintype.card s ≤ n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = #s := Fintype.card_coe _
      _ < Fintype.card ι := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s → Finset α := fun x' => t x'
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩
  -- Restrict to `sᶜ` in the domain and `(s.biUnion t)ᶜ` in the codomain.
  set ι'' := (s : Set ι)ᶜ
  let t'' : ι'' → Finset α := fun a'' => t a'' \ s.biUnion t
  have card_ι''_le : Fintype.card ι'' ≤ n := by
    simp_rw [ι'', ← Nat.lt_succ_iff, ← hn, ← Finset.coe_compl, coe_sort_coe]
    rwa [Fintype.card_coe, card_compl_lt_iff_nonempty]
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩
  -- Put them together
  have f''_notMem_biUnion : ∀ (x'') (hx'' : x'' ∉ s), f'' ⟨x'', hx''⟩ ∉ s.biUnion t := by
    intro x'' hx''
    have h := hsf'' ⟨x'', hx''⟩
    rw [mem_sdiff] at h
    exact h.2
  have im_disj :
      ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : x'' ∉ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩ := by
    grind
  refine ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, ?_, ?_⟩
  · refine hf'.dite _ hf'' (@fun x x' => im_disj x x' _ _)
  · intro x
    simp only
    split_ifs with h
    · exact hsf' ⟨x, h⟩
    · exact sdiff_subset (hsf'' ⟨x, h⟩)

end Fintype

variable [Finite ι]

/-- Here we combine the two inductive steps into a full strong induction proof,
completing the proof the harder direction of **Hall's Marriage Theorem**.
-/
theorem hall_hard_inductive (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  generalize hn : Fintype.card ι = m
  induction m using Nat.strongRecOn generalizing ι with | ind n ih => _
  rcases n with (_ | n)
  · rw [Fintype.card_eq_zero_iff] at hn
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  · have ih' : ∀ (ι' : Type u) [Fintype ι'] (t' : ι' → Finset α), Fintype.card ι' ≤ n →
        (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
        ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
      intro ι' _ _ hι' ht'
      exact ih _ (Nat.lt_succ_of_le hι') ht' _ rfl
    by_cases! h : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)
    · refine hall_hard_inductive_step_A hn ht (@fun ι' => ih' ι') h
    · rcases h with ⟨s, sne, snu, sle⟩
      exact hall_hard_inductive_step_B hn ht (@fun ι' => ih' ι')
        s sne snu (Nat.le_antisymm (ht _) sle)

end HallMarriageTheorem

/-- Finite Hall matching on a prescribed finite source set. -/
theorem exists_reps_of_card_le_biUnion {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (t : α → Finset β)
    (hall : ∀ X : Finset α, X ⊆ S → X.card ≤ (X.biUnion t).card) :
    ∃ f : {a // a ∈ S} → β, Function.Injective f ∧ ∀ a, f a ∈ t a.1 := by
  classical
  let t' : {a // a ∈ S} → Finset β := fun a => t a.1
  have hall' : ∀ X : Finset {a // a ∈ S}, X.card ≤ (X.biUnion t').card := by
    intro X
    let Y := X.image (fun a => a.1)
    have hsub : Y ⊆ S := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
      exact a.2
    have hcard : Y.card = X.card := by
      apply Finset.card_image_of_injective
      intro a b hab
      exact Subtype.ext hab
    have hunion : Y.biUnion t = X.biUnion t' := by
      ext y
      simp [Y, t']
    rw [← hcard, ← hunion]
    exact hall Y hsub
  exact HallMarriageTheorem.hall_hard_inductive hall'

/-- A normalized incidence mass: each source and target component carries total mass one,
and mass is supported only on actual entry matches.  The entry construction below the
component induction supplies this data by assigning mass `1 / k` to each matched entry pair. -/
structure NormalizedEntryMass (A B : Type*) [Fintype A] [Fintype B]
    (neighbors : A → Finset B) where
  mass : A → B → ℚ
  nonneg : ∀ a b, 0 ≤ mass a b
  row_sum : ∀ a, (∑ b : B, mass a b) = 1
  column_sum : ∀ b, (∑ a : A, mass a b) = 1
  support : ∀ a b, mass a b ≠ 0 → b ∈ neighbors a

theorem normalized_entry_mass_card_eq {A B : Type*} [Fintype A] [Fintype B]
    {neighbors : A → Finset B} (M : NormalizedEntryMass A B neighbors) : Fintype.card A = Fintype.card B := by
  classical
  have hmass : (Fintype.card A : ℚ) = Fintype.card B := by
    calc
      (Fintype.card A : ℚ) = ∑ a : A, (1 : ℚ) := by simp
      _ = ∑ a : A, ∑ b : B, M.mass a b := by simp_rw [M.row_sum]
      _ = ∑ b : B, ∑ a : A, M.mass a b := Finset.sum_comm
      _ = ∑ b : B, (1 : ℚ) := by simp_rw [M.column_sum]
      _ = Fintype.card B := by simp
  exact_mod_cast hmass

/-- Components reached by entries paired with an entry of `a`. -/
def entryNeighbors {E F A B : Type*} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F] [DecidableEq A] [DecidableEq B]
    (ownerE : E → A) (ownerF : F → B) (entryEquiv : E ≃ F) (a : A) : Finset B :=
  (Finset.univ.filter fun x => ownerE x = a).image fun x => ownerF (entryEquiv x)

/-- Matched entry count from `a` to `b`. -/
def entryPairCount {E F A B : Type*} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F] [DecidableEq A] [DecidableEq B]
    (ownerE : E → A) (ownerF : F → B) (entryEquiv : E ≃ F) (a : A) (b : B) : Nat :=
  ((Finset.univ.filter fun x => ownerE x = a).filter fun x => ownerF (entryEquiv x) = b).card

/-- A bijection between two owner fibers proves the entry-count equality needed for normalized
mass. This is the abstract counting interface consumed by the recursive component isomorphisms. -/
theorem owner_fiber_card_eq_of_equiv
    {E F A B : Type*} [Fintype E] [Fintype F] [DecidableEq A] [DecidableEq B]
    (ownerE : E → A) (ownerF : F → B) (x : E) (y : F)
    (fiberEquiv : {z : E // ownerE z = ownerE x} ≃
      {z : F // ownerF z = ownerF y}) :
    (Finset.univ.filter fun z : E => ownerE z = ownerE x).card =
      (Finset.univ.filter fun z : F => ownerF z = ownerF y).card := by
  classical
  calc
    (Finset.univ.filter fun z : E => ownerE z = ownerE x).card =
        Fintype.card {z : E // ownerE z = ownerE x} := by
          symm
          simpa using (Fintype.card_subtype (fun z : E => ownerE z = ownerE x))
    _ = Fintype.card {z : F // ownerF z = ownerF y} := Fintype.card_congr fiberEquiv
    _ = (Finset.univ.filter fun z : F => ownerF z = ownerF y).card := by
          simpa using (Fintype.card_subtype (fun z : F => ownerF z = ownerF y))

/-- The entry-equivalence construction of the normalized incidence mass. The only coherence
required is equality of the positive entry-fiber sizes along each matched pair. -/
noncomputable def normalizedEntryMass_of_entryEquiv
    {E F A B : Type*} [Fintype E] [Fintype F] [Fintype A] [Fintype B]
    [DecidableEq E] [DecidableEq F] [DecidableEq A] [DecidableEq B]
    (ownerE : E → A) (ownerF : F → B) (entryEquiv : E ≃ F)
    (hEpos : ∀ a, 0 < (Finset.univ.filter fun x => ownerE x = a).card)
    (hFpos : ∀ b, 0 < (Finset.univ.filter fun y => ownerF y = b).card)
    (hFiber : ∀ x : E,
      (Finset.univ.filter fun z => ownerE z = ownerE x).card =
        (Finset.univ.filter fun y => ownerF y = ownerF (entryEquiv x)).card) :
    NormalizedEntryMass A B (entryNeighbors ownerE ownerF entryEquiv) := by
  classical
  let kE (a : A) := (Finset.univ.filter fun x => ownerE x = a).card
  let kF (b : B) := (Finset.univ.filter fun y => ownerF y = b).card
  refine ⟨fun a b => (entryPairCount ownerE ownerF entryEquiv a b : ℚ) *
      (kE a : ℚ)⁻¹, ?_, ?_, ?_, ?_⟩
  · intro a b
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le (entryPairCount ownerE ownerF entryEquiv a b)
    · positivity
  · intro a
    have hcounts :
        (∑ b : B, entryPairCount ownerE ownerF entryEquiv a b) = kE a := by
      simp [entryPairCount, kE, Finset.sum_card_fiberwise_eq_card_filter]
    have hcast :
        (∑ b : B, (entryPairCount ownerE ownerF entryEquiv a b : ℚ)) = (kE a : ℚ) := by
      exact_mod_cast hcounts
    calc
      (∑ b : B, (entryPairCount ownerE ownerF entryEquiv a b : ℚ) * (kE a : ℚ)⁻¹) =
          (∑ b : B, (entryPairCount ownerE ownerF entryEquiv a b : ℚ)) * (kE a : ℚ)⁻¹ := by
            rw [← Finset.sum_mul]
      _ = (kE a : ℚ) * (kE a : ℚ)⁻¹ := by rw [hcast]
      _ = 1 := by
        have hkpos : 0 < (kE a : ℚ) := by exact_mod_cast hEpos a
        exact mul_inv_cancel₀ (ne_of_gt hkpos)
  · intro b
    let Eb := Finset.univ.filter fun x : E => ownerF (entryEquiv x) = b
    have hcounts :
        (∑ a : A, entryPairCount ownerE ownerF entryEquiv a b) = kF b := by
      have hsplit :
          (∑ a : A, (Eb.filter fun x => ownerE x = a).card) = Eb.card := by
        simpa [Eb, kF] using
          (Finset.sum_card_fiberwise_eq_card_filter Eb Finset.univ ownerE)
      have hcountEq (a : A) : entryPairCount ownerE ownerF entryEquiv a b =
          (Eb.filter fun x => ownerE x = a).card := by
        simp [entryPairCount, Eb, Finset.filter_filter, and_comm]
      rw [Finset.sum_congr rfl fun a _ => hcountEq a, hsplit]
      have himage : Eb.image entryEquiv = Finset.univ.filter fun y : F => ownerF y = b := by
        ext y
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, hx, hxy⟩
          subst y
          exact (Finset.mem_filter.mp hx).2
        · intro hy
          refine ⟨entryEquiv.symm y, ?_, entryEquiv.apply_symm_apply y⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Eb] using hy⟩
      have hcard := Finset.card_image_of_injective Eb entryEquiv.injective
      rw [himage] at hcard
      simpa [kF] using hcard.symm
    have hdenom : ∀ a, entryPairCount ownerE ownerF entryEquiv a b ≠ 0 → kE a = kF b := by
      intro a hcount
      have hpos : 0 < entryPairCount ownerE ownerF entryEquiv a b := Nat.pos_of_ne_zero hcount
      have hx : ∃ x : E, ownerE x = a ∧ ownerF (entryEquiv x) = b := by
        obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
        rcases Finset.mem_filter.mp hx with ⟨hinner, hxb⟩
        rcases Finset.mem_filter.mp hinner with ⟨_, hxa⟩
        exact ⟨x, hxa, hxb⟩
      obtain ⟨x, hxa, hxb⟩ := hx
      simpa [kE, kF, hxa, hxb] using hFiber x
    have hterm (a : A) :
        (entryPairCount ownerE ownerF entryEquiv a b : ℚ) * (kE a : ℚ)⁻¹ =
          (entryPairCount ownerE ownerF entryEquiv a b : ℚ) * (kF b : ℚ)⁻¹ := by
      by_cases hc : entryPairCount ownerE ownerF entryEquiv a b = 0
      · simp [hc]
      · rw [hdenom a hc]
    have hcast :
        (∑ a : A, (entryPairCount ownerE ownerF entryEquiv a b : ℚ)) = (kF b : ℚ) := by
      exact_mod_cast hcounts
    calc
      (∑ a : A, (entryPairCount ownerE ownerF entryEquiv a b : ℚ) * (kE a : ℚ)⁻¹) =
          (∑ a : A, (entryPairCount ownerE ownerF entryEquiv a b : ℚ) * (kF b : ℚ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hterm a
      _ = (∑ a : A, (entryPairCount ownerE ownerF entryEquiv a b : ℚ)) * (kF b : ℚ)⁻¹ := by
            rw [← Finset.sum_mul]
      _ = (kF b : ℚ) * (kF b : ℚ)⁻¹ := by rw [hcast]
      _ = 1 := by
        have hkpos : 0 < (kF b : ℚ) := by exact_mod_cast hFpos b
        exact mul_inv_cancel₀ (ne_of_gt hkpos)
  · intro a b hmass
    have hcount : entryPairCount ownerE ownerF entryEquiv a b ≠ 0 := by
      intro hz
      simp [hz] at hmass
    have hpos : 0 < entryPairCount ownerE ownerF entryEquiv a b := Nat.pos_of_ne_zero hcount
    have hx : ∃ x : E, ownerE x = a ∧ ownerF (entryEquiv x) = b := by
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by simpa [entryPairCount] using hpos)
      rcases Finset.mem_filter.mp hx with ⟨hinner, hxb⟩
      rcases Finset.mem_filter.mp hinner with ⟨_, hxa⟩
      exact ⟨x, hxa, hxb⟩
    obtain ⟨x, hxa, hxb⟩ := hx
    change b ∈ (Finset.univ.filter fun y => ownerE y = a).image
      (fun y => ownerF (entryEquiv y))
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, hxb⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxa⟩

/-- A normalized entry mass satisfies Hall's inequality on every finite family of components.
This is the finite weighted-counting step used to match deleted-root components without asking
the entry equivalence itself to descend to a component map. -/
theorem normalized_entry_mass_hall {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (neighbors : A → Finset B)
    (M : NormalizedEntryMass A B neighbors) (X : Finset A) :
    X.card ≤ (X.biUnion neighbors).card := by
  classical
  let N := X.biUnion neighbors
  have hrowN (a : A) (ha : a ∈ X) : (∑ b ∈ N, M.mass a b) = 1 := by
    calc
      (∑ b ∈ N, M.mass a b) = ∑ b : B, M.mass a b := by
        apply Finset.sum_subset (Finset.subset_univ N)
        intro b hb hnot
        have hzero : M.mass a b = 0 := by
          by_contra hne
          have hmem := M.support a b hne
          exact hnot (Finset.mem_biUnion.mpr ⟨a, ha, hmem⟩)
        exact hzero
      _ = 1 := M.row_sum a
  have hcolX (b : B) (hb : b ∈ N) : (∑ a ∈ X, M.mass a b) ≤ 1 := by
    calc
      (∑ a ∈ X, M.mass a b) ≤ ∑ a : A, M.mass a b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ X)
        intro a ha hnot
        exact M.nonneg a b
      _ = 1 := M.column_sum b
  have hmass : (X.card : ℚ) ≤ (N.card : ℚ) := by
    calc
      (X.card : ℚ) = ∑ a ∈ X, (1 : ℚ) := by simp
      _ = ∑ a ∈ X, ∑ b ∈ N, M.mass a b := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (hrowN a ha).symm
      _ = ∑ b ∈ N, ∑ a ∈ X, M.mass a b := Finset.sum_comm
      _ ≤ ∑ b ∈ N, (1 : ℚ) := Finset.sum_le_sum fun b hb => hcolX b hb
      _ = (N.card : ℚ) := by simp
  exact_mod_cast hmass

/-- Turn a normalized incidence mass into the ordinary finite Hall matching.  Each selected
component is paired with a component sharing at least one matched entry. -/
theorem exists_component_matching_of_normalized_entry_mass
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (neighbors : A → Finset B) (M : NormalizedEntryMass A B neighbors) :
    ∃ f : A → B, Function.Injective f ∧ ∀ a, f a ∈ neighbors a := by
  classical
  have hall : ∀ X : Finset A, X ⊆ Finset.univ → X.card ≤ (X.biUnion neighbors).card := by
    intro X _
    exact normalized_entry_mass_hall neighbors M X
  obtain ⟨f, hinj, hmem⟩ :=
    exists_reps_of_card_le_biUnion (Finset.univ : Finset A) neighbors hall
  refine ⟨fun a => f ⟨a, Finset.mem_univ _⟩, ?_, ?_⟩
  · intro a b hab
    exact congrArg Subtype.val (hinj hab)
  · intro a
    exact hmem ⟨a, Finset.mem_univ _⟩


/-- A full entry bijection with positive owner fibers and equal fiber sizes across each matched
entry induces an injective component matching. Every selected component pair is witnessed by a
specific matched entry. -/
theorem exists_component_injection_of_entryEquiv
    {E F A B : Type*} [Fintype E] [Fintype F] [Fintype A] [Fintype B]
    [DecidableEq E] [DecidableEq F] [DecidableEq A] [DecidableEq B]
    (ownerE : E → A) (ownerF : F → B) (entryEquiv : E ≃ F)
    (hEpos : ∀ a, 0 < (Finset.univ.filter fun x => ownerE x = a).card)
    (hFpos : ∀ b, 0 < (Finset.univ.filter fun y => ownerF y = b).card)
    (hFiber : ∀ x : E,
      (Finset.univ.filter fun z => ownerE z = ownerE x).card =
        (Finset.univ.filter fun y => ownerF y = ownerF (entryEquiv x)).card) :
    ∃ f : A → B, Function.Injective f ∧
      ∀ a, ∃ x : E, ownerE x = a ∧ ownerF (entryEquiv x) = f a := by
  classical
  let N := entryNeighbors ownerE ownerF entryEquiv
  let M := normalizedEntryMass_of_entryEquiv ownerE ownerF entryEquiv hEpos hFpos hFiber
  obtain ⟨f, hinj, hmem⟩ := exists_component_matching_of_normalized_entry_mass N M
  refine ⟨f, hinj, ?_⟩
  intro a
  have himage : f a ∈ N a := hmem a
  change f a ∈ (Finset.univ.filter fun x => ownerE x = a).image
    (fun x => ownerF (entryEquiv x)) at himage
  obtain ⟨x, hx, hxb⟩ := Finset.mem_image.mp himage
  exact ⟨x, (Finset.mem_filter.mp hx).2, hxb⟩


/-- Equal positive entry fibers turn the normalized-entry matching into a component
bijection, with a concrete matched entry witnessing every paired component. -/
theorem exists_component_bijection_of_entryEquiv
    {E F A B : Type*} [Fintype E] [Fintype F] [Fintype A] [Fintype B]
    [DecidableEq E] [DecidableEq F] [DecidableEq A] [DecidableEq B]
    (ownerE : E → A) (ownerF : F → B) (entryEquiv : E ≃ F)
    (hEpos : ∀ a, 0 < (Finset.univ.filter fun x => ownerE x = a).card)
    (hFpos : ∀ b, 0 < (Finset.univ.filter fun y => ownerF y = b).card)
    (hFiber : ∀ x : E,
      (Finset.univ.filter fun z => ownerE z = ownerE x).card =
        (Finset.univ.filter fun y => ownerF y = ownerF (entryEquiv x)).card) :
    ∃ f : A ≃ B,
      ∀ a, ∃ x : E, ownerE x = a ∧ ownerF (entryEquiv x) = f a := by
  classical
  let N := entryNeighbors ownerE ownerF entryEquiv
  let M := normalizedEntryMass_of_entryEquiv ownerE ownerF entryEquiv hEpos hFpos hFiber
  obtain ⟨g, hginj, hwitness⟩ :=
    exists_component_injection_of_entryEquiv ownerE ownerF entryEquiv hEpos hFpos hFiber
  have hcard : Fintype.card A = Fintype.card B := normalized_entry_mass_card_eq M
  have hgbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).2 ⟨hginj, hcard⟩
  refine ⟨Equiv.ofBijective g hgbij, ?_⟩
  intro a
  simpa [Equiv.ofBijective] using hwitness a


end

end TetraStereo.OneCenter.RetainedCoherentSymmetry

assert_kernel_only TetraStereo.OneCenter.RetainedCoherentSymmetry.ResidualPathTreeEquiv.symm
assert_kernel_only TetraStereo.OneCenter.RetainedCoherentSymmetry.childEntryEquiv
assert_kernel_only TetraStereo.OneCenter.RetainedCoherentSymmetry.childResidualPathTreeEquiv
assert_kernel_only TetraStereo.OneCenter.RetainedCoherentSymmetry.componentOwnerFiberEquiv
assert_kernel_only TetraStereo.OneCenter.RetainedCoherentSymmetry.entryCard_eq_of_childIso
assert_kernel_only TetraStereo.OneCenter.RetainedCoherentSymmetry.normalizedEntryMass_of_entryEquiv
assert_kernel_only TetraStereo.OneCenter.RetainedCoherentSymmetry.exists_component_bijection_of_entryEquiv
