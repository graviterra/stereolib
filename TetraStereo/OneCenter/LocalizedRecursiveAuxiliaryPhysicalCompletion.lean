import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalInverse
import TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness
import TetraStereo.OneCenter.LocalizedPhysicalDomainReindexing
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# A hidden bridgehead parity: the general inverse fails on the intended domain

The formal input `C(H)(Cl)(X_A)(X_B)` has two cage arms (15 atoms, single bonds,
two four-membered-ring cages):

```
atom   0  1  2   3   4  5  6  7  8   9  10 11 12 13 14
       C  H  Cl  C1A H  O  O  O  C3A C1B H  O  O  O  C3B
```

Bonds: `0-1, 0-2, 0-3, 0-9`; cage A `3-{5,6,7}, 8-{5,6,7}, 8-4`; cage B `9-{11,12,13},
14-{11,12,13}, 14-10`. The detected centers are `0, 3, 8, 9, 14`; there are no terminal twins.

**Actual side.** At a bridgehead `C3X` reached along `0, C1X, O, C3X`, the swap of the two other
bridge oxygens fixes the history and its residual component is one oxygen: a proper refusal
witness. At `C1X` the 3-cycle of the bridges is even at `C3X`: again a proper refusal witness.
Hence every occurrence in both arms is refused, the arm swap makes every read covariant without a
sign law, and the root keys of the two arms are equal (`referenceState_none_of_blindArms`).

**Physical side.** Any automorphism fixing the root and carrying `C1A` to `C1B` acts on the
bridge slots of `C1A` and `C3A` by the same permutation, so `s(C1A)·s(C3A)` is invariant under both
proper and mirror branch transport (`not_branchTransport_of_parityCoupling`). The coordinates put
the hydrogen of cage B on the root side of its bridge plane, so the two arms carry different
invariants. This graph and these coordinates satisfy the repository's stated domain predicates.
Physical realizability of this short cage is not established. In/out isomerism is a related
chemical concept requiring sufficiently long bridges (IUPAC Blue Book P-94.3.2.6); that source
does not establish realizability of this input.

This module records the graph data and the reader-free refusal witnesses.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.CartesianPoint3

/-! ## The source -/

def oxygen : SemanticAtom := { element := element 8 (by decide) (by decide) }

def point (x y z : ℚ) : CartesianPoint3 := { x := x, y := y, z := z }

def P0 : CartesianPoint3 := point 0 0 0
def P1 : CartesianPoint3 := point 0 0 1
def P2 : CartesianPoint3 := point 0 1 0
def P3 : CartesianPoint3 := point 2 0 0
def P4 : CartesianPoint3 := point 5 0 0
def P5 : CartesianPoint3 := point 3 1 0
def P6 : CartesianPoint3 := point 3 (-1) 1
def P7 : CartesianPoint3 := point 3 (-1) (-1)
def P8 : CartesianPoint3 := point 4 0 0
def P9 : CartesianPoint3 := point (-2) 0 0
/-- The hydrogen of cage B points into the cage, on the root side of its bridge plane. -/
def P10 : CartesianPoint3 := point (-5 / 2) 0 0
def P11 : CartesianPoint3 := point (-3) 1 0
def P12 : CartesianPoint3 := point (-3) (-1) 1
def P13 : CartesianPoint3 := point (-3) (-1) (-1)
def P14 : CartesianPoint3 := point (-4) 0 0

def positions : List CartesianPoint3 :=
  [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13, P14]

def cageSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, hydrogen, chlorine, carbon, hydrogen, oxygen, oxygen, oxygen, carbon,
          carbon, hydrogen, oxygen, oxygen, oxygen, carbon]
        interactions :=
          [singleBond 0 1, singleBond 0 2, singleBond 0 3, singleBond 0 9,
            singleBond 3 5, singleBond 3 6, singleBond 3 7, singleBond 4 8,
            singleBond 5 8, singleBond 6 8, singleBond 7 8,
            singleBond 9 11, singleBond 9 12, singleBond 9 13, singleBond 10 14,
            singleBond 11 14, singleBond 12 14, singleBond 13 14] }
    spatial? := some { positions := positions } }

theorem source_structurallyWellFormed : cageSource.structurallyWellFormed? = true := by
  decide +kernel

theorem source_graphReady : cageSource.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

theorem source_spatiallyWellFormed : cageSource.SpatialIndicesWellFormed := by
  change positions.length = 15
  decide +kernel

def cageAuthority : CertifiedAuthoritativeChemicalInput :=
  { input := cageSource
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff cageSource).mp
        source_structurallyWellFormed }

def cageCertified : CertifiedLocalizedCIPInput :=
  { certified := cageAuthority
    graphReady := (cageSource.molecule.localizedCIPGraphReady?_eq_true_iff).mp source_graphReady }

theorem atomCount_eq : cageSource.molecule.atomCount = 15 := rfl

abbrev graph : MoleculeGraph (Fin 15) := cageCertified.moleculeGraph

theorem simple_bonded : graph.SimpleBonded := by
  intro left right adjacent
  fin_cases left <;> fin_cases right <;> first
    | exact absurd adjacent (by decide)
    | decide

theorem degree_four_iff (atom : Fin 15) :
    atom ∈ graph.tetrahedralCenterSet ↔
      atom = 0 ∨ atom = 3 ∨ atom = 8 ∨ atom = 9 ∨ atom = 14 := by
  fin_cases atom <;> decide

/-! ## Simple paths through a bicyclic cage -/

section Paths

variable {V : Type*}

private theorem mem_of_getLast {α : Type*} : ∀ {l : List α} {a : α}, l.getLast? = some a → a ∈ l
  | [], _, h => by simp at h
  | [_], a, h => by
      simp at h
      simp [h]
  | _ :: y :: rest, _, h => by
      rw [List.getLast?_cons_cons] at h
      exact List.mem_cons_of_mem _ (mem_of_getLast (l := y :: rest) h)

/-- Neighbourhood data of a cage `r — c1 <(o₁,o₂,o₃)> c3 — h` seen from the outer atom `r`. -/
structure Cage (adj : V → V → Prop) (r c1 c3 h : V) (os : List V) : Prop where
  c1_adj : ∀ x, adj c1 x → x = r ∨ x ∈ os
  c3_adj : ∀ x, adj c3 x → x = h ∨ x ∈ os
  o_adj : ∀ o ∈ os, ∀ x, adj o x → x = c1 ∨ x = c3
  h_adj : ∀ x, adj h x → x = c3
  r_c1 : r ≠ c1
  r_c3 : r ≠ c3
  r_h : r ≠ h
  r_os : r ∉ os
  c1_os : c1 ∉ os
  c3_os : c3 ∉ os
  h_os : h ∉ os

variable {adj : V → V → Prop} {r c1 c3 h : V} {os : List V}

/-- A simple bonded history from `r` ending at the attachment bridgehead is `[c1, r]`. -/
theorem Cage.history_c1 (cage : Cage adj r c1 c3 h os) {l : List V} (nodup : l.Nodup)
    (chain : l.IsChain adj) (head : l.head? = some c1) (last : l.getLast? = some r) :
    l = [c1, r] := by
  match l, nodup, chain, head, last with
  | [], _, _, head, _ => simp at head
  | [a], _, _, head, last =>
      simp only [List.head?_cons, Option.some.injEq] at head
      simp only [List.getLast?_singleton, Option.some.injEq] at last
      exact absurd (last.symm.trans head) cage.r_c1
  | a :: b :: t, nodup, chain, head, last =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      have hab := (List.isChain_cons_cons.1 chain).1
      rcases cage.c1_adj b hab with rfl | hb
      · cases t with
        | nil => rfl
        | cons y t' =>
            exfalso
            rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at last
            exact (List.nodup_cons.1 (List.nodup_cons.1 nodup).2).1 (mem_of_getLast last)
      · exfalso
        cases t with
        | nil =>
            simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at last
            exact cage.r_os (last ▸ hb)
        | cons y t' =>
            have chain' := (List.isChain_cons_cons.1 chain).2
            have hby := (List.isChain_cons_cons.1 chain').1
            rcases cage.o_adj b hb y hby with rfl | rfl
            · simp at nodup
            · cases t' with
              | nil =>
                  simp only [List.getLast?_cons_cons, List.getLast?_singleton,
                    Option.some.injEq] at last
                  exact cage.r_c3 last.symm
              | cons w t'' =>
                  have chain'' := (List.isChain_cons_cons.1 chain').2
                  have hyw := (List.isChain_cons_cons.1 chain'').1
                  rcases cage.c3_adj w hyw with rfl | hw
                  · cases t'' with
                    | nil =>
                        simp only [List.getLast?_cons_cons, List.getLast?_singleton,
                          Option.some.injEq] at last
                        exact cage.r_h last.symm
                    | cons v t3 =>
                        have hwv := (List.isChain_cons_cons.1
                          (List.isChain_cons_cons.1 chain'').2).1
                        rw [cage.h_adj v hwv] at nodup
                        simp at nodup
                  · cases t'' with
                    | nil =>
                        simp only [List.getLast?_cons_cons, List.getLast?_singleton,
                          Option.some.injEq] at last
                        exact cage.r_os (last ▸ hw)
                    | cons v t3 =>
                        have hwv := (List.isChain_cons_cons.1
                          (List.isChain_cons_cons.1 chain'').2).1
                        rcases cage.o_adj w hw v hwv with rfl | rfl <;> simp at nodup

/-- A simple bonded history from `r` ending at the far bridgehead is `[c3, o, c1, r]` for one
bridge `o`. -/
theorem Cage.history_c3 (cage : Cage adj r c1 c3 h os) {l : List V} (nodup : l.Nodup)
    (chain : l.IsChain adj) (head : l.head? = some c3) (last : l.getLast? = some r) :
    ∃ o ∈ os, l = [c3, o, c1, r] := by
  match l, nodup, chain, head, last with
  | [], _, _, head, _ => simp at head
  | [a], _, _, head, last =>
      simp only [List.head?_cons, Option.some.injEq] at head
      simp only [List.getLast?_singleton, Option.some.injEq] at last
      exact absurd (last.symm.trans head) cage.r_c3
  | a :: b :: t, nodup, chain, head, last =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      have hab := (List.isChain_cons_cons.1 chain).1
      have chain' := (List.isChain_cons_cons.1 chain).2
      rcases cage.c3_adj b hab with rfl | hb
      · exfalso
        cases t with
        | nil =>
            simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at last
            exact cage.r_h last.symm
        | cons y t' =>
            have hby := (List.isChain_cons_cons.1 chain').1
            rw [cage.h_adj y hby] at nodup
            simp at nodup
      · cases t with
        | nil =>
            exfalso
            simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at last
            exact cage.r_os (last ▸ hb)
        | cons y t' =>
            have hby := (List.isChain_cons_cons.1 chain').1
            have chain'' := (List.isChain_cons_cons.1 chain').2
            rcases cage.o_adj b hb y hby with rfl | rfl
            · cases t' with
              | nil =>
                  exfalso
                  simp only [List.getLast?_cons_cons, List.getLast?_singleton,
                    Option.some.injEq] at last
                  exact cage.r_c1 last.symm
              | cons w t'' =>
                  have hyw := (List.isChain_cons_cons.1 chain'').1
                  rcases cage.c1_adj w hyw with rfl | hw
                  · cases t'' with
                    | nil => exact ⟨b, hb, rfl⟩
                    | cons v t3 =>
                        exfalso
                        rw [List.getLast?_cons_cons, List.getLast?_cons_cons,
                          List.getLast?_cons_cons, List.getLast?_cons_cons] at last
                        exact (List.nodup_cons.1 (List.nodup_cons.1
                          (List.nodup_cons.1 (List.nodup_cons.1 nodup).2).2).2).1
                          (mem_of_getLast last)
                  · exfalso
                    cases t'' with
                    | nil =>
                        simp only [List.getLast?_cons_cons, List.getLast?_singleton,
                          Option.some.injEq] at last
                        exact cage.r_os (last ▸ hw)
                    | cons v t3 =>
                        have hwv := (List.isChain_cons_cons.1
                          (List.isChain_cons_cons.1 chain'').2).1
                        rcases cage.o_adj w hw v hwv with rfl | rfl <;> simp at nodup
            · simp at nodup

end Paths

/-! ## Residual components -/

theorem inComponent_closed {V : Type*} [Fintype V] [DecidableEq V] (G : MoleculeGraph V)
    (B : List V) (S : V → Prop)
    (closed : ∀ a b, S a → a ∉ B → b ∉ B → G.Adj a b → S b) {v x : V}
    (component : RetainedCoherentSymmetry.InComponent G B v x) (start : S v) : S x := by
  obtain ⟨-, ⟨walk⟩⟩ := component
  revert start
  induction walk with
  | nil => exact id
  | cons edge _ ih => exact fun start => ih (closed _ _ start edge.1 edge.2.1 edge.2.2)

/-! ## Explicit automorphisms -/

def armSwapFun (atom : Fin 15) : Fin 15 :=
  if h₁ : 3 ≤ atom.val then
    if h₂ : atom.val ≤ 8 then ⟨atom.val + 6, by omega⟩
    else ⟨atom.val - 6, by have := atom.isLt; omega⟩
  else atom

private theorem armSwap_involutive : Function.Involutive armSwapFun := by
  intro atom
  fin_cases atom <;> rfl

def armSwapPerm : Equiv.Perm (Fin 15) where
  toFun := armSwapFun
  invFun := armSwapFun
  left_inv := armSwap_involutive
  right_inv := armSwap_involutive

theorem armSwap_isAutomorphism : graph.IsAutomorphism armSwapPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

def cycleAPerm : Equiv.Perm (Fin 15) := Equiv.swap 5 6 * Equiv.swap 6 7
def cycleBPerm : Equiv.Perm (Fin 15) := Equiv.swap 11 12 * Equiv.swap 12 13

theorem cycleA_isAutomorphism : graph.IsAutomorphism cycleAPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem cycleB_isAutomorphism : graph.IsAutomorphism cycleBPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap67_isAutomorphism : graph.IsAutomorphism (Equiv.swap 6 7) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap57_isAutomorphism : graph.IsAutomorphism (Equiv.swap 5 7) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap56_isAutomorphism : graph.IsAutomorphism (Equiv.swap 5 6) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap1213_isAutomorphism : graph.IsAutomorphism (Equiv.swap 12 13) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap1113_isAutomorphism : graph.IsAutomorphism (Equiv.swap 11 13) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap1112_isAutomorphism : graph.IsAutomorphism (Equiv.swap 11 12) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

def armSwap : graph.Aut := ⟨armSwapPerm, armSwap_isAutomorphism⟩
def cycleA : graph.Aut := ⟨cycleAPerm, cycleA_isAutomorphism⟩
def cycleB : graph.Aut := ⟨cycleBPerm, cycleB_isAutomorphism⟩

/-- The bridge swap fixing a given parent bridge of the far bridgehead. -/
def otherBridgeSwap (o : Fin 15) : graph.Aut :=
  if o = 5 then ⟨Equiv.swap 6 7, swap67_isAutomorphism⟩
  else if o = 6 then ⟨Equiv.swap 5 7, swap57_isAutomorphism⟩
  else if o = 7 then ⟨Equiv.swap 5 6, swap56_isAutomorphism⟩
  else if o = 11 then ⟨Equiv.swap 12 13, swap1213_isAutomorphism⟩
  else if o = 12 then ⟨Equiv.swap 11 13, swap1113_isAutomorphism⟩
  else ⟨Equiv.swap 11 12, swap1112_isAutomorphism⟩

/-! ## The physical molecule in sorted-neighbour slots -/

noncomputable section

open LocalizedRecursiveAuxiliaryPhysicalDomain LocalizedCyclicRootPhysicalSetup
open LocalizedRecursiveAuxiliaryPhysicalInverse
open scoped Classical

abbrev cageCanon : MultiCenterMolecule (Fin 15) :=
  cageCertified.canonicalDetectedMultiCenterMolecule

def k0 : cageCanon.Center := ⟨0, (degree_four_iff 0).mpr (by decide)⟩
def k3 : cageCanon.Center := ⟨3, (degree_four_iff 3).mpr (by decide)⟩
def k8 : cageCanon.Center := ⟨8, (degree_four_iff 8).mpr (by decide)⟩
def k9 : cageCanon.Center := ⟨9, (degree_four_iff 9).mpr (by decide)⟩
def k14 : cageCanon.Center := ⟨14, (degree_four_iff 14).mpr (by decide)⟩

theorem center_cases (c : cageCanon.Center) : c = k0 ∨ c = k3 ∨ c = k8 ∨ c = k9 ∨ c = k14 := by
  rcases (degree_four_iff c.1).mp c.2 with h | h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h))))

private theorem sorted_of_neighbors (center : Fin 15) (atoms : List (Fin 15))
    (nodup : atoms.Nodup) (pairwise : atoms.Pairwise (· ≤ ·))
    (members : ∀ atom : Fin 15, graph.Adj center atom ↔ atom ∈ atoms) :
    (graph.neighborFinset center).sort (· ≤ ·) = atoms := by
  have finsetEq : graph.neighborFinset center = atoms.toFinset := by
    ext atom
    simp only [MoleculeGraph.mem_neighborFinset, List.mem_toFinset]
    exact members atom
  rw [finsetEq]
  exact ((List.toFinset_sort (· ≤ ·) nodup).mpr pairwise)

private theorem ligand_of_sorted (center : cageCanon.Center) (sorted : List (Fin 15))
    (hlist : (cageCertified.moleculeGraph.neighborFinset center.1).sort (· ≤ ·) = sorted)
    (hlength : sorted.length = 4) (index : Fin 4) :
    cageCanon.ligandAtomAt center index = sorted.get (Fin.cast hlength.symm index) := by
  show cageCertified.canonicalLigandAtom center index = _
  unfold CertifiedLocalizedCIPInput.canonicalLigandAtom CertifiedLocalizedCIPInput.canonicalNeighborList
  simp [hlist]
  try rfl

private theorem sorted0 : (graph.neighborFinset 0).sort (· ≤ ·) = [1, 2, 3, 9] :=
  sorted_of_neighbors 0 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted3 : (graph.neighborFinset 3).sort (· ≤ ·) = [0, 5, 6, 7] :=
  sorted_of_neighbors 3 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted8 : (graph.neighborFinset 8).sort (· ≤ ·) = [4, 5, 6, 7] :=
  sorted_of_neighbors 8 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted9 : (graph.neighborFinset 9).sort (· ≤ ·) = [0, 11, 12, 13] :=
  sorted_of_neighbors 9 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted14 : (graph.neighborFinset 14).sort (· ≤ ·) = [10, 11, 12, 13] :=
  sorted_of_neighbors 14 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)

theorem lig0 : cageCanon.ligandAtomAt k0 0 = 1 ∧ cageCanon.ligandAtomAt k0 1 = 2 ∧
    cageCanon.ligandAtomAt k0 2 = 3 ∧ cageCanon.ligandAtomAt k0 3 = 9 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ligand_of_sorted k0 [1, 2, 3, 9] sorted0 rfl _
theorem lig3 : cageCanon.ligandAtomAt k3 0 = 0 ∧ cageCanon.ligandAtomAt k3 1 = 5 ∧
    cageCanon.ligandAtomAt k3 2 = 6 ∧ cageCanon.ligandAtomAt k3 3 = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ligand_of_sorted k3 [0, 5, 6, 7] sorted3 rfl _
theorem lig8 : cageCanon.ligandAtomAt k8 0 = 4 ∧ cageCanon.ligandAtomAt k8 1 = 5 ∧
    cageCanon.ligandAtomAt k8 2 = 6 ∧ cageCanon.ligandAtomAt k8 3 = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ligand_of_sorted k8 [4, 5, 6, 7] sorted8 rfl _
theorem lig9 : cageCanon.ligandAtomAt k9 0 = 0 ∧ cageCanon.ligandAtomAt k9 1 = 11 ∧
    cageCanon.ligandAtomAt k9 2 = 12 ∧ cageCanon.ligandAtomAt k9 3 = 13 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ligand_of_sorted k9 [0, 11, 12, 13] sorted9 rfl _
theorem lig14 : cageCanon.ligandAtomAt k14 0 = 10 ∧ cageCanon.ligandAtomAt k14 1 = 11 ∧
    cageCanon.ligandAtomAt k14 2 = 12 ∧ cageCanon.ligandAtomAt k14 3 = 13 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ligand_of_sorted k14 [10, 11, 12, 13] sorted14 rfl _

theorem lig0f : cageCanon.ligandAtomAt k0 = ![1, 2, 3, 9] := by
  funext i
  fin_cases i
  · exact lig0.1
  · exact lig0.2.1
  · exact lig0.2.2.1
  · exact lig0.2.2.2
theorem lig3f : cageCanon.ligandAtomAt k3 = ![0, 5, 6, 7] := by
  funext i
  fin_cases i
  · exact lig3.1
  · exact lig3.2.1
  · exact lig3.2.2.1
  · exact lig3.2.2.2
theorem lig8f : cageCanon.ligandAtomAt k8 = ![4, 5, 6, 7] := by
  funext i
  fin_cases i
  · exact lig8.1
  · exact lig8.2.1
  · exact lig8.2.2.1
  · exact lig8.2.2.2
theorem lig9f : cageCanon.ligandAtomAt k9 = ![0, 11, 12, 13] := by
  funext i
  fin_cases i
  · exact lig9.1
  · exact lig9.2.1
  · exact lig9.2.2.1
  · exact lig9.2.2.2
theorem lig14f : cageCanon.ligandAtomAt k14 = ![10, 11, 12, 13] := by
  funext i
  fin_cases i
  · exact lig14.1
  · exact lig14.2.1
  · exact lig14.2.2.1
  · exact lig14.2.2.2

/-! ### Coordinates and the calibrated configuration -/

def pos (atom : Fin 15) : CartesianPoint3 := positions[atom.val]'(by simp [positions])

theorem sourcePointAt (atom : Fin 15) : cageCertified.spatialPointAt? atom = some (pos atom) := by
  rw [cageCertified.spatialPointAt?_eq_some_iff]
  refine ⟨⟨positions⟩, rfl, ?_⟩
  change positions[atom.val]? = some _
  exact List.getElem?_eq_getElem (by simp [positions])

/-- Oriented volume of the four ligand positions in sorted-neighbour order. -/
def ligandVolume (c : cageCanon.Center) : ℚ :=
  orientedVolume (pos (cageCanon.ligandAtomAt c 0)) (pos (cageCanon.ligandAtomAt c 1))
    (pos (cageCanon.ligandAtomAt c 2)) (pos (cageCanon.ligandAtomAt c 3))

theorem volume0 : ligandVolume k0 = orientedVolume P1 P2 P3 P9 := by
  simp only [ligandVolume, lig0.1, lig0.2.1, lig0.2.2.1, lig0.2.2.2]
  rfl
theorem volume3 : ligandVolume k3 = orientedVolume P0 P5 P6 P7 := by
  simp only [ligandVolume, lig3.1, lig3.2.1, lig3.2.2.1, lig3.2.2.2]
  rfl
theorem volume8 : ligandVolume k8 = orientedVolume P4 P5 P6 P7 := by
  simp only [ligandVolume, lig8.1, lig8.2.1, lig8.2.2.1, lig8.2.2.2]
  rfl
theorem volume9 : ligandVolume k9 = orientedVolume P0 P11 P12 P13 := by
  simp only [ligandVolume, lig9.1, lig9.2.1, lig9.2.2.1, lig9.2.2.2]
  rfl
theorem volume14 : ligandVolume k14 = orientedVolume P10 P11 P12 P13 := by
  simp only [ligandVolume, lig14.1, lig14.2.1, lig14.2.2.1, lig14.2.2.2]
  rfl

theorem volume_ne_zero (c : cageCanon.Center) : ligandVolume c ≠ 0 := by
  rcases center_cases c with rfl | rfl | rfl | rfl | rfl
  · rw [volume0]; norm_num [orientedVolume, P1, P2, P3, P9, point]
  · rw [volume3]; norm_num [orientedVolume, P0, P5, P6, P7, point]
  · rw [volume8]; norm_num [orientedVolume, P4, P5, P6, P7, point]
  · rw [volume9]; norm_num [orientedVolume, P0, P11, P12, P13, point]
  · rw [volume14]; norm_num [orientedVolume, P10, P11, P12, P13, point]

/-- Cage A is out/out: its two bridgehead volumes have opposite signs. -/
theorem cageA_volumes : ligandVolume k3 * ligandVolume k8 < 0 := by
  rw [volume3, volume8]
  norm_num [orientedVolume, P0, P4, P5, P6, P7, point]

/-- Cage B carries an inner hydrogen: its two bridgehead volumes have equal signs. -/
theorem cageB_volumes : 0 < ligandVolume k9 * ligandVolume k14 := by
  rw [volume9, volume14]
  norm_num [orientedVolume, P0, P10, P11, P12, P13, point]

/-- The calibrated configuration: the sign of each center is the sign of its ligand volume. -/
def cageCfg : cageCanon.Configuration := fun c =>
  if ligandVolume c < 0 then Equiv.swap 0 1 else 1

theorem cfgSign (c : cageCanon.Center) :
    cageCanon.configurationSign cageCfg c = if ligandVolume c < 0 then -1 else 1 := by
  simp only [MultiCenterMolecule.configurationSign, cageCfg]
  split_ifs <;> simp

private theorem sign_mul_sign {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((if a < 0 then (-1 : ℝ) else 1) * (if b < 0 then (-1 : ℝ) else 1)) =
      if a * b < 0 then -1 else 1 := by
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · have : ¬ a * b < 0 := not_lt.mpr (mul_pos_of_neg_of_neg ha' hb').le
    simp [ha', hb', this]
  · have : a * b < 0 := mul_neg_of_neg_of_pos ha' hb'
    simp [ha', not_lt.mpr hb'.le, this]
  · have : a * b < 0 := mul_neg_of_pos_of_neg ha' hb'
    simp [not_lt.mpr ha'.le, hb', this]
  · have : ¬ a * b < 0 := not_lt.mpr (mul_pos ha' hb').le
    simp [not_lt.mpr ha'.le, not_lt.mpr hb'.le, this]

/-- **The hidden parity mismatch.** -/
theorem parity_mismatch :
    cageCanon.configurationSign cageCfg k3 * cageCanon.configurationSign cageCfg k8 ≠
      cageCanon.configurationSign cageCfg k9 * cageCanon.configurationSign cageCfg k14 := by
  rw [cfgSign, cfgSign, cfgSign, cfgSign, sign_mul_sign (volume_ne_zero k3) (volume_ne_zero k8),
    sign_mul_sign (volume_ne_zero k9) (volume_ne_zero k14), if_pos cageA_volumes,
    if_neg (not_lt.mpr cageB_volumes.le)]
  norm_num

theorem canonCoordinates (c : cageCanon.Center) :
    ActualPhysicalCalibratedCoordinates cageCertified cageCanon cageCfg c := by
  refine ⟨fun i => pos (cageCanon.ligandAtomAt c i), fun i => sourcePointAt _,
    volume_ne_zero c, ?_⟩
  show rationalVolumeSign (ligandVolume c) = _
  rw [cfgSign]
  split_ifs with negative
  · exact rationalVolumeSign_of_neg negative
  · exact rationalVolumeSign_of_pos
      (lt_of_le_of_ne (not_lt.mp negative) (volume_ne_zero c).symm)

/-! ### No proper and no mirror transport between the two arms -/

private def graphAut (e : cageCanon.Aut) : graph.Aut := ⟨e.val, e.property.1⟩

private theorem autAdj (e : cageCanon.Aut) {a b : Fin 15} (h : graph.Adj a b) :
    graph.Adj (e.val a) (e.val b) :=
  (MoleculeGraph.Aut.adj_iff (m := graph) (graphAut e) a b).mpr h

private theorem autZ (e : cageCanon.Aut) (atom : Fin 15) :
    graph.atomZ (e.val atom) = graph.atomZ atom :=
  MoleculeGraph.Aut.atomZ_eq (m := graph) (graphAut e) atom

/-- **Parity coupling.** A root-fixing automorphism carrying `C1A` to `C1B` carries `C3A` to
`C3B` and acts on the bridge slots of both bridgeheads by one permutation. -/
theorem arm_coupled (e : cageCanon.Aut) (fixed : cageCanon.centerPerm e k0 = k0)
    (moves : cageCanon.ligandPermAt e k0 2 = 3) :
    cageCanon.centerPerm e k3 = k9 ∧ cageCanon.centerPerm e k8 = k14 ∧
      permHandedness (cageCanon.ligandPermAt e k3) =
        permHandedness (cageCanon.ligandPermAt e k8) := by
  have e0 : e.val 0 = 0 := congrArg Subtype.val fixed
  have transported := cageCanon.ligandAtomAt_ligandPermAt (e := e) (c := k0) 2
  rw [fixed, moves, lig0.2.2.2, lig0.2.2.1] at transported
  have e3 : e.val 3 = 9 := transported.symm
  have nb9 : ∀ x, graph.Adj 9 x → x = 0 ∨ x = 11 ∨ x = 12 ∨ x = 13 := by decide
  have nbO : ∀ o x, (o = 11 ∨ o = 12 ∨ o = 13) → graph.Adj o x → x = 9 ∨ x = 14 := by decide
  have nb14 : ∀ x, graph.Adj 14 x → graph.atomZ x = 1 → x = 10 := by decide
  have e5 : e.val 5 = 11 ∨ e.val 5 = 12 ∨ e.val 5 = 13 := by
    have adjacent := autAdj e (show graph.Adj 3 5 by decide)
    rw [e3] at adjacent
    rcases nb9 _ adjacent with h | h
    · exact absurd (e.val.injective (h.trans e0.symm)) (by decide)
    · exact h
  have e8 : e.val 8 = 14 := by
    rcases nbO _ _ e5 (autAdj e (show graph.Adj 5 8 by decide)) with h | h
    · exact absurd (e.val.injective (h.trans e3.symm)) (by decide)
    · exact h
  have e4 : e.val 4 = 10 := by
    have adjacent := autAdj e (show graph.Adj 8 4 by decide)
    rw [e8] at adjacent
    exact nb14 _ adjacent (by rw [autZ]; decide)
  have c3 : cageCanon.centerPerm e k3 = k9 := Subtype.ext e3
  have c8 : cageCanon.centerPerm e k8 = k14 := Subtype.ext e8
  refine ⟨c3, c8, congrArg permHandedness (Equiv.ext fun k => ?_)⟩
  have same : ∀ m : Fin 4, m ≠ 0 → cageCanon.ligandAtomAt k14 m = cageCanon.ligandAtomAt k9 m := by
    rw [lig14f, lig9f]
    decide
  apply cageCanon.ligandAtomAt_injective k14
  have t3 := cageCanon.ligandAtomAt_ligandPermAt (e := e) (c := k3) k
  have t8 := cageCanon.ligandAtomAt_ligandPermAt (e := e) (c := k8) k
  rw [c3] at t3
  rw [c8] at t8
  rw [t8]
  have zero : cageCanon.ligandPermAt e k3 0 = 0 := by
    apply cageCanon.ligandAtomAt_injective k9
    have t30 := cageCanon.ligandAtomAt_ligandPermAt (e := e) (c := k3) 0
    rw [c3, lig3.1, e0] at t30
    rw [t30, lig9.1]
  have bridge : ∀ m : Fin 4, m ≠ 0 → cageCanon.ligandPermAt e k3 m ≠ 0 := by
    intro m hm h
    apply hm
    exact (cageCanon.ligandPermAt e k3).injective (h.trans zero.symm)
  by_cases hk : k = 0
  · subst hk
    rw [zero, lig14.1, lig8.1, e4]
  · rw [same _ (bridge k hk), t3]
    have bridges : ∀ m : Fin 4, m ≠ 0 →
        cageCanon.ligandAtomAt k3 m = cageCanon.ligandAtomAt k8 m := by
      rw [lig3f, lig8f]
      decide
    rw [bridges k hk]

private theorem edge35 : graph.underlyingSimpleGraph.Adj 3 5 :=
  (graph.underlyingSimpleGraph_adj 3 5).mpr (by decide)

private theorem edge58 : graph.underlyingSimpleGraph.Adj 5 8 :=
  (graph.underlyingSimpleGraph_adj 5 8).mpr (by decide)

private theorem reach3 : LigandBranchReaches cageCanon k0 2 k3.1 := by
  unfold LigandBranchReaches
  rw [lig0.2.2.1]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp [k0, k3]

private theorem reach8 : LigandBranchReaches cageCanon k0 2 k8.1 := by
  unfold LigandBranchReaches
  rw [lig0.2.2.1]
  refine ⟨SimpleGraph.Walk.cons edge35 (SimpleGraph.Walk.cons edge58 SimpleGraph.Walk.nil), ?_⟩
  simp [k0, k8]

theorem arms_noTransport (mirror : Bool) : ¬ BranchTransport cageCanon cageCfg k0 2 3 mirror :=
  not_branchTransport_of_parityCoupling cageCanon cageCfg k0 2 3 k3 k8 k9 k14 reach3 reach8
    arm_coupled parity_mismatch mirror

private theorem transportZ {i j : Fin 4} {mirror : Bool}
    (transport : BranchTransport cageCanon cageCfg k0 i j mirror) :
    graph.atomZ (cageCanon.ligandAtomAt k0 j) = graph.atomZ (cageCanon.ligandAtomAt k0 i) := by
  obtain ⟨e, fixed, sent, _⟩ := transport
  have action := cageCanon.ligandAtomAt_ligandPermAt (e := e) (c := k0) i
  rw [fixed, sent] at action
  rw [action]
  exact autZ e _

private theorem rootZ_tie (i j : Fin 4)
    (tie : graph.atomZ (cageCanon.ligandAtomAt k0 j) = graph.atomZ (cageCanon.ligandAtomAt k0 i)) :
    i = j ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  rw [lig0f] at tie
  revert tie
  revert i j
  decide

/-- No two distinct root branches are related by any branch transport. -/
theorem root_noTransport (i j : Fin 4) (mirror : Bool) (distinct : i ≠ j) :
    ¬ BranchTransport cageCanon cageCfg k0 i j mirror := by
  intro transport
  rcases rootZ_tie i j (transportZ transport) with same | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact distinct same
  · exact arms_noTransport mirror transport
  · exact arms_noTransport mirror (branchTransport_inverse cageCanon cageCfg k0 transport)

theorem canonPairwise : MultiCenterMolecule.PairwiseProperDistinguishable cageCanon cageCfg k0 :=
  fun i j distinct => root_noTransport i j false distinct

theorem canonPairCount : physicalEnantiomorphicPairCount cageCanon cageCfg k0 = 0 := by
  have noPair : ∀ i j : Fin 4, ¬ Enantiomorphic cageCanon cageCfg k0 i j :=
    fun i j pair => root_noTransport i j true pair.1 pair.2.1
  simp [physicalEnantiomorphicPairCount, sourceEnantiomorphicPairCount, noPair]

/-! ### The detected molecule -/

private theorem calibratedCoordinates_reindexFrames
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    {cfg : m.Configuration} (tau : m.Center → Equiv.Perm (Fin 4)) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input (m.reindexFrames tau)
      (m.reindexConfiguration tau cfg) center := by
  obtain ⟨pointAt, observed, nonzero, sign⟩ := coordinates
  refine ⟨fun i => pointAt (tau center i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact observed (tau center i)
  · exact cartesianOrientedVolume_perm_ne_zero pointAt (tau center) nonzero
  · have hvec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) k = pointAt k := by
      intro k
      fin_cases k <;> rfl
    have hperm : RationalTetrahedralPermutation.permutedOrientedVolume
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) (tau center) =
        CartesianPoint3.orientedVolume
          (pointAt (tau center 0)) (pointAt (tau center 1))
            (pointAt (tau center 2)) (pointAt (tau center 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
    rw [← hperm, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

private theorem calibratedCoordinates_congr
    {input : CertifiedLocalizedCIPInput} {m n : MultiCenterMolecule input.Atom}
    (h : m = n) (cfg : m.Configuration) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) center) := by
  cases h
  exact coordinates

private theorem branchTransport_congr {m n : MultiCenterMolecule (Fin 15)} (h : m = n)
    (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport m cfg c i j mirror) :
    BranchTransport n (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) c) i j mirror := by
  cases h
  exact transport

theorem cageFrameReindex :
    ∃ tau : cageCanon.Center → Equiv.Perm (Fin 4),
      cageCanon.reindexFrames tau = cageCertified.detectedMultiCenterMolecule := by
  apply cageCertified.exists_reindexFrames_detectedMultiCenterMolecule (m := cageCanon)
  · rfl
  · rfl

def cageTau : cageCanon.Center → Equiv.Perm (Fin 4) := Classical.choose cageFrameReindex

theorem cageTau_spec :
    cageCanon.reindexFrames cageTau = cageCertified.detectedMultiCenterMolecule :=
  Classical.choose_spec cageFrameReindex

/-- The calibrated configuration in the detected ligand enumeration. -/
def detectedCfg : cageCertified.detectedMultiCenterMolecule.Configuration :=
  Eq.mp (congrArg MultiCenterMolecule.Configuration cageTau_spec)
    (cageCanon.reindexConfiguration cageTau cageCfg)

theorem detectedCoordinates (center : cageCertified.detectedMultiCenterMolecule.Center) :
    ActualPhysicalCalibratedCoordinates cageCertified
      cageCertified.detectedMultiCenterMolecule detectedCfg center := by
  let center' : (cageCanon.reindexFrames cageTau).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center cageTau_spec.symm) center
  have coordinates' := calibratedCoordinates_reindexFrames
    (input := cageCertified) (m := cageCanon) (cfg := cageCfg) cageTau center'
    (canonCoordinates center')
  simpa [detectedCfg] using
    calibratedCoordinates_congr (input := cageCertified)
      (m := cageCanon.reindexFrames cageTau)
      (n := cageCertified.detectedMultiCenterMolecule) cageTau_spec
      (cageCanon.reindexConfiguration cageTau cageCfg) center' coordinates'

def cageRoot : cageCertified.TetrahedralCenter :=
  ⟨(0 : Fin 15), (degree_four_iff 0).mpr (by decide)⟩

theorem detectedDomain : RecursiveAuxiliaryPhysicalDomain cageCertified detectedCfg cageRoot :=
  ⟨fun center _ => Or.inr (detectedCoordinates center)⟩

theorem detectedGeometry : RootPhysicalGeometry cageCertified
    cageCertified.detectedMultiCenterMolecule detectedCfg cageRoot := by
  obtain ⟨pointAt, observed, nonzero, sign⟩ := detectedCoordinates cageRoot
  exact ⟨pointAt, observed, nonzero, sign⟩

/-- **No branch transport at the root of the detected molecule.** -/
theorem detected_noTransport (i j : Fin 4) (mirror : Bool) (distinct : i ≠ j) :
    ¬ BranchTransport cageCertified.detectedMultiCenterMolecule detectedCfg cageRoot i j
      mirror := by
  intro transport
  have back := branchTransport_congr cageTau_spec.symm detectedCfg cageRoot i j mirror transport
  have back' : BranchTransport (cageCanon.reindexFrames cageTau)
      (cageCanon.reindexConfiguration cageTau cageCfg) cageRoot i j mirror := by
    simpa [detectedCfg] using back
  have reindexed : BranchTransport (cageCanon.reindexFrames cageTau)
      (cageCanon.reindexConfiguration cageTau cageCfg) k0 i j mirror := back'
  have canonical := (MultiCenterMolecule.branchTransport_reindexFrames_iff cageCanon cageTau
    cageCfg k0 i j mirror).1 reindexed
  exact root_noTransport _ _ mirror (fun same => distinct ((cageTau k0).injective same)) canonical

theorem detectedPairwise : MultiCenterMolecule.PairwiseProperDistinguishable
    cageCertified.detectedMultiCenterMolecule detectedCfg cageRoot :=
  fun i j distinct => detected_noTransport i j false distinct

theorem detectedPairCount : physicalEnantiomorphicPairCount
    cageCertified.detectedMultiCenterMolecule detectedCfg cageRoot = 0 := by
  have noPair : ∀ i j : Fin 4,
      ¬ Enantiomorphic cageCertified.detectedMultiCenterMolecule detectedCfg cageRoot i j :=
    fun i j pair => detected_noTransport i j true pair.1 pair.2.1
  simp [physicalEnantiomorphicPairCount, sourceEnantiomorphicPairCount, noPair]

theorem constant_charge :
    AcyclicCutBranchAutomorphism.ConstantFormalCharge cageCertified.moleculeGraph := by
  refine ⟨0, ?_⟩
  intro atom
  fin_cases atom <;> decide

/-! ## The actual evaluator -/

open LocalizedRuleMajorReference DeclarativeCIP
open LocalizedRecursiveAuxiliaryPhysicalTransport LocalizedRecursiveAuxiliaryPhysicalCorrectness
open LocalizedCyclicMatchedReadingPhysicalTransport

def cageReference : LocalizedRuleMajorReference.Input where
  certified := cageCertified

abbrev cageFrames := finalRootFrames cageReference simple_bonded cageRoot

abbrev cageTarget : LocalizedRuleMajorReference.Occurrence cageReference :=
  cageCertified.localizedFinalOccurrenceExecutable (carrierFuel cageReference) cageRoot

theorem cageCenter : cageFrames.center = cageRoot :=
  finalRootFrames_center cageReference simple_bonded cageRoot

theorem cageAddress : cageTarget.1.address = [] :=
  cageCertified.localizedFinalOccurrenceExecutable_address (carrierFuel cageReference) cageRoot

theorem cageReal : cageTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real cageReference cageRoot

theorem cageHistory : cageTarget.1.node.history = ([0] : List (Fin 15)) := by
  have facts := (rootFrame_target_facts cageFrames cageAddress cageReal).2.1
  refine facts.trans ?_
  rw [cageCenter]
  rfl

theorem cage_slot (a : Fin 15) (adjacent : graph.Adj 0 a) :
    ∃ s : Fin 4, cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
      (cageFrames.detectedLigandPermutation s) = a := by
  have adjacentCenter : graph.Adj cageFrames.center.1 a := by
    rw [cageCenter]
    exact adjacent
  obtain ⟨k, hk⟩ := cageCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
    cageFrames.center a adjacentCenter
  exact ⟨cageFrames.detectedLigandPermutation.symm k, by rw [Equiv.apply_symm_apply]; exact hk⟩

def slotA : Fin 4 := Classical.choose (cage_slot 3 (by decide))
def slotB : Fin 4 := Classical.choose (cage_slot 9 (by decide))

theorem slotA_spec : cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
    (cageFrames.detectedLigandPermutation slotA) = (3 : Fin 15) :=
  Classical.choose_spec (cage_slot 3 (by decide))

theorem slotB_spec : cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
    (cageFrames.detectedLigandPermutation slotB) = (9 : Fin 15) :=
  Classical.choose_spec (cage_slot 9 (by decide))

theorem slots_ne : slotA ≠ slotB := by
  intro same
  have atoms := slotA_spec
  rw [same, slotB_spec] at atoms
  exact absurd atoms (by decide)

theorem armSwap_root :
    (armSwap : Equiv.Perm (Fin 15)) cageFrames.center.1 = cageFrames.center.1 := by
  rw [cageCenter]
  decide

theorem armSwap_AB : (armSwap : Equiv.Perm (Fin 15))
      (cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
        (cageFrames.detectedLigandPermutation slotA)) =
    cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
      (cageFrames.detectedLigandPermutation slotB) := by
  rw [slotA_spec, slotB_spec]
  decide

theorem armSwap_BA : (armSwap : Equiv.Perm (Fin 15))
      (cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
        (cageFrames.detectedLigandPermutation slotB)) =
    cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
      (cageFrames.detectedLigandPermutation slotA) := by
  rw [slotA_spec, slotB_spec]
  decide

/-! ### Reader-free refusal witnesses -/

theorem handedness_of_cube {V : Type*} [Fintype V] [DecidableEq V] (m : MultiCenterMolecule V)
    (E : m.Aut) (d : m.Center) (fixed : m.centerPerm E d = d) (cube : E * E * E = 1) :
    permHandedness (m.ligandPermAt E d) = 1 := by
  have two : m.ligandPermAt (E * E) d = m.ligandPermAt E d * m.ligandPermAt E d := by
    rw [MultiCenterMolecule.ligandPermAt_mul, fixed]
  have three : m.ligandPermAt (E * E * E) d =
      m.ligandPermAt E d * m.ligandPermAt E d * m.ligandPermAt E d := by
    rw [MultiCenterMolecule.ligandPermAt_mul, fixed, two]
  rw [cube, MultiCenterMolecule.ligandPermAt_one] at three
  have signs := congrArg Equiv.Perm.sign three
  rw [Equiv.Perm.sign_one, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul] at signs
  rcases Int.units_eq_one_or (Equiv.Perm.sign (m.ligandPermAt E d)) with hs | hs
  · simp [permHandedness, hs]
  · rw [hs] at signs
    exact absurd signs (by decide)

private theorem detected_center_mem (d : cageCertified.detectedMultiCenterMolecule.Center) :
    d.1 ∈ graph.tetrahedralCenterSet := d.2

/-- Bridge 3-cycle at an attachment bridgehead, history `[c1, 0]`. -/
theorem cycleWitness (σ : graph.Aut) (c1 c3 s t : Fin 15) (inner : List (Fin 15))
    (basics : s ≠ t ∧ graph.Adj c1 s ∧ graph.Adj c1 t ∧ s ∉ [c1, 0] ∧ t ∉ [c1, 0] ∧
      (∀ x ∈ [c1, 0], (σ : Equiv.Perm (Fin 15)) x = x) ∧ (σ : Equiv.Perm (Fin 15)) s = t)
    (closed : ∀ a b, a ∈ inner → a ∉ [c1, 0] → b ∉ [c1, 0] → graph.Adj a b → b ∈ inner)
    (start : s ∈ inner)
    (centers : ∀ x ∈ inner, x ∈ graph.tetrahedralCenterSet → x = c3)
    (fixes : (σ : Equiv.Perm (Fin 15)) c3 = c3)
    (cube : (σ : Equiv.Perm (Fin 15)) * σ * σ = 1) :
    HistoryRefusalWitness cageReference detectedCfg ([c1, 0] : List (Fin 15)) c1 := by
  obtain ⟨st, adjS, adjT, freshS, freshT, fixedHistory, sent⟩ := basics
  refine ⟨σ, s, t, st, adjS, adjT, freshS, freshT, fixedHistory, sent, ?_⟩
  intro d component
  have member := inComponent_closed graph [c1, 0] (fun x => x ∈ inner) closed component start
  have dEq : d.1 = c3 := centers _ member (detected_center_mem d)
  have fixedE : cageReference.certified.detectedMultiCenterMolecule.centerPerm
      (cageReference.certified.physicalDetectedAut σ) d = d := by
    apply Subtype.ext
    show (σ : Equiv.Perm (Fin 15)) d.1 = d.1
    rw [dEq]
    exact fixes
  have cubeE : cageReference.certified.physicalDetectedAut σ *
      cageReference.certified.physicalDetectedAut σ *
      cageReference.certified.physicalDetectedAut σ = 1 := Subtype.ext cube
  rw [fixedE, handedness_of_cube _ _ d fixedE cubeE, mul_one]

/-- Bridge swap at a far bridgehead, history `[c3, o, c1, 0]`. -/
theorem swapWitness (σ : graph.Aut) (c1 c3 o s t : Fin 15)
    (basics : s ≠ t ∧ graph.Adj c3 s ∧ graph.Adj c3 t ∧ s ∉ [c3, o, c1, 0] ∧
      t ∉ [c3, o, c1, 0] ∧ (∀ x ∈ [c3, o, c1, 0], (σ : Equiv.Perm (Fin 15)) x = x) ∧
      (σ : Equiv.Perm (Fin 15)) s = t)
    (isolated : ∀ b, b ∉ [c3, o, c1, 0] → graph.Adj s b → False)
    (notCenter : s ∉ graph.tetrahedralCenterSet) :
    HistoryRefusalWitness cageReference detectedCfg ([c3, o, c1, 0] : List (Fin 15)) c3 := by
  obtain ⟨st, adjS, adjT, freshS, freshT, fixedHistory, sent⟩ := basics
  refine ⟨σ, s, t, st, adjS, adjT, freshS, freshT, fixedHistory, sent, ?_⟩
  intro d component
  have member := inComponent_closed graph [c3, o, c1, 0] (fun x => x = s)
    (fun a b ha _ hb adjacent => (isolated b hb (ha ▸ adjacent)).elim) component rfl
  exact absurd (member ▸ detected_center_mem d) notCenter

theorem cycleWitnessA :
    HistoryRefusalWitness cageReference detectedCfg ([3, 0] : List (Fin 15)) (3 : Fin 15) :=
  cycleWitness cycleA 3 8 5 6 [4, 5, 6, 7, 8] (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem cycleWitnessB :
    HistoryRefusalWitness cageReference detectedCfg ([9, 0] : List (Fin 15)) (9 : Fin 15) :=
  cycleWitness cycleB 9 14 11 12 [10, 11, 12, 13, 14] (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem swapWitnessA (o : Fin 15) (ho : o ∈ [5, 6, 7]) :
    HistoryRefusalWitness cageReference detectedCfg ([8, o, 3, 0] : List (Fin 15)) (8 : Fin 15) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact swapWitness (otherBridgeSwap 5) 3 8 5 6 7 (by decide) (by decide) (by decide)
  · exact swapWitness (otherBridgeSwap 6) 3 8 6 5 7 (by decide) (by decide) (by decide)
  · exact swapWitness (otherBridgeSwap 7) 3 8 7 5 6 (by decide) (by decide) (by decide)

theorem swapWitnessB (o : Fin 15) (ho : o ∈ [11, 12, 13]) :
    HistoryRefusalWitness cageReference detectedCfg ([14, o, 9, 0] : List (Fin 15)) (14 : Fin 15) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact swapWitness (otherBridgeSwap 11) 9 14 11 12 13 (by decide) (by decide) (by decide)
  · exact swapWitness (otherBridgeSwap 12) 9 14 12 11 13 (by decide) (by decide) (by decide)
  · exact swapWitness (otherBridgeSwap 13) 9 14 13 11 12 (by decide) (by decide) (by decide)

/-! ### Every reached occurrence of a cage arm is refused -/

private theorem getLast?_append_of {α : Type*} (l m : List α) {a : α}
    (h : m.getLast? = some a) : (l ++ m).getLast? = some a := by
  simp [List.getLast?_append, h]

theorem blind_of_cage {i j : Fin 4} (distinct : i ≠ j)
    (sent : (armSwap : Equiv.Perm (Fin 15))
        (cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
          (cageFrames.detectedLigandPermutation i)) =
      cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
        (cageFrames.detectedLigandPermutation j))
    {c1 c3 h : Fin 15} {os : List (Fin 15)}
    (ligand : cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
      (cageFrames.detectedLigandPermutation i) = c1)
    (cage : Cage graph.Adj 0 c1 c3 h os)
    (armClosed : ∀ a b, a ∈ c1 :: c3 :: h :: os → a ∉ [0] → b ∉ [0] → graph.Adj a b →
      b ∈ c1 :: c3 :: h :: os)
    (centers : ∀ x ∈ c1 :: c3 :: h :: os, x ∈ graph.tetrahedralCenterSet → x = c1 ∨ x = c3)
    (cycleW : HistoryRefusalWitness cageReference detectedCfg ([c1, 0] : List (Fin 15)) c1)
    (swapW : ∀ o ∈ os,
      HistoryRefusalWitness cageReference detectedCfg ([c3, o, c1, 0] : List (Fin 15)) c3) :
    ∀ z, Reach cageFrames i z → referenceState cageReference z = none := by
  intro z reach
  by_cases real : z.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  swap
  · exact referenceState_none_of_not_real cageReference z real
  by_cases detected : IsDetectedCenter cageCertified.moleculeGraph
      (cageCertified.molecularFrameUnit z.1).atom
  swap
  · exact (LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_state_transport_none
      cageReference simple_bonded armSwap z real detected).1
  have domain : RecursiveAuxiliaryPhysicalDomain cageCertified detectedCfg cageFrames.center := by
    rw [cageCenter]
    exact detectedDomain
  apply referenceState_none_of_historyWitness simple_bonded cageFrames cageAddress cageReal distinct
    armSwap armSwap_root sent detectedCfg domain z reach real detected
  intro d current
  obtain ⟨cursor, cursorEq, reachable⟩ := reach
  have outwardI : IsLocalizedActualFrameOutwardCursor cageCertified cageTarget
      (cageFrames.frame.cursorAt i) :=
    ⟨_, (rootFramePair cageFrames cageAddress i i).leftAddress⟩
  obtain ⟨extra, _extraNe, history, located⟩ :=
    reached_history_inComponent simple_bonded cageFrames cageReal outwardI cursor reachable
  rw [cursorEq] at history located
  obtain ⟨atom, current', component⟩ := located real
  have atomEq : atom = d := Option.some.inj (current'.symm.trans current)
  subst atomEq
  change RetainedCoherentSymmetry.InComponent graph cageTarget.1.node.history
    (cageCertified.detectedMultiCenterMolecule.ligandAtomAt cageFrames.center
      (cageFrames.detectedLigandPermutation i)) atom at component
  rw [ligand, cageHistory] at component
  have member := inComponent_closed graph [0] (fun x => x ∈ c1 :: c3 :: h :: os) armClosed
    component List.mem_cons_self
  let unit : DetectedOccurrence cageCertified.moleculeGraph :=
    ⟨cageCertified.molecularFrameUnit z.1, detected⟩
  let frames := cyclicContextFrameCompilation cageReference simple_bonded z real unit rfl
  have centerMeaning := (cageCertified.localizedOccurrenceDescriptorCenter?_eq_some_iff z
    frames.center).mp frames.centerComputed
  have atomCenter : atom = frames.center.1 :=
    Option.some.inj (current.symm.trans centerMeaning.2)
  have isCenter : atom ∈ graph.tetrahedralCenterSet := by
    rw [atomCenter]
    exact frames.center.2
  have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    cageCertified z real
  have head : z.1.node.history.head? = some atom := facts.2.symm.trans current
  have chain : z.1.node.history.IsChain graph.Adj :=
    cageCertified.declarativeLocalizedOccurrence_node_history_chain
      ((cageCertified.mem_localizedOccurrences_iff _ z.1).mp z.2)
  have rootLast : cageTarget.1.node.history.getLast? = some (0 : Fin 15) := by
    rw [cageHistory]
    rfl
  have last : z.1.node.history.getLast? = some (0 : Fin 15) := by
    rw [history]
    exact getLast?_append_of extra _ rootLast
  rcases centers atom member isCenter with rfl | rfl
  · rw [cage.history_c1 facts.1 chain head last]
    exact cycleW
  · obtain ⟨o, ho, historyEq⟩ := cage.history_c3 facts.1 chain head last
    rw [historyEq]
    exact swapW o ho

theorem cageA : Cage graph.Adj 0 3 8 4 [5, 6, 7] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem cageB : Cage graph.Adj 0 9 14 10 [11, 12, 13] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem arms_blind : ∀ z, Reach cageFrames slotA z ∨ Reach cageFrames slotB z →
    referenceState cageReference z = none := by
  rintro z (reach | reach)
  · exact blind_of_cage slots_ne armSwap_AB slotA_spec cageA (by decide) (by decide)
      cycleWitnessA swapWitnessA z reach
  · exact blind_of_cage slots_ne.symm armSwap_BA slotB_spec cageB (by decide) (by decide)
      cycleWitnessB swapWitnessB z reach

/-! ## The counterexample -/

theorem cage_rootKeys_eq : cageFrames.retainedKeys slotA = cageFrames.retainedKeys slotB :=
  retainedKeys_eq_of_blindArms simple_bonded cageFrames cageAddress cageReal armSwap armSwap_root
    armSwap_AB arms_blind

theorem cage_root_refuses : referenceState cageReference cageTarget = none :=
  referenceState_none_of_blindArms simple_bonded cageFrames cageAddress cageReal armSwap slots_ne
    armSwap_root armSwap_AB arms_blind

theorem cage_report_refuses : (cageRoot.val.val, none) ∈ analyze cageReference := by
  rw [analyze_eq_referenceReport cageReference]
  exact List.mem_map.mpr ⟨cageRoot,
    (cageCertified.mem_canonicalTetrahedralCenters_iff cageRoot).mpr cageRoot.2,
    Prod.ext rfl cage_root_refuses⟩

/-- **Hidden bridgehead parity: the inverse fails on the intended final domain.** For the
fifteen-atom single-bond formal cage input with calibrated coordinates:

* the physical domain holds: simple bonds, constant formal charge, every non-root detected
  center calibrated (`RecursiveAuxiliaryPhysicalDomain`), calibrated root geometry, and the root
  branches are pairwise properly distinguishable; in fact no two distinct root branches are
  related by any proper or mirror transport, so the physical enantiomorphic pair count is `0`;
* yet the actual complete retained keys of the two cage arms are equal (a full Rule-5 tie, in
  particular an actual prior tie of a non-enantiomorphic pair), the actual report state at the
  root is `none`, and `analyze` reports the root as refused. -/
theorem hiddenParity_counterexample :
    cageCertified.moleculeGraph.SimpleBonded ∧
    AcyclicCutBranchAutomorphism.ConstantFormalCharge cageCertified.moleculeGraph ∧
    RecursiveAuxiliaryPhysicalDomain cageCertified detectedCfg cageRoot ∧
    RootPhysicalGeometry cageCertified cageCertified.detectedMultiCenterMolecule detectedCfg
      cageRoot ∧
    MultiCenterMolecule.PairwiseProperDistinguishable cageCertified.detectedMultiCenterMolecule
      detectedCfg cageRoot ∧
    (∀ i j : Fin 4, i ≠ j → ∀ mirror : Bool,
      ¬ BranchTransport cageCertified.detectedMultiCenterMolecule detectedCfg cageRoot i j
        mirror) ∧
    physicalEnantiomorphicPairCount cageCertified.detectedMultiCenterMolecule detectedCfg
      cageRoot = 0 ∧
    slotA ≠ slotB ∧
    cageFrames.retainedKeys slotA = cageFrames.retainedKeys slotB ∧
    referenceState cageReference cageTarget = none ∧
    (cageRoot.val.val, none) ∈ analyze cageReference :=
  ⟨simple_bonded, constant_charge, detectedDomain, detectedGeometry, detectedPairwise,
    fun i j distinct mirror => detected_noTransport i j mirror distinct, detectedPairCount,
    slots_ne, cage_rootKeys_eq, cage_root_refuses, cage_report_refuses⟩

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.source_graphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.simple_bonded
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.degree_four_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.Cage.history_c1
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.Cage.history_c3
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.inComponent_closed
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.armSwap_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.swap67_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.arm_coupled
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.parity_mismatch
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.root_noTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.detected_noTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.detectedDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.handedness_of_cube
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.blind_of_cage
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.arms_blind
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.cage_rootKeys_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.cage_root_refuses
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.cage_report_refuses
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion.hiddenParity_counterexample
