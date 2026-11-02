import TetraStereo.UniversalProof.NextFrontier.NativeRingReachability
import TetraStereo.UniversalProof.NextFrontier.NativeRingHydrogenFacts

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingCycleGuard

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingReachability
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

theorem avoiding_forward (mol : RawMolecule) (blocked source target : Nat)
    (kind : ParsedBondKind) (edge : (⟨source, target, kind⟩ : RawBond) ∈ mol.bonds)
    (unblocked : target ≠ blocked) : target ∈ avoidingNeighbors mol blocked source := by
  apply List.mem_filterMap.mpr
  exact ⟨_, edge, by simp [unblocked]⟩

theorem avoiding_reverse (mol : RawMolecule) (blocked source target : Nat)
    (kind : ParsedBondKind) (edge : (⟨source, target, kind⟩ : RawBond) ∈ mol.bonds)
    (unblocked : source ≠ blocked) : source ∈ avoidingNeighbors mol blocked target := by
  apply List.mem_filterMap.mpr
  refine ⟨_, edge, ?_⟩
  by_cases equal : source = target
  · subst target
    simp [unblocked]
  · simp [equal, unblocked]

theorem incident_forward (mol : RawMolecule) (source target : Nat) (kind : ParsedBondKind)
    (edge : (⟨source, target, kind⟩ : RawBond) ∈ mol.bonds) :
    target ∈ mol.incidentAtoms source := by
  apply (mem_eraseDups_iff target _).mpr
  exact List.mem_filterMap.mpr ⟨_, edge, by simp⟩

theorem incident_reverse (mol : RawMolecule) (source target : Nat) (kind : ParsedBondKind)
    (edge : (⟨source, target, kind⟩ : RawBond) ∈ mol.bonds) :
    source ∈ mol.incidentAtoms target := by
  apply (mem_eraseDups_iff source _).mpr
  apply List.mem_filterMap.mpr
  refine ⟨_, edge, ?_⟩
  by_cases equal : source = target
  · subst target
    simp
  · simp [equal]

/-- A pair in the actual incident list contributes to the production ring counter when its
ordered endpoints are connected without the center. -/
theorem ringPairCount_pos_of_ordered_reach (mol : RawMolecule) (fuel center : Nat)
    (ligands : List Nat) (i j : Nat) (hi : i < ligands.length) (hj : j < ligands.length)
    (ordered : i < j)
    (reached : (mol.reachableAvoiding fuel center [ligands.getD i 0]
      [ligands.getD i 0]).contains (ligands.getD j 0) = true) :
    0 < mol.ringPairCount fuel center ligands := by
  apply List.length_pos_of_mem (a := (i, j))
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨j, List.mem_range.mpr hj, by simp only [if_pos ordered, reached, ↓reduceIte]⟩

/-- The graph test does not depend on which of the two ligand roots appears first in bond order.
Both directed walks are explicit structural witnesses, not assumed cycle-test results. -/
theorem cycle_of_walks (mol : RawMolecule) (center fuel length a b : Nat)
    (ha : a ∈ mol.incidentAtoms center) (hb : b ∈ mol.incidentAtoms center)
    (distinct : a ≠ b) (forward : AvoidingWalk mol center length a b)
    (backward : AvoidingWalk mol center length b a) (enough : length ≤ fuel) :
    mol.atomLiesInCycle fuel center = true := by
  obtain ⟨i, ai⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨j, bj⟩ := List.mem_iff_getElem?.mp hb
  have hi := (List.getElem?_eq_some_iff.mp ai).1
  have hj := (List.getElem?_eq_some_iff.mp bj).1
  have aiD : (mol.incidentAtoms center).getD i 0 = a := by
    rw [List.getD_eq_getElem?_getD, ai]
    rfl
  have bjD : (mol.incidentAtoms center).getD j 0 = b := by
    rw [List.getD_eq_getElem?_getD, bj]
    rfl
  have different : i ≠ j := by
    intro equal
    subst j
    exact distinct (Option.some.inj (ai.symm.trans bj))
  have positive : 0 < mol.ringPairCount fuel center (mol.incidentAtoms center) := by
    rcases lt_or_gt_of_ne different with ordered | ordered
    · apply ringPairCount_pos_of_ordered_reach mol fuel center _ i j hi hj ordered
      rw [aiD, bjD]
      exact reachable_singleton_of_walk mol center fuel length a b forward enough
    · apply ringPairCount_pos_of_ordered_reach mol fuel center _ j i hj hi ordered
      rw [bjD, aiD]
      exact reachable_singleton_of_walk mol center fuel length b a backward enough
  exact decide_eq_true positive

theorem original_edge_retained (n : Nat) (parity : TetrahedralInputParity) (edge : RawBond)
    (member : edge ∈ ringBonds n) : edge ∈ (expanded n parity).bonds := by
  exact (withExplicitHydrogens_bonds_mem_iff (ringRaw n parity) edge).mpr
    (Or.inl member)

theorem chain_forward (n : Nat) (parity : TetrahedralInputParity) (steps start : Nat)
    (bound : start + steps ≤ n) :
    AvoidingWalk (expanded n parity) 0 steps (start + 4) (start + steps + 4) := by
  induction steps generalizing start with
  | zero => simpa using AvoidingWalk.nil (mol := expanded n parity) (blocked := 0) (start + 4)
  | succ steps ih =>
      have edge := original_edge_retained n parity (chainBond (start + 1))
        (chainBond_mem n (start + 1) (by omega))
      have step : start + 5 ∈ avoidingNeighbors (expanded n parity) 0 (start + 4) := by
        have shape : chainBond (start + 1) = (⟨start + 4, start + 5, .single⟩ : RawBond) := by
          simp [chainBond]
        rw [shape] at edge
        exact avoiding_forward _ 0 _ _ _ edge (by omega)
      have tail := ih (start + 1) (by omega)
      convert AvoidingWalk.cons step tail using 1
      omega

theorem chain_backward_to_arm (n : Nat) (parity : TetrahedralInputParity) (k : Nat)
    (bound : k ≤ n) : AvoidingWalk (expanded n parity) 0 (k + 1) (k + 4) 2 := by
  induction k with
  | zero =>
      have edge := original_edge_retained n parity (chainBond 0)
        (chainBond_mem n 0 (by omega))
      exact AvoidingWalk.cons (avoiding_reverse _ 0 2 4 .single edge (by decide))
        (AvoidingWalk.nil 2)
  | succ k ih =>
      have edge := original_edge_retained n parity (chainBond (k + 1))
        (chainBond_mem n (k + 1) (by omega))
      have shape : chainBond (k + 1) = (⟨k + 4, k + 5, .single⟩ : RawBond) := by
        simp [chainBond]
      rw [shape] at edge
      exact AvoidingWalk.cons (avoiding_reverse _ 0 _ _ _ edge (by omega)) (ih (by omega))

/-- Every expanded family member has an actual cycle through its tagged root. The path joins
the two carbon arms using exactly n+1 heavy-atom edges and avoids the tagged root throughout. -/
theorem actual_root_cycle (n fuel : Nat) (parity : TetrahedralInputParity)
    (enough : n + 1 ≤ fuel) : (expanded n parity).atomLiesInCycle fuel 0 = true := by
  have leftEdge := original_edge_retained n parity _ (prefix1_mem n)
  have rightEdge := original_edge_retained n parity _ (closureBond_mem n)
  have firstEdge := original_edge_retained n parity (chainBond 0)
    (chainBond_mem n 0 (by omega))
  have forward : AvoidingWalk (expanded n parity) 0 (n + 1) 2 (n + 4) := by
    exact AvoidingWalk.cons (avoiding_forward _ 0 2 4 .single firstEdge (by decide))
      (by simpa using chain_forward n parity n 0 (by omega))
  exact cycle_of_walks _ 0 fuel (n + 1) 2 (n + 4)
    (incident_forward _ 0 2 .single leftEdge)
    (incident_reverse _ (n + 4) 0 .single rightEdge) (by omega)
    forward (chain_backward_to_arm n parity n (Nat.le_refl _)) enough

end TetraStereo.UniversalProof.NativeRingCycleGuard
