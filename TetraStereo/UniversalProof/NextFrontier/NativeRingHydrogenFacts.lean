import TetraStereo.UniversalProof.NextFrontier.NativeRingParserPublic
import TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingHydrogenFacts

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

/-- The actual production hydrogen expansion of the independently specified physical family. -/
def expanded (n : Nat) (parity : TetrahedralInputParity) : RawMolecule :=
  (ringRaw n parity).withExplicitHydrogens

private theorem range_lookup_map {α β : Type*} (values : List α) (f : α → β)
    (fallback : β) :
    (List.range values.length).map (fun index => ((listGet? values index).map f).getD fallback) =
      values.map f := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map, listGet?, Option.map_some, Option.getD_some, List.map_cons]
      exact congrArg (fun rest => f head :: rest) ih

theorem ring_inline_counts (n : Nat) (parity : TetrahedralInputParity)
    (spec : AtomSpec) (member : spec ∈ (ringRaw n parity).atoms) :
    ∃ count, spec.explicitHydrogens? = some count := by
  rw [ringRaw_atoms] at member
  rcases List.mem_append.mp member with initialMembers | tail
  · simp only [ringPrefix, List.mem_cons, List.not_mem_nil, or_false] at initialMembers
    rcases initialMembers with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · have equal := (List.mem_replicate.mp tail).2
    subst spec
    exact ⟨2, rfl⟩

theorem ring_actual_hydrogen_inventory (n : Nat) (parity : TetrahedralInputParity) :
    (List.range (ringRaw n parity).atomCount).map (ringRaw n parity).hydrogenCountAt =
      hydrogenInventory n := by
  rw [← hydrogen_inventory_actual_atoms n parity,
    ← range_lookup_map (ringRaw n parity).atoms AtomSpec.explicitHydrogens 0]
  apply List.map_congr_left
  intro index member
  have bound := List.mem_range.mp member
  obtain ⟨spec, lookup⟩ := listGet?_exists_of_lt (ringRaw n parity).atoms index bound
  obtain ⟨count, inline⟩ := ring_inline_counts n parity spec
    (listGet?_eq_some_implies_mem _ index spec lookup)
  simp only [hydrogenCountAt, atomAt?, lookup, Option.map_some, Option.getD_some,
    AtomSpec.explicitHydrogens, inline]

theorem expanded_atom_count (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).atomCount = 3 * n + 9 := by
  unfold expanded
  rw [withExplicitHydrogens_atomCount_eq, ring_actual_hydrogen_inventory, atom_count,
    hydrogen_count]
  omega

theorem expanded_original_atom (n : Nat) (parity : TetrahedralInputParity)
    (index : Nat) (spec : AtomSpec) (observed : (ringRaw n parity).atomAt? index = some spec) :
    (expanded n parity).atomAt? index = some (materializedAtomSpec spec) :=
  withExplicitHydrogens_originalAtom _ (ringRaw_wellFormed n parity) index spec observed

theorem expanded_fresh_atom (n : Nat) (parity : TetrahedralInputParity)
    (index : Nat) (spec : AtomSpec) (fresh : n + 5 ≤ index)
    (observed : (expanded n parity).atomAt? index = some spec) :
    spec = AtomSpec.aliphatic .H ∧ (expanded n parity).incidentBondOrderSum index = 1 :=
  withExplicitHydrogens_freshAtom _ (ringRaw_wellFormed n parity) index spec
    (by rwa [atom_count]) observed

theorem raw_only_root_tagged (n : Nat) (parity : TetrahedralInputParity) :
    ∀ index : Fin (ringRaw n parity).atomCount, ∀ spec,
      (ringRaw n parity).atomAt? index.val = some spec →
      spec.tetrahedral?.isSome = true → index.val = 0 := by
  intro index spec observed tagged
  rcases lt_or_ge index.val 4 with small | large
  · interval_cases index.val <;>
      simp [ringRaw, atomAt?, listGet?] at observed
    all_goals subst spec
    all_goals simp_all [carbon, taggedCarbon, AtomSpec.aliphatic]
  · obtain ⟨k, position⟩ : ∃ k, index.val = k + 4 := ⟨index.val - 4, by omega⟩
    have bound : k ≤ n := by
      have bounded : index.val < n + 5 := by simpa only [atom_count] using index.isLt
      omega
    rw [position, ringRaw_atomAt_chain n parity k bound] at observed
    injection observed with equal
    subst spec
    cases tagged

theorem expanded_only_root_tagged (n : Nat) (parity : TetrahedralInputParity) :
    ∀ index : Fin (expanded n parity).atomCount, ∀ spec,
      (expanded n parity).atomAt? index.val = some spec →
      spec.tetrahedral?.isSome = true → index.val = 0 := by
  intro index spec observed tagged
  by_cases original : index.val < (ringRaw n parity).atomCount
  · obtain ⟨originalSpec, lookup⟩ := listGet?_exists_of_lt (ringRaw n parity).atoms index.val original
    have source : (ringRaw n parity).atomAt? index.val = some originalSpec := lookup
    have equal := Option.some.inj ((expanded_original_atom n parity index.val originalSpec source).symm.trans observed)
    subst spec
    exact raw_only_root_tagged n parity ⟨index.val, original⟩ originalSpec source tagged
  · have fresh : n + 5 ≤ index.val := by rw [atom_count] at original; omega
    have equal := (expanded_fresh_atom n parity index.val spec fresh observed).1
    subst spec
    cases tagged

theorem root_has_no_predecessor (n : Nat) (parity : TetrahedralInputParity) :
    (ringRaw n parity).hydrogenHasPreceding 0 = false := rfl

/-- The complete actual expansion, including final exact-neighbor normalization, preserves the
correct first-atom H position. No intermediate-fold row is substituted for the output row. -/
theorem expanded_root_written_row (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).writtenNeighbors 0 = [n + 5, 1, 2, n + 4] := by
  rw [expanded, withExplicitHydrogens_writtenNeighbors _ (ringRaw_wellFormed n parity)
    (ringRaw_writtenNeighborExact n parity) 0 (by rw [atom_count]; omega)]
  unfold materializedWrittenRow materializedHydrogenIds hydrogenExpansionBase
  rw [ringRaw_writtenNeighbors_zero, atom_count]
  change insertHydrogenInOrder [1, 2, n + 4] false [n + 5 + 0] = _
  simp only [Nat.add_zero]
  rfl

theorem expanded_stereochemical_admissible (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).StereochemicalAdmissible :=
  withExplicitHydrogens_preserves_stereochemicalAdmissible _
    ⟨ringRaw_admissible n parity, ringRaw_writtenNeighborExact n parity⟩

theorem raw_chain_hydrogen_count (n : Nat) (parity : TetrahedralInputParity)
    (k : Nat) (bound : k ≤ n) :
    (ringRaw n parity).hydrogenCountAt (k + 4) = 2 := by
  unfold hydrogenCountAt
  rw [ringRaw_atomAt_chain n parity k bound]
  rfl

theorem ring_prefix_hydrogen_sum (n : Nat) (parity : TetrahedralInputParity)
    (k : Nat) (bound : k ≤ n + 1) :
    ((List.range (k + 4)).map (ringRaw n parity).hydrogenCountAt).sum = 2 + 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show k + 1 + 4 = (k + 4) + 1 by omega, List.range_succ, List.map_append,
        List.sum_append, List.map_singleton, List.sum_singleton, ih (by omega),
        raw_chain_hydrogen_count n parity k (by omega)]
      omega

theorem chain_hydrogen_base (n : Nat) (parity : TetrahedralInputParity)
    (k : Nat) (bound : k ≤ n) :
    hydrogenExpansionBase (ringRaw n parity) (k + 4) = n + 7 + 2 * k := by
  unfold hydrogenExpansionBase
  rw [atom_count, ring_prefix_hydrogen_sum n parity k (by omega)]
  omega

theorem expanded_chlorinated_arm_row (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).writtenNeighbors 2 = [0, n + 6, 3, 4] := by
  rw [expanded, withExplicitHydrogens_writtenNeighbors _ (ringRaw_wellFormed n parity)
    (ringRaw_writtenNeighborExact n parity) 2 (by rw [atom_count]; omega)]
  unfold materializedWrittenRow materializedHydrogenIds hydrogenExpansionBase
  rw [ringRaw_writtenNeighbors_two, atom_count]
  change insertHydrogenInOrder [0, 3, 4] true [n + 5 + (1 + 0) + 0] = _
  simp [insertHydrogenInOrder]

theorem expanded_chain_written_row (n : Nat) (parity : TetrahedralInputParity)
    (k : Nat) (bound : k ≤ n) :
    (expanded n parity).writtenNeighbors (k + 4) =
      [if k = 0 then 2 else k + 3, n + 7 + 2 * k, n + 8 + 2 * k,
        if k < n then k + 5 else 0] := by
  rw [expanded, withExplicitHydrogens_writtenNeighbors _ (ringRaw_wellFormed n parity)
    (ringRaw_writtenNeighborExact n parity) (k + 4) (by rw [atom_count]; omega)]
  have preceding : materializationHasPreceding (ringRaw n parity) (k + 4) = true := by
    change (ringRaw n parity).hydrogenHasPreceding (k + 4) = true
    unfold hydrogenHasPreceding
    rw [ringRaw_predecessor_chain n k parity (by omega)]
    rfl
  unfold materializedWrittenRow materializedHydrogenIds
  rw [ringRaw_writtenNeighbors_chain n parity k (by omega), preceding,
    raw_chain_hydrogen_count n parity k bound, chain_hydrogen_base n parity k bound]
  change [if k = 0 then 2 else k + 3, n + 7 + 2 * k + 0,
    n + 7 + 2 * k + 1, if k < n then k + 5 else 0] = _
  rw [Nat.add_zero, show n + 7 + 2 * k + 1 = n + 8 + 2 * k by omega]
  simp only [Nat.add_zero]

theorem expanded_closing_arm_row (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).writtenNeighbors (n + 4) =
      [if n = 0 then 2 else n + 3, 3 * n + 7, 3 * n + 8, 0] := by
  rw [expanded_chain_written_row n parity n (Nat.le_refl _)]
  simp only [lt_self_iff_false, if_false]
  rw [show n + 7 + 2 * n = 3 * n + 7 by omega,
    show n + 8 + 2 * n = 3 * n + 8 by omega]

theorem expanded_valence (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).ValenceOK :=
  withExplicitHydrogens_preserves_valenceOK _ (ringRaw_wellFormed n parity)
    (ringRaw_valenceOK n parity)

theorem expanded_rule2_masses (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).Rule2MassesKnown :=
  withExplicitHydrogens_preserves_rule2MassesKnown _ (ringRaw_rule2MassesKnown n parity)

end TetraStereo.UniversalProof.NativeRingHydrogenFacts
