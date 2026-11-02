import TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport

private theorem range_lookup_map {Alpha Beta : Type*} (values : List Alpha)
    (f : Alpha → Beta) (fallback : Beta) :
    (List.range values.length).map (fun index =>
      ((listGet? values index).map f).getD fallback) = values.map f := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map, listGet?, Option.map_some, Option.getD_some, List.map_cons]
      exact congrArg (fun rest => f head :: rest) ih

theorem raw_inline_counts (parity : TetrahedralInputParity) (n : Nat)
    (spec : AtomSpec) (retained : spec ∈ (raw parity n).atoms) :
    ∃ count, spec.explicitHydrogens? = some count := by
  change spec ∈ prefixAtoms parity ++ tailAtoms n at retained
  rcases List.mem_append.mp retained with inPrefix | tail
  · simp only [prefixAtoms, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
    rcases inPrefix with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · rcases List.mem_append.mp tail with repeated | terminal
    · have same := (List.mem_replicate.mp repeated).2
      subst spec
      exact ⟨2, rfl⟩
    · have same := List.mem_singleton.mp terminal
      subst spec
      exact ⟨3, rfl⟩

private theorem hydrogen_counts_eq_inline (mol : RawMolecule)
    (inline : ∀ spec ∈ mol.atoms, ∃ count, spec.explicitHydrogens? = some count) :
    (List.range mol.atomCount).map mol.hydrogenCountAt =
      mol.atoms.map AtomSpec.explicitHydrogens := by
  rw [← range_lookup_map mol.atoms AtomSpec.explicitHydrogens 0]
  apply List.map_congr_left
  intro index retained
  have bound := List.mem_range.mp retained
  obtain ⟨spec, lookup⟩ := listGet?_exists_of_lt mol.atoms index bound
  obtain ⟨count, hydrogens⟩ := inline spec
    (listGet?_eq_some_implies_mem mol.atoms index spec lookup)
  simp [hydrogenCountAt, atomAt?, lookup, AtomSpec.explicitHydrogens, hydrogens]

theorem actual_hydrogen_counts (parity : TetrahedralInputParity) (n : Nat) :
    (List.range (raw parity n).atomCount).map (raw parity n).hydrogenCountAt =
      [1, 0, 0, 0, 1, 2] ++ List.replicate n 2 ++ [3] := by
  rw [hydrogen_counts_eq_inline (raw parity n) (raw_inline_counts parity n)]
  simp [raw, prefixAtoms, tailAtoms, centerSpec, bracket, AtomSpec.explicitHydrogens]

theorem actual_total_hydrogens (parity : TetrahedralInputParity) (n : Nat) :
    ((List.range (raw parity n).atomCount).map (raw parity n).hydrogenCountAt).sum =
      2 * n + 7 := by
  rw [actual_hydrogen_counts]
  simp [List.sum_append, List.sum_replicate]
  omega

/-- Actual production expansion has unbounded size, including every materialized hydrogen. -/
theorem expanded_atomCount (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).atomCount = 3 * n + 14 := by
  unfold expanded
  rw [withExplicitHydrogens_atomCount_eq, actual_total_hydrogens, raw_atomCount]
  omega

theorem expanded_original_atom (parity : TetrahedralInputParity) (n index : Nat)
    (spec : AtomSpec) (observed : (raw parity n).atomAt? index = some spec) :
    (expanded parity n).atomAt? index = some (materializedAtomSpec spec) :=
  withExplicitHydrogens_originalAtom (raw parity n) (raw_wellFormed parity n)
    index spec observed

theorem expanded_fresh_hydrogen (parity : TetrahedralInputParity) (n index : Nat)
    (spec : AtomSpec) (fresh : n + 7 ≤ index)
    (observed : (expanded parity n).atomAt? index = some spec) :
    spec = AtomSpec.aliphatic .H ∧ (expanded parity n).incidentBondOrderSum index = 1 :=
  withExplicitHydrogens_freshAtom (raw parity n) (raw_wellFormed parity n) index spec
    (by rwa [raw_atomCount]) observed

private theorem tail_atoms_untagged (n : Nat) (spec : AtomSpec)
    (retained : spec ∈ tailAtoms n) : spec.tetrahedral? = none := by
  rcases List.mem_append.mp retained with repeated | terminal
  · have same := (List.mem_replicate.mp repeated).2
    subst spec
    rfl
  · have same := List.mem_singleton.mp terminal
    subst spec
    rfl

theorem raw_only_center_tagged (parity : TetrahedralInputParity) (n : Nat) :
    ∀ index : Fin (raw parity n).atomCount, ∀ spec,
      (raw parity n).atomAt? index.val = some spec →
        spec.tetrahedral?.isSome = true → index.val = 0 := by
  intro index spec observed tagged
  by_cases inPrefix : index.val < 6
  · interval_cases position : index.val <;>
      simp [raw, prefixAtoms, atomAt?, listGet?] at observed
    all_goals subst spec
    all_goals simp_all [bracket, centerSpec]
  · have lookup : listGet? (tailAtoms n) (index.val - 6) = some spec := by
      change listGet? (prefixAtoms parity ++ tailAtoms n) index.val = some spec at observed
      rw [listGet?_append_right_of_length_le] at observed
      · simpa only [prefixAtoms, List.length_cons, List.length_nil] using observed
      · simpa [prefixAtoms] using Nat.le_of_not_gt inPrefix
    have absent := tail_atoms_untagged n spec
      (listGet?_eq_some_implies_mem (tailAtoms n) (index.val - 6) spec lookup)
    simp [absent] at tagged

/-- Multiple hydrogen demands do not manufacture new annotated centers. -/
theorem expanded_only_center_tagged (parity : TetrahedralInputParity) (n : Nat) :
    ∀ index : Fin (expanded parity n).atomCount, ∀ spec,
      (expanded parity n).atomAt? index.val = some spec →
        spec.tetrahedral?.isSome = true → index.val = 0 := by
  intro index spec observed tagged
  by_cases old : index.val < (raw parity n).atomCount
  · obtain ⟨original, lookup⟩ := listGet?_exists_of_lt (raw parity n).atoms index.val old
    have source : (raw parity n).atomAt? index.val = some original := lookup
    have equal := Option.some.inj
      ((expanded_original_atom parity n index.val original source).symm.trans observed)
    subst spec
    exact raw_only_center_tagged parity n ⟨index.val, old⟩ original source tagged
  · have fresh : n + 7 ≤ index.val := by rw [raw_atomCount] at old; omega
    have same := (expanded_fresh_hydrogen parity n index.val spec fresh observed).1
    subst spec
    cases tagged

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
