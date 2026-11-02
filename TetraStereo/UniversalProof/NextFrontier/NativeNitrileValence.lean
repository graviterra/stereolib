import TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

/-! Exact incident bond-order sums and valence admission of the independent nitrile family.
Only the small physical family foundation is imported; no runtime success is assumed. -/

def incidentWeight (index : Nat) (bond : RawBond) : Nat :=
  if bond.source = index ∨ bond.target = index then bond.kind.order else 0

private theorem incident_fold_sum (bonds : List RawBond) (index start : Nat) :
    bonds.foldl (fun total bond =>
      if bond.source == index || bond.target == index then total + bond.kind.order else total)
        start = start + (bonds.map (incidentWeight index)).sum := by
  induction bonds generalizing start with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      by_cases active : head.source = index ∨ head.target = index
      · have activeBool : (head.source == index || head.target == index) = true := by
          simpa using active
        rw [activeBool]
        simp only [↓reduceIte, ih, incidentWeight, if_pos active]
        omega
      · have inactiveBool : (head.source == index || head.target == index) = false := by
          simp [(not_or.mp active).1, (not_or.mp active).2]
        rw [inactiveBool]
        simp only [Bool.false_eq_true, ↓reduceIte, incidentWeight, if_neg active,
          Nat.zero_add]
        exact ih start

theorem raw_incident_sum (parity : TetrahedralInputParity) (n index : Nat) :
    (raw parity n).incidentBondOrderSum index =
      (prefixBonds.map (incidentWeight index)).sum +
        ((tailBonds n).map (incidentWeight index)).sum := by
  unfold incidentBondOrderSum
  rw [incident_fold_sum]
  simp [raw, List.map_append, List.sum_append]

/-- One incoming chain edge and, except at the terminus, one outgoing chain edge. Atom four
has the chain's initial outgoing edge; all other prefix atoms have no tail incidence. -/
theorem tail_incident_sum (n index : Nat) :
    ((tailBonds n).map (incidentWeight index)).sum =
      (if index = 4 then 1 else 0) +
        (if 6 ≤ index ∧ index ≤ n + 6 then 1 else 0) +
          (if 6 ≤ index ∧ index < n + 6 then 1 else 0) := by
  induction n with
  | zero =>
      simp only [tailBonds, List.range_succ, List.range_zero, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      simp only [incidentWeight, tailParent, ParsedBondKind.order]
      split_ifs <;> omega
  | succ n ih =>
      have step : tailBonds (n + 1) = tailBonds n ++ [⟨n + 6, n + 7, .single⟩] := by
        simp [tailBonds, List.range_succ, List.map_append, tailParent, Nat.add_assoc]
      rw [step, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero, incidentWeight, ParsedBondKind.order]
      split_ifs <;> omega

theorem raw_prefix_incident_sums (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).incidentBondOrderSum 0 = 3 ∧
      (raw parity n).incidentBondOrderSum 1 = 1 ∧
      (raw parity n).incidentBondOrderSum 2 = 4 ∧
      (raw parity n).incidentBondOrderSum 3 = 3 ∧
      (raw parity n).incidentBondOrderSum 4 = 3 ∧
      (raw parity n).incidentBondOrderSum 5 = 1 := by
  simp [raw_incident_sum, tail_incident_sum, prefixBonds, incidentWeight,
    ParsedBondKind.order]

theorem raw_tail_incident_sum (parity : TetrahedralInputParity) (n offset : Nat)
    (bound : offset ≤ n) :
    (raw parity n).incidentBondOrderSum (offset + 6) =
      if offset < n then 2 else 1 := by
  rw [raw_incident_sum, tail_incident_sum]
  simp [prefixBonds, incidentWeight, show offset + 6 ≠ 4 by omega,
    show 6 ≤ offset + 6 by omega, show offset + 6 ≤ n + 6 by omega]
  split_ifs <;> omega

private theorem listGet_replicate {Alpha : Type} (count index : Nat) (value : Alpha) :
    listGet? (List.replicate count value) index = if index < count then some value else none := by
  induction count generalizing index with
  | zero => simp [listGet?]
  | succ count ih =>
      cases index with
      | zero => simp [List.replicate_succ, listGet?]
      | succ index =>
          simp only [List.replicate_succ, listGet?]
          rw [ih]
          simp only [Nat.succ_lt_succ_iff]

theorem raw_tail_atom (parity : TetrahedralInputParity) (n offset : Nat)
    (bound : offset ≤ n) :
    (raw parity n).atomAt? (offset + 6) =
      some (bracket .C (if offset < n then 2 else 3)) := by
  change listGet? (prefixAtoms parity ++ tailAtoms n) (offset + 6) = _
  rw [listGet?_append_right_of_length_le]
  · simp only [prefixAtoms, List.length_cons, List.length_nil]
    rw [show offset + 6 - 6 = offset by omega]
    unfold tailAtoms
    by_cases internal : offset < n
    · rw [listGet?_append_left_of_lt]
      · simp [listGet_replicate, internal]
      · simpa only [List.length_replicate] using internal
    · have terminal : offset = n := by omega
      subst offset
      rw [listGet?_append_right_of_length_le]
      · simp [listGet?]
      · simp
  · simp [prefixAtoms]

theorem raw_valence_ok (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).ValenceOK := by
  intro index spec observed
  have bound := listGet?_eq_some_implies_lt (raw parity n).atoms index spec observed
  change index < (raw parity n).atomCount at bound
  rw [raw_atomCount] at bound
  have sums := raw_prefix_incident_sums parity n
  rcases lt_or_ge index 6 with small | large
  · interval_cases index
    · rw [raw_center] at observed
      cases observed
      refine ⟨4, by cases parity <;> decide, ?_⟩
      simp [usedValenceAt, raw_center, centerSpec, bracket, AtomSpec.explicitHydrogens, sums.1]
    · rw [raw_fluorine] at observed
      cases observed
      refine ⟨1, by decide, ?_⟩
      simp [usedValenceAt, raw_fluorine, bracket, AtomSpec.explicitHydrogens, sums.2.1]
    · rw [raw_nitrile_carbon] at observed
      cases observed
      refine ⟨4, by decide, ?_⟩
      simp [usedValenceAt, raw_nitrile_carbon, bracket, AtomSpec.explicitHydrogens, sums.2.2.1]
    · rw [raw_nitrile_nitrogen] at observed
      cases observed
      refine ⟨3, by decide, ?_⟩
      simp [usedValenceAt, raw_nitrile_nitrogen, bracket, AtomSpec.explicitHydrogens,
        sums.2.2.2.1]
    · rw [raw_amino_carbon] at observed
      cases observed
      refine ⟨4, by decide, ?_⟩
      simp [usedValenceAt, raw_amino_carbon, bracket, AtomSpec.explicitHydrogens,
        sums.2.2.2.2.1]
    · rw [raw_amino_nitrogen] at observed
      cases observed
      refine ⟨3, by decide, ?_⟩
      simp [usedValenceAt, raw_amino_nitrogen, bracket, AtomSpec.explicitHydrogens,
        sums.2.2.2.2.2]
  · obtain ⟨offset, rfl⟩ : ∃ offset, index = offset + 6 := ⟨index - 6, by omega⟩
    have inside : offset ≤ n := by omega
    rw [raw_tail_atom parity n offset inside] at observed
    cases observed
    refine ⟨4, ?_, ?_⟩
    · split_ifs <;> decide
    · rw [usedValenceAt, raw_tail_atom parity n offset inside,
        raw_tail_incident_sum parity n offset inside]
      by_cases internal : offset < n <;>
        simp [internal, bracket, AtomSpec.explicitHydrogens]

theorem raw_rule2_masses_known (parity : TetrahedralInputParity) (n : Nat) :
    (raw parity n).Rule2MassesKnown := by
  have carbon : ∃ mass, rule2MassPico? .C none = some mass := by
    obtain ⟨mass, observed⟩ :=
      CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 6 (by decide)
    exact ⟨mass, by simpa [rule2MassPico?, Element.atomicNumber] using observed⟩
  have nitrogen : ∃ mass, rule2MassPico? .N none = some mass := by
    obtain ⟨mass, observed⟩ :=
      CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 7 (by decide)
    exact ⟨mass, by simpa [rule2MassPico?, Element.atomicNumber] using observed⟩
  have fluorine : ∃ mass, rule2MassPico? .F none = some mass := by
    obtain ⟨mass, observed⟩ :=
      CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 9 (by decide)
    exact ⟨mass, by simpa [rule2MassPico?, Element.atomicNumber] using observed⟩
  intro spec retained
  change spec ∈ prefixAtoms parity ++ tailAtoms n at retained
  rcases List.mem_append.mp retained with inPrefix | inTail
  · simp only [prefixAtoms, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
    rcases inPrefix with rfl | rfl | rfl | rfl | rfl | rfl
    · exact carbon
    · exact fluorine
    · exact carbon
    · exact nitrogen
    · exact carbon
    · exact nitrogen
  · rcases List.mem_append.mp inTail with repeated | terminal
    · have same := (List.mem_replicate.mp repeated).2
      subst spec
      exact carbon
    · have same := List.mem_singleton.mp terminal
      subst spec
      exact carbon

theorem expanded_valence_ok (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).ValenceOK :=
  withExplicitHydrogens_preserves_valenceOK _ (raw_wellFormed parity n) (raw_valence_ok parity n)

theorem expanded_rule2_masses_known (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).Rule2MassesKnown :=
  withExplicitHydrogens_preserves_rule2MassesKnown _ (raw_rule2_masses_known parity n)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
