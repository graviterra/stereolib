import TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.CertifiedFamilyValenceRecoveryProofs.CertifiedFamilyValenceRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery

/-!
Proposed extension of the physical arbitrary-positive-size, arbitrary-parity family.
Valence is derived from its actual atom and single-bond records. Actual certify? success
is then derived from all reflected intake checks, including the accepted legacy unknown
introduction prefix. No parser success or desired report
is an input. Kernel, human, external-source and general string parsing reviews remain OPEN.
-/

theorem single_contributions_eq_written_length (bonds : List RawBond) (center : ℕ)
    (single : ∀ bond ∈ bonds, bond.kind = .single) :
    (bonds.map (incidentContributionAt center)).sum =
      (bonds.filterMap (wnFilter center)).length := by
  induction bonds with
  | nil => rfl
  | cons bond tail ih =>
      have kind := single bond (List.mem_cons_self)
      have rest := ih (fun selected member => single selected (List.mem_cons_of_mem bond member))
      simp only [List.map_cons, List.sum_cons, List.filterMap_cons]
      by_cases source : bond.source = center
      · have contribution : incidentContributionAt center bond = 1 := by
          simp [incidentContributionAt, source, kind, ParsedBondKind.order]
        have filtered : wnFilter center bond = some bond.target := by
          simp [wnFilter, source]
        rw [contribution, filtered]
        simp only [List.length_cons, rest]
        omega
      · by_cases target : bond.target = center
        · have contribution : incidentContributionAt center bond = 1 := by
            simp [incidentContributionAt, target, kind, ParsedBondKind.order]
          have filtered : wnFilter center bond = some bond.source := by
            simp [wnFilter, source, target]
          rw [contribution, filtered]
          simp only [List.length_cons, rest]
          omega
        · have contribution : incidentContributionAt center bond = 0 := by
            simp [incidentContributionAt, source, target]
          have filtered : wnFilter center bond = none := by
            simp [wnFilter, source, target]
          rw [contribution, filtered]
          simpa only [Nat.zero_add] using rest

theorem family_incident_order_eq_raw_row_length (n : ℕ)
    (parity : ℕ → TetrahedralInputParity) (center : ℕ) :
    (family n parity).incidentBondOrderSum center =
      ((rawFamily n parity).writtenNeighbors center).length := by
  rw [incidentBondOrderSum_eq_incidentContributionAt_sum, family_bonds,
    single_contributions_eq_written_length (familyBonds n) center (familyBonds_kind_single n),
    rawFamily_writtenNeighbors_fallback]

private theorem sum_range_indicator (k i : ℕ) :
    ((List.range k).map (fun j => if j = i then 1 else 0)).sum =
      if i < k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      by_cases small : i < k
      · have different : k ≠ i := by omega
        simp [small, different, show i < k + 1 by omega]
      · by_cases equal : k = i
        · subst i
          simp
        · have large : ¬ i < k + 1 := by omega
          simp [small, equal, large]

theorem chain_contributions (n i : ℕ) (hn : 1 ≤ n) (hi : i < n) :
    ((chainBonds n).map (incidentContributionAt (5 * i))).sum =
      (if i + 1 < n then 1 else 0) + (if 0 < i then 1 else 0) := by
  unfold chainBonds
  rw [List.map_map]
  change ((List.range (n - 1)).map (fun j => incidentContributionAt (5 * i)
    (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond))).sum = _
  have contributions :
      (fun j => incidentContributionAt (5 * i)
        (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond)) =
      (fun j => (if j = i then 1 else 0) +
        (if 0 < i then if j = i - 1 then 1 else 0 else 0)) := by
    funext j
    by_cases same : j = i
    · subst j
      by_cases positive : 0 < i
      · have different : i ≠ i - 1 := by omega
        simp [incidentContributionAt, ParsedBondKind.order, positive, different]
      · simp [incidentContributionAt, ParsedBondKind.order, positive]
    · by_cases positive : 0 < i
      · by_cases previous : j = i - 1
        · have target : 5 * j + 5 = 5 * i := by omega
          have value : incidentContributionAt (5 * i)
              (⟨5 * j, 5 * j + 5, ParsedBondKind.single⟩ : RawBond) = 1 := by
            simp [incidentContributionAt, target, ParsedBondKind.order]
          rw [value, if_neg same, if_pos positive, if_pos previous]
        · have source : 5 * j ≠ 5 * i := by omega
          have target : 5 * j + 5 ≠ 5 * i := by omega
          simp [incidentContributionAt, source, target, same, positive, previous]
      · have source : 5 * j ≠ 5 * i := by omega
        have target : 5 * j + 5 ≠ 5 * i := by omega
        simp [incidentContributionAt, source, target, same, positive]
  rw [contributions, List.sum_map_add, sum_range_indicator]
  have outgoing : (i < n - 1) ↔ i + 1 < n := by omega
  by_cases positive : 0 < i
  · have incoming : i - 1 < n - 1 := by omega
    simp [positive, sum_range_indicator, incoming, outgoing]
  · simp [positive, outgoing]

theorem backbone_written_degree (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (i : ℕ) (hn : 1 ≤ n) (hi : i < n) :
    ((rawFamily n parity).writtenNeighbors (5 * i)).length = 4 := by
  rw [rawFamily_writtenNeighbors_fallback]
  simp only [familyBonds, List.filterMap_append, List.length_append]
  have chain : ((chainBonds n).filterMap (wnFilter (5 * i))).length =
      (if i + 1 < n then 1 else 0) + (if 0 < i then 1 else 0) := by
    rw [← single_contributions_eq_written_length]
    · exact chain_contributions n i hn hi
    · intro bond member
      rcases List.mem_map.mp member with ⟨j, _, rfl⟩
      rfl
  have pendant : ((pendantBonds n).filterMap (wnFilter (5 * i))).length = 1 := by
    have row : ((pendantBonds n).filterMap (wnFilter (5 * i))) = [5 * i + 1] := by
      simpa only [pendantBonds, Nat.add_zero] using
        (wn_source_single (k := n) (i := i) (u := 0) (v := 1)
          (by omega) (by omega) (by omega) hi)
    exact congrArg List.length row
  have link : ((linkBonds n).filterMap (wnFilter (5 * i))).length = 1 := by
    rw [linkBonds, List.filterMap_map]
    change ((List.range n).filterMap (fun j => wnFilter (5 * i)
      (⟨5 * j, 5 * n + j, ParsedBondKind.single⟩ : RawBond))).length = 1
    rw [filterMap_congr_local (g := fun j => if j = i then some (5 * n + i) else none) ?_]
    · rw [filterMap_range_singleton, if_pos hi]
      rfl
    · intro j member
      have bound := List.mem_range.mp member
      unfold wnFilter
      dsimp only
      by_cases equal : j = i
      · subst j
        simp only [if_true]
      · have source : 5 * j ≠ 5 * i := by omega
        have target : 5 * n + j ≠ 5 * i := by omega
        simp only [if_neg source, if_neg target, if_neg equal]
  have terminalH : (terminalHBonds n).filterMap (wnFilter (5 * i)) = [] :=
    segment_none _ (by intro j hj; constructor <;> dsimp only <;> omega)
  have terminalF : (terminalFBonds n).filterMap (wnFilter (5 * i)) = [] :=
    segment_none _ (by intro j hj; constructor <;> dsimp only <;> omega)
  have terminalBr : (terminalBrBonds n).filterMap (wnFilter (5 * i)) = [] :=
    segment_none _ (by intro j hj; constructor <;> dsimp only <;> omega)
  have left : ((capLeftBonds n).filterMap (wnFilter (5 * i))).length =
      if i = 0 then 1 else 0 := by
    unfold capLeftBonds wnFilter
    by_cases zero : i = 0
    · subst i
      simp
    · simp [show (0 : ℕ) ≠ 5 * i by omega, show 6 * n ≠ 5 * i by omega, zero]
  have right : ((capRightBonds n).filterMap (wnFilter (5 * i))).length =
      if i + 1 = n then 1 else 0 := by
    unfold capRightBonds wnFilter
    by_cases last : i + 1 = n
    · have source : 5 * n - 5 = 5 * i := by omega
      simp [source, last]
    · have source : 5 * n - 5 ≠ 5 * i := by omega
      have target : 6 * n + 1 ≠ 5 * i := by omega
      simp [source, target, last]
  rw [chain, pendant, terminalH, terminalF, terminalBr, link, left, right]
  have incoming : (0 < i) ↔ i ≠ 0 := by omega
  have outgoing : (i + 1 < n) ↔ i + 1 ≠ n := by omega
  by_cases zero : i = 0 <;> by_cases last : i + 1 = n <;> simp_all
  all_goals omega

theorem atomAtIndex_explicit_hydrogens_zero (n : ℕ)
    (parity : ℕ → TetrahedralInputParity) (idx : ℕ) :
    (atomAtIndex n parity idx).explicitHydrogens = 0 := by
  unfold atomAtIndex
  split
  · split <;> rfl
  · rfl

theorem family_used_valence_eq_raw_row_length (n : ℕ)
    (parity : ℕ → TetrahedralInputParity) (idx : ℕ)
    (bound : idx < (family n parity).atomCount) :
    (family n parity).usedValenceAt idx =
      ((rawFamily n parity).writtenNeighbors idx).length := by
  unfold usedValenceAt
  rw [family_atomAt? n parity idx bound]
  change (atomAtIndex n parity idx).explicitHydrogens +
    (family n parity).incidentBondOrderSum idx = _
  rw [atomAtIndex_explicit_hydrogens_zero, Nat.zero_add,
    family_incident_order_eq_raw_row_length]

theorem family_valenceOK (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (family n parity).ValenceOK := by
  intro idx atom observed
  have bound : idx < (family n parity).atomCount :=
    listGet?_eq_some_implies_lt _ _ _ observed
  have size : idx < 6 * n + 2 := by simpa only [family_atomCount] using bound
  have atomEq : atom = atomAtIndex n parity idx := by
    rw [family_atomAt? n parity idx bound] at observed
    exact (Option.some.inj observed).symm
  subst atom
  rw [family_used_valence_eq_raw_row_length n parity idx bound]
  by_cases block : idx < 5 * n
  · let i := idx / 5
    have divmod : 5 * i + idx % 5 = idx := Nat.div_add_mod idx 5
    have inside : i < n := by omega
    have roles : idx % 5 = 0 ∨ idx % 5 = 1 ∨ idx % 5 = 2 ∨
        idx % 5 = 3 ∨ idx % 5 = 4 := by omega
    rcases roles with role | role | role | role | role
    · have index : idx = 5 * i := by omega
      rw [index, atomAtIndex_backbone n parity i inside,
        backbone_written_degree n parity i hn inside]
      exact ⟨4, by decide, le_rfl⟩
    · have index : idx = 5 * i + 1 := by omega
      rw [index, atomAtIndex_tag n parity i inside,
        tag_writtenNeighbors n parity i hn inside]
      exact ⟨4, by simp [pendantCarbon, AtomSpec.aliphatic, AtomSpec.allowedValences,
        Element.allowedValences], le_rfl⟩
    · have index : idx = 5 * i + 2 := by omega
      rw [index, atomAtIndex_terminalH n parity i inside,
        terminalH_writtenNeighbors n parity i hn inside]
      exact ⟨1, by decide, le_rfl⟩
    · have index : idx = 5 * i + 3 := by omega
      rw [index, atomAtIndex_terminalF n parity i inside,
        terminalF_writtenNeighbors n parity i hn inside]
      exact ⟨1, by decide, le_rfl⟩
    · have index : idx = 5 * i + 4 := by omega
      rw [index, atomAtIndex_terminalBr n parity i inside,
        terminalBr_writtenNeighbors n parity i hn inside]
      exact ⟨1, by decide, le_rfl⟩
  · have hydrogen : atomAtIndex n parity idx = terminalHydrogen := by
      simp only [atomAtIndex, if_neg block]
    rw [hydrogen]
    refine ⟨1, by decide, ?_⟩
    by_cases link : idx < 6 * n
    · let j := idx - 5 * n
      have index : idx = 5 * n + j := by omega
      have inside : j < n := by omega
      simpa only [index, linkH_writtenNeighbors n parity j hn inside] using
        (Nat.le_refl (1 : ℕ))
    · have ends : idx = 6 * n ∨ idx = 6 * n + 1 := by omega
      rcases ends with rfl | rfl
      · simpa only [capLeftH_writtenNeighbors n parity hn] using (Nat.le_refl (1 : ℕ))
      · simpa only [capRightH_writtenNeighbors n parity hn] using (Nat.le_refl (1 : ℕ))

theorem family_normalized_valenceOK (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) : (normalizeRawMolecule (family n parity)).parsed.ValenceOK := by
  rw [family_actual_normalized_parsed]
  exact family_valenceOK n parity hn

def certifiedFamily (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    CertifiedChemistryNormalizationResult where
  result := normalizeRawMolecule (family n parity)
  admissible := (family_normalized_admissible n parity hn).1
  writtenNeighborExact := (family_normalized_admissible n parity hn).2
  valenceOK := family_normalized_valenceOK n parity hn
  rule2MassesKnown := family_normalized_masses n parity

theorem family_actual_certified_normalization (n : ℕ)
    (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    normalizeRawMoleculeCertified? (family n parity) = some (certifiedFamily n parity hn) := by
  have introduction :
      (normalizeRawMolecule (family n parity)).parsed.introductionPredecessorsValid? = true := by
    rw [family_actual_normalized_parsed]
    change (decide (0 ≤ (family n parity).atomCount) && true) = true
    simp
  have admission : (normalizeRawMolecule (family n parity)).parsed.admissible? = true :=
    ((normalizeRawMolecule (family n parity)).parsed.admissible?_eq_true_iff).mpr
      (family_normalized_admissible n parity hn).1
  have written : (normalizeRawMolecule (family n parity)).parsed.writtenNeighborExact? = true :=
    ((normalizeRawMolecule (family n parity)).parsed.writtenNeighborExact?_eq_true_iff).mpr
      (family_normalized_admissible n parity hn).2
  have valence : (normalizeRawMolecule (family n parity)).parsed.valenceOK? = true :=
    ((normalizeRawMolecule (family n parity)).parsed.valenceOK?_eq_true_iff).mpr
      (family_normalized_valenceOK n parity hn)
  have masses : (normalizeRawMolecule (family n parity)).parsed.rule2MassesKnown? = true :=
    ((normalizeRawMolecule (family n parity)).parsed.rule2MassesKnown?_eq_true_iff).mpr
      (family_normalized_masses n parity)
  unfold normalizeRawMoleculeCertified? ChemistryNormalizationResult.certify? certifiedFamily
  rw [if_pos introduction, dif_pos admission, dif_pos written, dif_pos valence, dif_pos masses]

theorem certifiedFamily_parsed (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (certifiedFamily n parity hn).result.parsed = family n parity :=
  family_actual_normalized_parsed n parity

theorem positive_family_certified_intake (n : ℕ)
    (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    ∃ certified : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeCertified? (family n parity) = some certified ∧
      certified.result = normalizeRawMolecule (family n parity) ∧
      certified.result.parsed = family n parity ∧
      certified.result.parsed.atomCount = 6 * n + 2 ∧
      certified.result.parsed.bonds.length = 6 * n + 1 := by
  refine ⟨certifiedFamily n parity hn, family_actual_certified_normalization n parity hn,
    rfl, certifiedFamily_parsed n parity hn, ?_, ?_⟩
  · rw [certifiedFamily_parsed, family_atomCount]
  · rw [certifiedFamily_parsed, family_bonds, familyBonds_length n hn]

theorem family_valence_check (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) :
    (family n parity).valenceOK? = true :=
  ((family n parity).valenceOK?_eq_true_iff).mpr (family_valenceOK n parity hn)

theorem certifiedFamily_report_intake (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) :
    FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.FirstZTagDomain
        (certifiedFamily n parity hn).result.parsed ∧
      NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery.OrdinarySourceInput
        (certifiedFamily n parity hn).result.parsed ∧
      (certifiedFamily n parity hn).result.parsed.withExplicitHydrogens =
        (certifiedFamily n parity hn).result.parsed := by
  rw [certifiedFamily_parsed]
  exact ⟨family_first_z_domain n parity hn, family_ordinary_source_input n parity hn,
    family_expansion_identity n parity⟩

end TetraStereo.UniversalProof.CertifiedFamilyValenceRecoveryProofs.CertifiedFamilyValenceRecovery
