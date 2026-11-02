import TetraStereo.UniversalProof.NextFrontier.NativeRingPhysicalAdjacency

set_option autoImplicit false

namespace TetraStereo.UniversalProof.GeneralRingPhysicalAdmission

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain

theorem ringRaw_valenceOK (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).ValenceOK := by
  intro idx atom h
  have hbounded := ringRaw_atomAt?_bounded n parity h
  rcases lt_or_ge idx 4 with hsmall | hbig
  · interval_cases idx
    · rw [ringRaw_atomAt_zero] at h; injection h with h; subst h
      refine ⟨4, by cases parity <;> decide, ?_⟩
      have hle := ringRaw_incidentSum_le_row n parity 0 (by omega)
      rw [ringRaw_written_row_length_zero n parity] at hle
      rw [RawMolecule.usedValenceAt, ringRaw_atomAt_zero]
      simp only [taggedCarbon, carbon, AtomSpec.explicitHydrogens, Option.getD_some]
      omega
    · rw [ringRaw_atomAt_one] at h; injection h with h; subst h
      refine ⟨1, by decide, ?_⟩
      have hle := ringRaw_incidentSum_le_row n parity 1 (by omega)
      rw [ringRaw_written_row_length_one n parity] at hle
      rw [RawMolecule.usedValenceAt, ringRaw_atomAt_one]
      simp only [AtomSpec.explicitHydrogens, Option.getD_some]
      omega
    · rw [ringRaw_atomAt_two] at h; injection h with h; subst h
      refine ⟨4, by decide, ?_⟩
      have hle := ringRaw_incidentSum_two_le n parity
      rw [RawMolecule.usedValenceAt, ringRaw_atomAt_two]
      simp only [carbon, AtomSpec.explicitHydrogens, Option.getD_some]
      omega
    · rw [ringRaw_atomAt_three] at h; injection h with h; subst h
      refine ⟨1, by decide, ?_⟩
      have hle := ringRaw_incidentSum_le_row n parity 3 (by omega)
      rw [ringRaw_written_row_length_three n parity] at hle
      rw [RawMolecule.usedValenceAt, ringRaw_atomAt_three]
      simp only [AtomSpec.explicitHydrogens, Option.getD_some]
      omega
  · obtain ⟨k, rfl⟩ : ∃ k, idx = k + 4 := ⟨idx - 4, by omega⟩
    rw [ringRaw_atomAt_chain n parity k (by omega)] at h
    injection h with h; subst h
    refine ⟨4, by decide, ?_⟩
    have hle := ringRaw_incidentSum_chain_le n parity k (by omega)
    rw [RawMolecule.usedValenceAt, ringRaw_atomAt_chain n parity k (by omega)]
    simp only [carbon, AtomSpec.explicitHydrogens, Option.getD_some]
    omega

theorem normalizeUnspecifiedBond_of_single (mol : RawMolecule) (b : RawBond)
    (h : b.kind = ParsedBondKind.single) : mol.normalizeUnspecifiedBond b = b := by
  unfold RawMolecule.normalizeUnspecifiedBond
  rw [h]

theorem map_id_of_fixed {α : Type} {f : α → α} :
    ∀ l : List α, (∀ a ∈ l, f a = a) → l.map f = l
  | [], _ => rfl
  | a :: t, h => by
      rw [List.map_cons, h a (List.mem_cons_self), map_id_of_fixed t
        (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem ringRaw_normalizeUnspecifiedBonds (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).normalizeUnspecifiedBonds = ringRaw n parity := by
  unfold RawMolecule.normalizeUnspecifiedBonds
  have hmap : (ringRaw n parity).bonds.map (ringRaw n parity).normalizeUnspecifiedBond =
      (ringRaw n parity).bonds := by
    apply map_id_of_fixed
    intro b hb
    rw [ringRaw_bonds] at hb
    exact normalizeUnspecifiedBond_of_single (ringRaw n parity) b (ringBonds_kind_single n b hb)
  rw [hmap]

theorem ringRaw_normalized_parsed (n : ℕ) (parity : TetrahedralInputParity) :
    (normalizeRawMolecule (ringRaw n parity)).parsed = ringRaw n parity := by
  show (ringRaw n parity).normalizeUnspecifiedBonds = ringRaw n parity
  exact ringRaw_normalizeUnspecifiedBonds n parity

def ringRawCertified (n : ℕ) (parity : TetrahedralInputParity) :
    CertifiedChemistryNormalizationResult where
  result := normalizeRawMolecule (ringRaw n parity)
  admissible := by rw [ringRaw_normalized_parsed]; exact ringRaw_admissible n parity
  writtenNeighborExact := by rw [ringRaw_normalized_parsed]; exact ringRaw_writtenNeighborExact n parity
  valenceOK := by rw [ringRaw_normalized_parsed]; exact ringRaw_valenceOK n parity
  rule2MassesKnown := by rw [ringRaw_normalized_parsed]; exact ringRaw_rule2MassesKnown n parity

theorem ringRawCertified_result_parsed (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRawCertified n parity).result.parsed = ringRaw n parity := ringRaw_normalized_parsed n parity

theorem ringRawCertified_stereochemicalAdmissible (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRawCertified n parity).result.parsed.StereochemicalAdmissible :=
  (ringRawCertified n parity).stereochemicalAdmissible

theorem ringRaw_actual_certified_intake (n : Nat) (parity : TetrahedralInputParity) :
    normalizeRawMoleculeCertified? (ringRaw n parity) = some (ringRawCertified n parity) := by
  have hparsed := ringRaw_normalized_parsed n parity
  have hadm : (normalizeRawMolecule (ringRaw n parity)).parsed.admissible? = true := by
    rw [hparsed]; exact (RawMolecule.admissible?_eq_true_iff _).mpr (ringRaw_admissible n parity)
  have hwn : (normalizeRawMolecule (ringRaw n parity)).parsed.writtenNeighborExact? = true := by
    rw [hparsed]
    exact (RawMolecule.writtenNeighborExact?_eq_true_iff _).mpr (ringRaw_writtenNeighborExact n parity)
  have hval : (normalizeRawMolecule (ringRaw n parity)).parsed.valenceOK? = true := by
    rw [hparsed]; exact (RawMolecule.valenceOK?_eq_true_iff _).mpr (ringRaw_valenceOK n parity)
  have hmass : (normalizeRawMolecule (ringRaw n parity)).parsed.rule2MassesKnown? = true := by
    rw [hparsed]; exact (RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr (ringRaw_rule2MassesKnown n parity)
  have hintro : (normalizeRawMolecule (ringRaw n parity)).parsed.introductionPredecessorsValid? = true := by
    rw [hparsed]
    exact ringRaw_introduction_valid n parity
  unfold normalizeRawMoleculeCertified? ChemistryNormalizationResult.certify? ringRawCertified
  rw [if_pos hintro, dif_pos hadm, dif_pos hwn, dif_pos hval, dif_pos hmass]

theorem ringRaw_normalizeCertified?_isSome (n : Nat) (parity : TetrahedralInputParity) :
    (normalizeRawMoleculeCertified? (ringRaw n parity)).isSome = true := by
  simp only [ringRaw_actual_certified_intake, Option.isSome_some]

theorem general_ring_physical_admission (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).atomCount = n + 5 ∧
    (ringRaw n parity).bonds.length = n + 5 ∧
    (ringRaw n parity).neighborOrder.length = n + 5 ∧
    (ringRaw n parity).Admissible ∧
    (ringRaw n parity).WrittenNeighborExact ∧
    (ringRaw n parity).ValenceOK ∧
    (ringRaw n parity).Rule2MassesKnown :=
  ⟨atom_count n parity, bond_count n parity, row_count n parity, ringRaw_admissible n parity,
    ringRaw_writtenNeighborExact n parity, ringRaw_valenceOK n parity, ringRaw_rule2MassesKnown n parity⟩

theorem general_ring_physical_domain_inhabited (n : ℕ) (parity : TetrahedralInputParity) :
    (ringRaw n parity).StereochemicalAdmissible ∧
      (normalizeRawMoleculeCertified? (ringRaw n parity)).isSome = true :=
  ⟨⟨ringRaw_admissible n parity, ringRaw_writtenNeighborExact n parity⟩,
    ringRaw_normalizeCertified?_isSome n parity⟩

theorem general_ring_loop_parallel_free (n : Nat) (parity : TetrahedralInputParity) :
    (∀ bond ∈ (ringRaw n parity).bonds, bond.source ≠ bond.target) ∧
      ((ringRaw n parity).bonds.map RawBond.edgeKey).Nodup := by
  refine ⟨?_, ringRaw_bondRecordsUnique n parity⟩
  intro bond member
  exact (ringRaw_wellFormed n parity bond member).2.2

end TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
