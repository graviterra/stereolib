import TetraStereo.UniversalProof.NextFrontier.NativeRingHydrogenFacts
import TetraStereo.UniversalProof.NativeRawRecordBounds

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

theorem recordNeighbor_endpoints (center neighbor : Nat) (bond : RawBond)
    (observed : recordNeighbor? center bond = some neighbor) :
    (bond.source = center ∧ bond.target = neighbor) ∨
      (bond.target = center ∧ bond.source = neighbor) := by
  unfold recordNeighbor? at observed
  split at observed
  · rename_i source
    exact Or.inl ⟨by simpa using source, Option.some.inj observed⟩
  · split at observed
    · rename_i target
      exact Or.inr ⟨by simpa using target, Option.some.inj observed⟩
    · cases observed

theorem recordNeighbor_edgeKey (center neighbor : Nat) (bond : RawBond)
    (observed : recordNeighbor? center bond = some neighbor) :
    bond.edgeKey = (min center neighbor, max center neighbor) := by
  rcases recordNeighbor_endpoints center neighbor bond observed with
    ⟨source, target⟩ | ⟨target, source⟩
  · simp only [RawBond.edgeKey, source, target]
  · simp only [RawBond.edgeKey, source, target, Nat.min_comm, Nat.max_comm]

/-- Unordered bond uniqueness rules out duplicate physical neighbors without requiring distinct
elements, distinct priorities, or terminal ligands. -/
theorem recordNeighbors_nodup (raw : RawMolecule) (unique : raw.BondRecordsUnique)
    (center : Nat) : (recordNeighbors raw center).Nodup := by
  have keys : raw.bonds.Pairwise (fun left right => left.edgeKey ≠ right.edgeKey) :=
    List.pairwise_map.mp unique
  apply keys.filterMap (recordNeighbor? center)
  intro left right different leftAtom leftObserved rightAtom rightObserved equal
  subst rightAtom
  exact different ((recordNeighbor_edgeKey center leftAtom left leftObserved).trans
    (recordNeighbor_edgeKey center leftAtom right rightObserved).symm)

theorem recordNeighbor_connects (center neighbor : Nat) (bond : RawBond)
    (observed : recordNeighbor? center bond = some neighbor) :
    bond.connects center neighbor = true := by
  rcases recordNeighbor_endpoints center neighbor bond observed with
    ⟨source, target⟩ | ⟨target, source⟩ <;>
    simp [RawBond.connects, source, target]

theorem recordNeighbor_positive_iff (raw : RawMolecule) (well : raw.WellFormed)
    (center neighbor : Nat) :
    neighbor ∈ recordNeighbors raw center ↔ 0 < raw.bondOrder center neighbor := by
  constructor
  · intro member
    have different := (recordNeighbor_bounds well member).2
    obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
    exact (raw.bondOrder_pos_iff_exists_bond different.symm).mpr
      ⟨bond, retained, recordNeighbor_connects center neighbor bond observed⟩
  · intro positive
    have different : center ≠ neighbor := by
      intro equal
      subst neighbor
      have impossible : 0 < (0 : Nat) := by
        simpa only [raw.bondOrder_self] using positive
      exact (Nat.lt_irrefl 0) impossible
    obtain ⟨bond, retained, connects⟩ := (raw.bondOrder_pos_iff_exists_bond different).mp positive
    apply List.mem_filterMap.mpr
    refine ⟨bond, retained, ?_⟩
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
    rcases connects with ⟨source, target⟩ | ⟨source, target⟩
    · simp [recordNeighbor?, source, target]
    · simp [recordNeighbor?, source, target, Ne.symm different]

/-- Every admitted exact written row is a permutation of the physical record projection, even
when two carbon ligands tie in their first atomic number. -/
theorem written_perm_records (raw : RawMolecule) (admitted : raw.StereochemicalAdmissible)
    (center : Nat) (bounded : center < raw.atomCount) :
    (raw.writtenNeighbors center).Perm (recordNeighbors raw center) := by
  have clauses := WrittenNeighborExact.at raw admitted.2 ⟨center, bounded⟩
  apply List.perm_of_nodup_nodup_toFinset_eq clauses.1
    (recordNeighbors_nodup raw admitted.1.2 center)
  apply Finset.ext
  intro neighbor
  simp only [List.mem_toFinset]
  rw [source_writtenNeighbors_mem_iff raw admitted.1.1 admitted.2 center bounded neighbor,
    recordNeighbor_positive_iff raw admitted.1.1 center neighbor]

theorem expanded_bonds_single (n : Nat) (parity : TetrahedralInputParity)
    (bond : RawBond) (member : bond ∈ (expanded n parity).bonds) :
    bond.kind = .single := by
  rcases (withExplicitHydrogens_bonds_mem_iff (ringRaw n parity) bond).mp member with
    original | ⟨parent, _, hydrogen, _, equal⟩
  · exact ringBonds_kind_single n bond original
  · rw [equal]

theorem expanded_record_bond_one (n : Nat) (parity : TetrahedralInputParity)
    (center neighbor : Nat) (member : neighbor ∈ recordNeighbors (expanded n parity) center) :
    (expanded n parity).bondOrder center neighbor = 1 := by
  obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
  have admitted := (expanded_stereochemical_admissible n parity).1
  rw [bondOrder_eq_kind_of_mem_connects _ admitted.1 admitted.2 retained
    (recordNeighbor_connects center neighbor bond observed), expanded_bonds_single n parity bond retained]
  rfl

theorem expanded_records_perm_written (n : Nat) (parity : TetrahedralInputParity)
    (center : Nat) (bounded : center < 3 * n + 9) :
    (recordNeighbors (expanded n parity) center).Perm
      ((expanded n parity).writtenNeighbors center) :=
  (written_perm_records _ (expanded_stereochemical_admissible n parity) center
    (by rwa [expanded_atom_count])).symm

theorem expanded_root_records (n : Nat) (parity : TetrahedralInputParity) :
    (recordNeighbors (expanded n parity) 0).Perm [n + 5, 1, 2, n + 4] := by
  simpa only [expanded_root_written_row] using expanded_records_perm_written n parity 0 (by omega)

theorem expanded_left_records (n : Nat) (parity : TetrahedralInputParity) :
    (recordNeighbors (expanded n parity) 2).Perm [0, n + 6, 3, 4] := by
  simpa only [expanded_chlorinated_arm_row] using expanded_records_perm_written n parity 2 (by omega)

theorem expanded_right_records (n : Nat) (parity : TetrahedralInputParity) :
    (recordNeighbors (expanded n parity) (n + 4)).Perm
      [if n = 0 then 2 else n + 3, 3 * n + 7, 3 * n + 8, 0] := by
  simpa only [expanded_closing_arm_row] using
    expanded_records_perm_written n parity (n + 4) (by omega)

end TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
