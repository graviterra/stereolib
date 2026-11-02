import TetraStereo.UniversalProof.NextFrontier.NativeNitrileLocalExpansion
import TetraStereo.UniversalProof.NextFrontier.NativeNitrilePhysicalAdmission
import TetraStereo.UniversalProof.NativeRawRecordBounds

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

private theorem selected_record_endpoints (center neighbor : Nat) (bond : RawBond)
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

private theorem selected_record_edge (center neighbor : Nat) (bond : RawBond)
    (observed : recordNeighbor? center bond = some neighbor) :
    bond.edgeKey = (min center neighbor, max center neighbor) := by
  rcases selected_record_endpoints center neighbor bond observed with
    ⟨source, target⟩ | ⟨target, source⟩
  · simp only [RawBond.edgeKey, source, target]
  · simp only [RawBond.edgeKey, source, target, Nat.min_comm, Nat.max_comm]

private theorem selected_record_connects (center neighbor : Nat) (bond : RawBond)
    (observed : recordNeighbor? center bond = some neighbor) :
    bond.connects center neighbor = true := by
  rcases selected_record_endpoints center neighbor bond observed with
    ⟨source, target⟩ | ⟨target, source⟩ <;>
    simp [RawBond.connects, source, target]

theorem expanded_records_nodup (parity : TetrahedralInputParity) (n center : Nat) :
    (recordNeighbors (expanded parity n) center).Nodup := by
  have keys : (expanded parity n).bonds.Pairwise (fun left right =>
      left.edgeKey ≠ right.edgeKey) :=
    List.pairwise_map.mp (expanded_admissible parity n).2
  apply keys.filterMap (recordNeighbor? center)
  intro left right different leftAtom leftObserved rightAtom rightObserved equal
  subst rightAtom
  exact different ((selected_record_edge center leftAtom left leftObserved).trans
    (selected_record_edge center leftAtom right rightObserved).symm)

private theorem expanded_record_positive_iff (parity : TetrahedralInputParity)
    (n center neighbor : Nat) :
    neighbor ∈ recordNeighbors (expanded parity n) center ↔
      0 < (expanded parity n).bondOrder center neighbor := by
  constructor
  · intro member
    have different := (recordNeighbor_bounds (expanded_admissible parity n).1 member).2
    obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
    exact (bondOrder_pos_iff_exists_bond _ different.symm).mpr
      ⟨bond, retained, selected_record_connects center neighbor bond observed⟩
  · intro positive
    have different : center ≠ neighbor := by
      intro equal
      subst neighbor
      simp only [bondOrder_self, Nat.lt_irrefl] at positive
    obtain ⟨bond, retained, connected⟩ :=
      (bondOrder_pos_iff_exists_bond _ different).mp positive
    apply List.mem_filterMap.mpr
    refine ⟨bond, retained, ?_⟩
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connected
    rcases connected with ⟨source, target⟩ | ⟨source, target⟩
    · simp [recordNeighbor?, source, target]
    · simp [recordNeighbor?, source, target, Ne.symm different]

theorem expanded_record_row (parity : TetrahedralInputParity) (n center : Nat)
    (bounded : center < 3 * n + 14) :
    (recordNeighbors (expanded parity n) center).Perm
      ((expanded parity n).writtenNeighbors center) := by
  have bound : center < (expanded parity n).atomCount := by rwa [expanded_atomCount]
  have clauses := WrittenNeighborExact.at _ (expanded_written_exact parity n) ⟨center, bound⟩
  apply List.perm_of_nodup_nodup_toFinset_eq
    (expanded_records_nodup parity n center) clauses.1
  apply Finset.ext
  intro neighbor
  simp only [List.mem_toFinset]
  rw [source_writtenNeighbors_mem_iff _ (expanded_admissible parity n).1
    (expanded_written_exact parity n) center bound neighbor,
    expanded_record_positive_iff]

theorem expanded_center_records (parity : TetrahedralInputParity) (n : Nat) :
    (recordNeighbors (expanded parity n) 0).Perm [n + 7, 1, 2, 4] := by
  simpa only [expanded_center_row] using expanded_record_row parity n 0 (by omega)

theorem expanded_amino_records (parity : TetrahedralInputParity) (n : Nat) :
    (recordNeighbors (expanded parity n) 4).Perm [0, n + 8, 5, 6] := by
  simpa only [expanded_amino_row] using expanded_record_row parity n 4 (by omega)

theorem expanded_only_triple (parity : TetrahedralInputParity) (n : Nat)
    (bond : RawBond) (retained : bond ∈ (expanded parity n).bonds)
    (triple : bond.kind = .triple) : bond = ⟨2, 3, .triple⟩ := by
  rcases (withExplicitHydrogens_bonds_mem_iff (raw parity n) bond).mp retained with
    original | ⟨parent, _, hydrogen, _, equal⟩
  · change bond ∈ prefixBonds ++ tailBonds n at original
    rcases List.mem_append.mp original with inPrefix | inTail
    · simp only [prefixBonds, List.mem_cons, List.not_mem_nil, or_false] at inPrefix
      rcases inPrefix with rfl | rfl | rfl | rfl | rfl <;> simp_all
    · obtain ⟨offset, _, rfl⟩ := List.mem_map.mp inTail
      cases triple
  · rw [equal] at triple
    cases triple

theorem expanded_incident_single (parity : TetrahedralInputParity) (n center : Nat)
    (notCarbon : center ≠ 2) (notNitrogen : center ≠ 3)
    (bond : RawBond) (retained : bond ∈ (expanded parity n).bonds)
    (incident : bond.source = center ∨ bond.target = center) : bond.kind = .single := by
  rcases expanded_bond_kinds parity n bond retained with single | triple
  · exact single
  · have same := expanded_only_triple parity n bond retained triple
    subst bond
    exact False.elim (incident.elim (fun same => notCarbon same.symm)
      (fun same => notNitrogen same.symm))

theorem expanded_record_order_one (parity : TetrahedralInputParity) (n center neighbor : Nat)
    (notCarbon : center ≠ 2) (notNitrogen : center ≠ 3)
    (retained : neighbor ∈ recordNeighbors (expanded parity n) center) :
    (expanded parity n).bondOrder center neighbor = 1 := by
  obtain ⟨bond, member, observed⟩ := List.mem_filterMap.mp retained
  have incident : bond.source = center ∨ bond.target = center :=
    (selected_record_endpoints center neighbor bond observed).elim
      (fun ends => Or.inl ends.1) (fun ends => Or.inr ends.1)
  rw [bondOrder_eq_kind_of_mem_connects _ (expanded_admissible parity n).1
    (expanded_admissible parity n).2 member (selected_record_connects center neighbor bond observed),
    expanded_incident_single parity n center notCarbon notNitrogen bond member incident]
  rfl

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
