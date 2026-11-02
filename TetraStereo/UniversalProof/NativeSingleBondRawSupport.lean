import TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery
import TetraStereo.UniversalProof.NativeFamilyRawSupport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ChronologicalFamilyPhysicalBridge
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

private theorem single_fold_le_one (bonds : List RawBond) (u v : ℕ) :
    ∀ acc, acc ≤ 1 → (∀ bond ∈ bonds, bond.kind = .single) →
    bonds.foldl (fun order bond =>
      if bond.directedConnects u v then max order bond.kind.order else order) acc ≤ 1 := by
  induction bonds with
  | nil => intro acc bound single; exact bound
  | cons bond bonds ih =>
      intro acc bound single
      simp only [List.foldl_cons]
      apply ih
      · have kind := single bond List.mem_cons_self
        rw [kind]
        split <;> simp_all [ParsedBondKind.order]
      · intro selected member
        exact single selected (List.mem_cons_of_mem bond member)

theorem all_single_bond_order_le_one (raw : RawMolecule)
    (single : ∀ bond ∈ raw.bonds, bond.kind = .single) (u v : ℕ) :
    raw.bondOrder u v ≤ 1 := by
  by_cases same : u = v
  · simpa only [RawMolecule.bondOrder, if_pos same] using Nat.zero_le (1 : ℕ)
  · simp only [RawMolecule.bondOrder, if_neg same]
    apply max_le
    · exact single_fold_le_one raw.bonds u v 0 (Nat.zero_le (1 : ℕ)) single
    · exact single_fold_le_one raw.bonds v u 0 (Nat.zero_le (1 : ℕ)) single

theorem all_single_incident_order (raw : RawMolecule) (well : raw.WellFormed)
    (single : ∀ bond ∈ raw.bonds, bond.kind = .single) (center other : ℕ)
    (member : other ∈ recordNeighbors raw center) : raw.bondOrder center other = 1 := by
  obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
  have distinct := (well bond retained).2.2
  have positive : 0 < raw.bondOrder center other := by
    apply (TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery.bondOrder_pos_iff_connect
      raw center other).mpr
    unfold recordNeighbor? at observed
    by_cases source : bond.source = center
    · have target : bond.target = other := by simpa [source] using observed
      refine ⟨?_, bond, retained, ?_⟩
      · simpa only [source, target] using distinct
      · simp [RawBond.connects, source, target]
    · have target : bond.target = center := by
        by_contra absent
        simp [source, absent] at observed
      have sourceOther : bond.source = other := by simpa [source, target] using observed
      refine ⟨?_, bond, retained, ?_⟩
      · intro equal
        exact distinct (sourceOther.trans (equal.symm.trans target.symm))
      · simp [RawBond.connects, sourceOther, target]
  exact Nat.le_antisymm (all_single_bond_order_le_one raw single center other)
    (Nat.succ_le_of_lt positive)

/-- Counts actual incident records, including the source-first policy for a loop. No graph
uniqueness, valence conclusion or callback is assumed. -/
theorem all_single_incident_fold (bonds : List RawBond) (center : ℕ)
    (single : ∀ bond ∈ bonds, bond.kind = .single) :
    ∀ acc, bonds.foldl (fun total bond =>
      if bond.source == center || bond.target == center then total + bond.kind.order else total) acc =
      acc + (bonds.filterMap (recordNeighbor? center)).length := by
  revert single
  induction bonds with
  | nil => intro single acc; simp
  | cons bond tail ih =>
      intro single acc
      have kind := single bond List.mem_cons_self
      have tailSingle : ∀ selected ∈ tail, selected.kind = .single := by
        intro selected retained
        exact single selected (List.mem_cons_of_mem bond retained)
      simp only [List.foldl_cons]
      rw [ih tailSingle]
      cases source : bond.source == center <;> cases target : bond.target == center <;>
        simp_all [recordNeighbor?, ParsedBondKind.order, Nat.add_assoc, Nat.add_comm]

theorem all_single_incident_sum (raw : RawMolecule)
    (single : ∀ bond ∈ raw.bonds, bond.kind = .single) (center : ℕ) :
    raw.incidentBondOrderSum center = (recordNeighbors raw center).length := by
  simpa only [Nat.zero_add] using all_single_incident_fold raw.bonds center single 0

end TetraStereo.UniversalProof.ChronologicalFamilyPhysicalBridge
