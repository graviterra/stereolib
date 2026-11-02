import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeGraphFacts
import TetraStereo.UniversalProof.ReviewedPositiveHydrogenAtomTransportClosureProofs.ReviewedPositiveHydrogenAtomTransportClosure

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingRuntimeAtoms

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.ReviewedPositiveHydrogenAtomTransportClosureProofs.ReviewedPositiveHydrogenAtomTransportClosure

/-- A demanded hydrogen has exactly its demanding atom as physical record neighbor. The proof
uses the materialized block partition, so it also applies to cyclic parents. -/
theorem materialized_hydrogen_records (raw : RawMolecule)
    (admitted : raw.StereochemicalAdmissible) (parent offset : Nat)
    (parentBound : parent < raw.atomCount) (offsetBound : offset < raw.hydrogenCountAt parent) :
    recordNeighbors raw.withExplicitHydrogens (hydrogenExpansionBase raw parent + offset) =
      [parent] := by
  let hydrogen := hydrogenExpansionBase raw parent + offset
  have lower : raw.atomCount ≤ hydrogen := materializedHydrogenId_lower raw parent offset
  have block : hydrogen ∈ materializedHydrogenIds raw parent :=
    List.mem_map.mpr ⟨offset, List.mem_range.mpr offsetBound, rfl⟩
  have output := withExplicitHydrogens_preserves_stereochemicalAdmissible raw admitted
  apply List.Perm.eq_singleton
  apply List.perm_of_nodup_nodup_toFinset_eq
    (recordNeighbors_nodup _ output.1.2 hydrogen) (by simp)
  apply Finset.ext
  intro neighbor
  simp only [List.mem_toFinset, List.mem_singleton]
  constructor
  · intro member
    obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
    have endpoints := recordNeighbor_endpoints hydrogen neighbor bond observed
    rcases (withExplicitHydrogens_bonds_mem_iff raw bond).mp retained with
      original | ⟨owner, ownerBound, target, targetBlock, equal⟩
    · obtain ⟨sourceBound, targetBound, _⟩ := admitted.1.1 bond original
      rcases endpoints with ⟨source, _⟩ | ⟨target, _⟩ <;> omega
    · subst bond
      rcases endpoints with ⟨source, _⟩ | ⟨targetEqual, ownerEqual⟩
      · change owner = hydrogen at source
        omega
      · change target = hydrogen at targetEqual
        change owner = neighbor at ownerEqual
        subst target
        exact ownerEqual.symm.trans (materializedHydrogenId_parent_unique raw hydrogen owner parent
          targetBlock block)
  · intro equal
    subst neighbor
    apply List.mem_filterMap.mpr
    refine ⟨{ source := parent, target := hydrogen, kind := .single },
      withExplicitHydrogens_createdBond_mem raw parent offset parentBound offsetBound, ?_⟩
    have different : parent ≠ hydrogen := by omega
    simp [recordNeighbor?, different]

theorem expanded_fresh_hydrogen (n : Nat) (parity : TetrahedralInputParity) (atom : Nat)
    (lower : n + 5 ≤ atom) (upper : atom < 3 * n + 9) :
    (expanded n parity).atomAt? atom = some (AtomSpec.aliphatic .H) := by
  obtain ⟨spec, observed⟩ := listGet?_exists_of_lt (expanded n parity).atoms atom
    (by change atom < (expanded n parity).atomCount; rwa [expanded_atom_count])
  have identity := (expanded_fresh_atom n parity atom spec lower observed).1
  simpa only [identity] using observed

theorem expanded_atom_z_original (n : Nat) (parity : TetrahedralInputParity)
    (atom : Nat) (spec : AtomSpec) (observed : (ringRaw n parity).atomAt? atom = some spec) :
    (expanded n parity).atomZAt atom = spec.element.atomicNumber := by
  unfold atomZAt
  rw [expanded_original_atom n parity atom spec observed]
  rfl

theorem expanded_root_z (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).atomZAt 0 = 6 :=
  expanded_atom_z_original n parity 0 _ (ringRaw_atomAt_zero n parity)

theorem expanded_fluorine_z (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).atomZAt 1 = 9 :=
  expanded_atom_z_original n parity 1 _ (ringRaw_atomAt_one n parity)

theorem expanded_left_z (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).atomZAt 2 = 6 :=
  expanded_atom_z_original n parity 2 _ (ringRaw_atomAt_two n parity)

theorem expanded_chlorine_z (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).atomZAt 3 = 17 :=
  expanded_atom_z_original n parity 3 _ (ringRaw_atomAt_three n parity)

theorem expanded_chain_z (n : Nat) (parity : TetrahedralInputParity) (k : Nat) (bound : k ≤ n) :
    (expanded n parity).atomZAt (k + 4) = 6 :=
  expanded_atom_z_original n parity (k + 4) _ (ringRaw_atomAt_chain n parity k bound)

theorem expanded_right_predecessor_z (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).atomZAt (if n = 0 then 2 else n + 3) = 6 := by
  cases n with
  | zero => exact expanded_left_z 0 parity
  | succ n =>
      simpa [Nat.add_assoc] using
        expanded_chain_z (n + 1) parity n (by omega)

theorem expanded_hydrogen_z (n : Nat) (parity : TetrahedralInputParity) (atom : Nat)
    (lower : n + 5 ≤ atom) (upper : atom < 3 * n + 9) :
    (expanded n parity).atomZAt atom = 1 := by
  unfold atomZAt
  rw [expanded_fresh_hydrogen n parity atom lower upper]
  rfl

theorem expanded_chain_hydrogen_records (n : Nat) (parity : TetrahedralInputParity)
    (k offset : Nat) (bound : k ≤ n) (offsetBound : offset < 2) :
    recordNeighbors (expanded n parity) (n + 7 + 2 * k + offset) = [k + 4] := by
  have result := materialized_hydrogen_records (ringRaw n parity)
    ⟨ringRaw_admissible n parity, ringRaw_writtenNeighborExact n parity⟩ (k + 4) offset
    (by rw [atom_count]; omega)
    (by rwa [raw_chain_hydrogen_count n parity k bound])
  rwa [chain_hydrogen_base n parity k bound] at result

theorem expanded_right_hydrogen_records (n : Nat) (parity : TetrahedralInputParity) :
    recordNeighbors (expanded n parity) (3 * n + 7) = [n + 4] ∧
      recordNeighbors (expanded n parity) (3 * n + 8) = [n + 4] := by
  constructor
  · rw [show 3 * n + 7 = n + 7 + 2 * n + 0 by omega]
    exact expanded_chain_hydrogen_records n parity n 0 (by omega) (by decide)
  · rw [show 3 * n + 8 = n + 7 + 2 * n + 1 by omega]
    exact expanded_chain_hydrogen_records n parity n 1 (by omega) (by decide)

end TetraStereo.UniversalProof.NativeRingRuntimeAtoms
