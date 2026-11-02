import TetraStereo.UniversalProof.NextFrontier.NativeNitrileHydrogenAtoms
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileWrittenNeighbors
import TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

theorem center_hydrogen_base (parity : TetrahedralInputParity) (n : Nat) :
    hydrogenExpansionBase (raw parity n) 0 = n + 7 := by
  simp [hydrogenExpansionBase, raw_atomCount]

theorem amino_hydrogen_base (parity : TetrahedralInputParity) (n : Nat) :
    hydrogenExpansionBase (raw parity n) 4 = n + 8 := by
  change (raw parity n).atomCount +
    ([0, 1, 2, 3].map (raw parity n).hydrogenCountAt).sum = n + 8
  rw [raw_atomCount]
  simp [hydrogenCountAt, raw_center, raw_fluorine, raw_nitrile_carbon,
    raw_nitrile_nitrogen, centerSpec, bracket, Nat.add_assoc]

theorem center_hydrogen_ids (parity : TetrahedralInputParity) (n : Nat) :
    materializedHydrogenIds (raw parity n) 0 = [n + 7] := by
  simp [materializedHydrogenIds, center_hydrogen_base, raw_center_hydrogen]

theorem amino_hydrogen_ids (parity : TetrahedralInputParity) (n : Nat) :
    materializedHydrogenIds (raw parity n) 4 = [n + 8] := by
  have demand : (raw parity n).hydrogenCountAt 4 = 1 := rfl
  simp [materializedHydrogenIds, amino_hydrogen_base, demand]

theorem nitrile_hydrogen_ids (parity : TetrahedralInputParity) (n : Nat) :
    materializedHydrogenIds (raw parity n) 2 = [] := by
  simp [materializedHydrogenIds, (raw_nitrile_hydrogens parity n).1]

theorem expanded_center_row (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).writtenNeighbors 0 = [n + 7, 1, 2, 4] := by
  rw [expanded, withExplicitHydrogens_writtenNeighbors _ (raw_wellFormed parity n)
    (raw_written_exact parity n) 0 (by rw [raw_atomCount]; omega)]
  rw [materializedWrittenRow, center_hydrogen_ids]
  rfl

theorem expanded_nitrile_row (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).writtenNeighbors 2 = [0, 3] := by
  rw [expanded, withExplicitHydrogens_writtenNeighbors _ (raw_wellFormed parity n)
    (raw_written_exact parity n) 2 (by rw [raw_atomCount]; omega)]
  rw [materializedWrittenRow, nitrile_hydrogen_ids]
  rfl

theorem expanded_amino_row (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).writtenNeighbors 4 = [0, n + 8, 5, 6] := by
  rw [expanded, withExplicitHydrogens_writtenNeighbors _ (raw_wellFormed parity n)
    (raw_written_exact parity n) 4 (by rw [raw_atomCount]; omega)]
  rw [materializedWrittenRow, amino_hydrogen_ids]
  rfl

theorem actual_center_hydrogen_bond (parity : TetrahedralInputParity) (n : Nat) :
    ({ source := 0, target := n + 7, kind := .single } : RawBond) ∈
      (expanded parity n).bonds := by
  have present := withExplicitHydrogens_createdBond_mem (raw parity n) 0 0
    (by rw [raw_atomCount]; omega) (by rw [raw_center_hydrogen]; decide)
  simpa only [center_hydrogen_base, Nat.add_zero] using present

theorem actual_amino_hydrogen_bond (parity : TetrahedralInputParity) (n : Nat) :
    ({ source := 4, target := n + 8, kind := .single } : RawBond) ∈
      (expanded parity n).bonds := by
  have present := withExplicitHydrogens_createdBond_mem (raw parity n) 4 0
    (by rw [raw_atomCount]; omega) (by change 0 < 1; decide)
  simpa only [amino_hydrogen_base, Nat.add_zero] using present

theorem actual_center_hydrogen_atom (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).atomAt? (n + 7) = some (AtomSpec.aliphatic .H) := by
  obtain ⟨spec, lookup⟩ := listGet?_exists_of_lt (expanded parity n).atoms (n + 7)
    (by change n + 7 < (expanded parity n).atomCount; rw [expanded_atomCount]; omega)
  have same := (expanded_fresh_hydrogen parity n (n + 7) spec (by omega) lookup).1
  simpa only [same] using lookup

theorem actual_amino_hydrogen_atom (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).atomAt? (n + 8) = some (AtomSpec.aliphatic .H) := by
  obtain ⟨spec, lookup⟩ := listGet?_exists_of_lt (expanded parity n).atoms (n + 8)
    (by change n + 8 < (expanded parity n).atomCount; rw [expanded_atomCount]; omega)
  have same := (expanded_fresh_hydrogen parity n (n + 8) spec (by omega) lookup).1
  simpa only [same] using lookup

/-- Generated H atoms cannot attach to a zero-demand original atom. This retains exact original
incident bond records, even though unrelated atoms in the molecule have positive demand. -/
theorem expanded_zero_demand_incident (parity : TetrahedralInputParity) (n index : Nat)
    (bound : index < n + 7) (zero : (raw parity n).hydrogenCountAt index = 0)
    (bond : RawBond) (incident : bond.source = index ∨ bond.target = index) :
    bond ∈ (expanded parity n).bonds ↔ bond ∈ (raw parity n).bonds := by
  rw [expanded, withExplicitHydrogens_bonds_mem_iff]
  constructor
  · rintro (original | ⟨parent, _, hydrogen, generated, equal⟩)
    · exact original
    · subst bond
      rcases incident with sameParent | sameHydrogen
      · change parent = index at sameParent
        subst parent
        simp [materializedHydrogenIds, zero] at generated
      · rcases List.mem_map.mp generated with ⟨offset, _, same⟩
        have lower := hydrogenExpansionBase_original_count_le (raw parity n) parent
        rw [raw_atomCount] at lower
        simp only at sameHydrogen
        omega
  · exact Or.inl

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
