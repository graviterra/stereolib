import TetraStereo.UniversalProof.NextFrontier.NativeNitrileCycleExclusion
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileAtomicLabels

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.TerminalStarCycleGuard

private theorem record_count_le_contribution (bonds : List RawBond) (center : Nat) :
    (bonds.filterMap (recordNeighbor? center)).length ≤
      (bonds.map (incidentContributionAt center)).sum := by
  induction bonds with
  | nil => simp
  | cons bond tail ih =>
      cases kind : bond.kind <;>
        cases source : bond.source == center <;> cases target : bond.target == center <;>
        simp_all [recordNeighbor?, incidentContributionAt, ParsedBondKind.order] <;> omega

private theorem incident_degree_le_order_sum (mol : RawMolecule) (center : Nat)
    (distinct : (recordNeighbors mol center).Nodup) :
    (mol.incidentAtoms center).length ≤ mol.incidentBondOrderSum center := by
  rw [incidentAtoms_eq_recordNeighbors_eraseDups, eraseDups_eq_self_of_nodup _ distinct,
    incidentBondOrderSum_eq_incidentContributionAt_sum]
  exact record_count_le_contribution mol.bonds center

private theorem leaf_acyclic (molecule : RawMolecule) (atom fuel : Nat)
    (degree : (molecule.incidentAtoms atom).length ≤ 1) :
    molecule.atomLiesInCycle fuel atom = false := by
  cases observed : molecule.incidentAtoms atom with
  | nil => simp [atomLiesInCycle, observed, ringPairCount]
  | cons head tail =>
      cases tail with
      | nil => simp [atomLiesInCycle, observed, ringPairCount]
      | cons second rest =>
          simp only [observed, List.length_cons] at degree
          omega

theorem expanded_fluorine_written_row (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).writtenNeighbors 1 = [0] := by
  have ids : materializedHydrogenIds (raw parity n) 1 = [] := by
    simp [materializedHydrogenIds, hydrogenCountAt, raw_fluorine,
      bracket]
  rw [expanded, withExplicitHydrogens_writtenNeighbors _ (raw_wellFormed parity n)
    (raw_written_exact parity n) 1 (by rw [raw_atomCount]; omega)]
  rw [materializedWrittenRow, ids]
  rfl

theorem expanded_fluorine_acyclic (parity : TetrahedralInputParity) (n fuel : Nat) :
    (expanded parity n).atomLiesInCycle fuel 1 = false := by
  apply leaf_acyclic
  rw [incidentAtoms_eq_recordNeighbors_eraseDups,
    eraseDups_eq_self_of_nodup _ (expanded_records_nodup parity n 1)]
  have count := (expanded_record_row parity n 1 (by omega)).length_eq
  rw [expanded_fluorine_written_row] at count
  simpa only [List.length_cons, List.length_nil] using count.le

theorem expanded_center_hydrogen_acyclic (parity : TetrahedralInputParity) (n fuel : Nat) :
    (expanded parity n).atomLiesInCycle fuel (n + 7) = false := by
  apply leaf_acyclic
  have incident := (expanded_fresh_hydrogen parity n (n + 7) (AtomSpec.aliphatic .H)
    (Nat.le_refl _) (actual_center_hydrogen_atom parity n)).2
  exact incident ▸ incident_degree_le_order_sum (expanded parity n) (n + 7)
    (expanded_records_nodup parity n (n + 7))

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
