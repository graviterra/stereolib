import TetraStereo.UniversalProof.NextFrontier.NativeNitrileRuntimeSecondSphere
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileCycleExclusion

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

/-- The actual physical acyclicity proof disables the legacy conflict guard in both directions. -/
theorem actual_nitrile_amino_guards (parity : TetrahedralInputParity) (n fuel : Nat)
    (ordering : Ordering) :
    occurrenceRootsProvedAutomorphic (expanded parity n) fuel
        nitrileCursor aminoCursor ordering = false ∧
      occurrenceRootsProvedAutomorphic (expanded parity n) fuel
        aminoCursor nitrileCursor ordering = false := by
  have absent := expanded_nitrile_acyclic parity n fuel
  cases ordering <;>
    simp [occurrenceRootsProvedAutomorphic, nitrileCursor, canonicalRoot, absent]

/-- Both full production occurrence comparators retain the independently derived strict
constitution decision for every auxiliary state. No assigned descriptor is a premise. -/
theorem actual_nitrile_amino_occurrence_comparison (parity : TetrahedralInputParity)
    (n fuel : Nat) (state : OccurrenceAuxState) :
    compareOccurrenceBranches? (expanded parity n) state (fuel + 2) nitrileCursor aminoCursor =
        some { ordering := .gt } ∧
      compareOccurrenceBranchesAuthoritative? (expanded parity n) state (fuel + 2)
        nitrileCursor aminoCursor = some { ordering := .gt } ∧
      compareOccurrenceBranches? (expanded parity n) state (fuel + 2) aminoCursor nitrileCursor =
        some { ordering := .lt } ∧
      compareOccurrenceBranchesAuthoritative? (expanded parity n) state (fuel + 2)
        aminoCursor nitrileCursor = some { ordering := .lt } := by
  have comparisons := actual_nitrile_amino_comparison parity n fuel .rule2
  have forward := (actual_nitrile_amino_guards parity n (fuel + 2) .gt).1
  have reverse := (actual_nitrile_amino_guards parity n (fuel + 2) .lt).2
  simp [compareOccurrenceBranches?, compareOccurrenceBranchesAuthoritative?,
    certifiedConstitutionalStage?, certifiedConstitutionalStageAuthoritative?,
    comparisons.1, comparisons.2.1, comparisons.2.2.1, comparisons.2.2.2,
    forward, reverse]

theorem actual_nitrile_amino_complete_comparison (parity : TetrahedralInputParity)
    (n fuel : Nat) (state : OccurrenceAuxState) :
    compareOccurrenceBranchesComplete? (expanded parity n) state (fuel + 2)
        nitrileCursor aminoCursor = some { ordering := .gt } ∧
      compareOccurrenceBranchesComplete? (expanded parity n) state (fuel + 2)
        aminoCursor nitrileCursor = some { ordering := .lt } := by
  have actual := actual_nitrile_amino_occurrence_comparison parity n fuel state
  simp [compareOccurrenceBranchesComplete?, actual.1, actual.2.2.1]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
