import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFinishGuardLeaves
import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFinishCandidateLeaves

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Production completion for the finite eight-member parsed parity family. The actual initial
seed, full-state scheduler transition, auxiliary guard, simultaneous candidates and carrier
normalization are independently discharged stages. No final discovery/model equation is a premise.
This does not close source/chemical-input scheduled-model semantics or external source approval. -/
namespace TetraStereo.UniversalProof.FramedParsedParityFinishCompletion

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParitySeed
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
open TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves
open TetraStereo.UniversalProof.FramedParsedParityFinish
open TetraStereo.UniversalProof.FramedParsedParityFinishEqualSupport
open TetraStereo.UniversalProof.FramedParsedParityFinishGuardLeaves
open TetraStereo.UniversalProof.FramedParsedParityFinishCandidateLeaves

theorem equal_auxiliary_noop (center arm : TetrahedralInputParity) :
    solveAuxiliaryDescriptorDependencies (actualResult center arm arm) (actualMol center arm arm)
      100 (actualFuel center arm arm) (stateD center arm arm) = stateD center arm arm := by
  exact equal_auxiliary_from_guard center arm (equal_refusal_guard center arm)

/-- All four temporary senses/cases are tested by the actual streaming algorithm. -/
theorem equal_summary_none (center arm : TetrahedralInputParity) :
    exactAuxiliaryDescriptorSolutionSummary (actualResult center arm arm)
      (actualMol center arm arm) 100 (actualFuel center arm arm) (stateD center arm arm) [1] =
        .none := by
  exact exact_summary_none_singleton (actualResult center arm arm) (actualMol center arm arm)
    100 (actualFuel center arm arm) 1 (stateD center arm arm)
    (equal_candidate_none center arm RS.R true) (equal_candidate_none center arm RS.S true)
    (equal_candidate_none center arm RS.R false) (equal_candidate_none center arm RS.S false)

theorem equal_exact_auxiliary_noop (center arm : TetrahedralInputParity) :
    solveExactAuxiliaryDescriptorDependencies (actualResult center arm arm)
      (actualMol center arm arm) 100 (actualFuel center arm arm) (stateD center arm arm) =
        stateD center arm arm := by
  exact exact_auxiliary_noop_singleton (actualResult center arm arm) (actualMol center arm arm)
    100 (actualFuel center arm arm) 1 (stateD center arm arm)
    ((unresolved_centers center arm arm).trans (if_pos rfl))
    (equal_summary_none center arm)

theorem equal_finish_noop (center arm : TetrahedralInputParity) :
    finishRawDescriptorSource (actualResult center arm arm) (actualMol center arm arm)
      (actualFuel center arm arm) (stateD center arm arm) = stateD center arm arm := by
  exact finish_noop_of_exact_noop (actualResult center arm arm) (actualMol center arm arm)
    (actualFuel center arm arm) (stateD center arm arm) (equal_exact_auxiliary_noop center arm)

theorem auxiliary_noop (center left right : TetrahedralInputParity) :
    solveAuxiliaryDescriptorDependencies (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right)
      (stateD center left right) = stateD center left right := by
  by_cases same : left = right
  · subst right
    exact equal_auxiliary_noop center left
  · exact opposite_auxiliary_noop center left right same

theorem finish_noop (center left right : TetrahedralInputParity) :
    finishRawDescriptorSource (actualResult center left right) (actualMol center left right)
      (actualFuel center left right) (stateD center left right) = stateD center left right := by
  by_cases same : left = right
  · subst right
    exact equal_finish_noop center left
  · exact opposite_finish_noop center left right same

/-- The actual production selector after its accepted nonempty initial seed transition. -/
theorem actual_source (center left right : TetrahedralInputParity) :
    discoverRawDescriptorSource (actualResult center left right) (actualMol center left right)
      (actualFuel center left right) = stateD center left right := by
  exact SeedToSourceBridge.source_of_nonempty_seed_transition
    (actualResult center left right) (actualMol center left right) (actualFuel center left right)
    (expectedSeed left right) (stateD center left right) (actual_initial center left right)
    rfl (stabilized_from_seed center left right) (stabilized_from_stateD center left right)
    (auxiliary_noop center left right) (finish_noop center left right)

/-- Full-state actual discovery for every parsed family member, with actual carrier normalization. -/
theorem actual_descriptors (center left right : TetrahedralInputParity) :
    discoverRawDescriptors (actualResult center left right) (actualMol center left right)
      (actualFuel center left right) = stateD center left right := by
  unfold discoverRawDescriptors
  rw [actual_source center left right]
  exact normalize_stateD center left right

end TetraStereo.UniversalProof.FramedParsedParityFinishCompletion
