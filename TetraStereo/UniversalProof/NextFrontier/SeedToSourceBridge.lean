import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SeedToSourceBridge
open TetraStereo.OneCenter

/-- A changed initial seed may reach a stable state before the auxiliary and finishing stages.
This generalizes the no-op selector lemma without reducing the dependent provenance payload. -/
theorem constructive_source_of_transition
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : Nat)
    (seed stable : RawDescriptorState)
    (initialAccepted : stabilizedRawDescriptorState? result mol 100 fuel
      (result.parsed.atomCount + 1) seed = some stable)
    (stableAccepted : stabilizedRawDescriptorState? result mol 100 fuel
      (result.parsed.atomCount + 1) stable = some stable)
    (auxiliaryNoop : solveAuxiliaryDescriptorDependencies result mol 100 fuel stable = stable)
    (finishNoop : finishRawDescriptorSource result mol fuel stable = stable) :
    (certifiedConstructiveRawDescriptorSource result mol fuel seed).val = stable := by
  change constructiveRawDescriptorSourceValue result mol fuel seed = stable
  unfold constructiveRawDescriptorSourceValue
  rw [initialAccepted]
  dsimp only
  rw [auxiliaryNoop, stableAccepted]
  dsimp only
  rw [auxiliaryNoop]
  unfold retainLastStableRawDescriptorState
  simp only [beq_self_eq_true, if_true]
  exact finishNoop

/-- Actual production selection from an independently established nonempty seed. All computational
premises name actual stages; no final source equality is assumed. Family instantiation is separate. -/
theorem source_of_nonempty_seed_transition
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : Nat)
    (seed stable : RawDescriptorState)
    (initialEq : initialRawDescriptorState result mol fuel = seed)
    (nonempty : seed.isEmpty = false)
    (initialAccepted : stabilizedRawDescriptorState? result mol 100 fuel
      (result.parsed.atomCount + 1) seed = some stable)
    (stableAccepted : stabilizedRawDescriptorState? result mol 100 fuel
      (result.parsed.atomCount + 1) stable = some stable)
    (auxiliaryNoop : solveAuxiliaryDescriptorDependencies result mol 100 fuel stable = stable)
    (finishNoop : finishRawDescriptorSource result mol fuel stable = stable) :
    discoverRawDescriptorSource result mol fuel = stable := by
  have chosen : (certifiedRawDescriptorSource result mol fuel).val =
      (certifiedConstructiveRawDescriptorSource result mol fuel seed).val := by
    subst seed
    unfold certifiedRawDescriptorSource
    simp only [nonempty, Bool.false_eq_true, if_false]
  unfold discoverRawDescriptorSource
  rw [chosen]
  exact constructive_source_of_transition result mol fuel seed stable initialAccepted
    stableAccepted auxiliaryNoop finishNoop

end TetraStereo.UniversalProof.SeedToSourceBridge
