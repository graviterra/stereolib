import TetraStereo.Examples.CarbohydrateImage362FixtureCore

set_option autoImplicit false

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace DescriptorCertificateSupport

open OneCenter

/-- Erasing the production selector's certificate recovers exactly its value-only branch. -/
theorem certifiedConstructiveRawDescriptorSource_val_eq_value
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (sourceFuel : Nat)
    (initial : RawDescriptorState) :
    (certifiedConstructiveRawDescriptorSource result mol sourceFuel initial).val =
      constructiveRawDescriptorSourceValue result mol sourceFuel initial := by
  rfl

/-- A constructive source whose stabilization and auxiliary stages are all no-ops is selected
unchanged. The theorem is molecule-generic so concrete chemistry terms stay out of the selector's
dependent provenance proof. -/
theorem certifiedConstructiveRawDescriptorSource_val_eq_of_noop
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (sourceFuel : Nat)
    (state : RawDescriptorState)
    (accepted :
      stabilizedRawDescriptorState? result mol 100 sourceFuel
          (result.parsed.atomCount + 1) state = some state)
    (auxiliaryNoop :
      solveAuxiliaryDescriptorDependencies result mol 100 sourceFuel state = state)
    (finishNoop : finishRawDescriptorSource result mol sourceFuel state = state) :
    (certifiedConstructiveRawDescriptorSource result mol sourceFuel state).val = state := by
  rw [certifiedConstructiveRawDescriptorSource_val_eq_value]
  unfold constructiveRawDescriptorSourceValue
  rw [accepted]
  dsimp only
  rw [auxiliaryNoop, accepted]
  dsimp only
  rw [auxiliaryNoop]
  unfold retainLastStableRawDescriptorState
  simp only [beq_self_eq_true, if_true]
  exact finishNoop

/-- A known nonempty initial state selects the constructive production branch. Keeping the
initial-state equality abstract prevents concrete chemistry reduction from traversing the
dependent provenance payload of `certifiedRawDescriptorSource`. -/
theorem certifiedRawDescriptorSource_val_eq_constructive_of_initial_eq
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (sourceFuel : Nat)
    (state : RawDescriptorState)
    (initialEq : initialRawDescriptorState result mol sourceFuel = state)
    (nonempty : state.isEmpty = false) :
    (certifiedRawDescriptorSource result mol sourceFuel).val =
      (certifiedConstructiveRawDescriptorSource result mol sourceFuel state).val := by
  subst state
  unfold certifiedRawDescriptorSource
  simp only [nonempty, Bool.false_eq_true, if_false]

end DescriptorCertificateSupport
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
