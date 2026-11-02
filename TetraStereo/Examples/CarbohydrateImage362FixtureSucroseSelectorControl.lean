import TetraStereo.Examples.CarbohydrateImage362FixtureSucroseSelectorValue

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

open OneCenter

/-- A constructive source whose stabilization and auxiliary stages are all no-ops is selected
unchanged.  Keeping this reduction molecule-generic prevents concrete chemistry terms from being
duplicated throughout the selector's provenance proof. -/
theorem certifiedConstructiveRawDescriptorSource_val_eq_of_noop
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (sourceFuel : Nat)
    (state : RawDescriptorState)
    (accepted :
      stabilizedRawDescriptorState? result mol 100 sourceFuel
          (result.parsed.atomCount + 1) state = some state)
    (auxiliaryNoop :
      solveAuxiliaryDescriptorDependencies result mol 100 sourceFuel state = state)
    (finishNoop : finishRawDescriptorSource result mol sourceFuel state = state) :
    (certifiedConstructiveRawDescriptorSource result mol sourceFuel state).val = state :=
  DescriptorCertificateSupport.certifiedConstructiveRawDescriptorSource_val_eq_of_noop
    result mol sourceFuel state accepted auxiliaryNoop finishNoop

/-- A known nonempty initial state selects the constructive production branch.  Keeping the
initial-state equality abstract prevents concrete chemistry reduction from traversing the
dependent provenance payload of `certifiedRawDescriptorSource`. -/
theorem certifiedRawDescriptorSource_val_eq_constructive_of_initial_eq
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (sourceFuel : Nat)
    (state : RawDescriptorState)
    (initialEq : initialRawDescriptorState result mol sourceFuel = state)
    (nonempty : state.isEmpty = false) :
    (certifiedRawDescriptorSource result mol sourceFuel).val =
      (certifiedConstructiveRawDescriptorSource result mol sourceFuel state).val :=
  DescriptorCertificateSupport.certifiedRawDescriptorSource_val_eq_constructive_of_initial_eq
    result mol sourceFuel state initialEq nonempty

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
