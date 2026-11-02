import TetraStereo.Examples.CarbohydrateImage362FixtureSelectorCertificateSupport

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
namespace SucroseDescriptorCertificate

open OneCenter

/-- Erasing the production selector's certificate recovers exactly its value-only branch. -/
theorem certifiedConstructiveRawDescriptorSource_val_eq_value
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (sourceFuel : Nat)
    (initial : RawDescriptorState) :
    (certifiedConstructiveRawDescriptorSource result mol sourceFuel initial).val =
      constructiveRawDescriptorSourceValue result mol sourceFuel initial :=
  DescriptorCertificateSupport.certifiedConstructiveRawDescriptorSource_val_eq_value
    result mol sourceFuel initial

end SucroseDescriptorCertificate
end TetraStereo.Examples.CarbohydrateImage362ExternalFixtures.Internal
