import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual marked keys separate the two root arms in the explicit reference-30
generated snapshot. The finite graph symmetry proof and the actual generated-label
orientation decoder meet here. This is not a complete descriptor or molecular report. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSeparationCertificate

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation LocalizedChemicalRingReferenceOrbitCoveringSymmetry
open LocalizedChemicalRingInheritedRefusalCases

/-- No supplied key tie, auxiliary label, physical sign, or whole-state execution:
both successful observation and every possible exchange's negative sign are derived. -/
theorem root_keys_separate :
    markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
        rootSnapshot reference leftSlot ≠
      markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
        rootSnapshot reference rightSlot :=
  root_keys_ne_of_exchange_sign (reference_exchange_current_negative cfg)

end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSeparationCertificate

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSeparationCertificate.root_keys_separate
