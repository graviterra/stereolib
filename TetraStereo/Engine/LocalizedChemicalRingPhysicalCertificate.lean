import TetraStereo.Engine.LocalizedChemicalRingPublic
import TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Checked physical admission for the explicit public ring profile. The coordinate check
constructs the calibration needed by the physical/source theorem. It does not decide physical
distinguishability, select a chemical reference policy, or identify rejection with refusal. -/
namespace TetraStereo.Engine.LocalizedChemicalRing

open OneCenter
open LocalizedChemicalRingPhysicalAdmission

/-- Executable coordinate-domain check for an already structurally admitted public input. -/
def coordinatesAdmitted (input : Input) : Bool :=
  allCentersAdmitted input.certified

/-- A successful coordinate check supplies the configuration and all-center calibration;
the physical clause of `SourceMeaning` retains its explicit distinguishability hypothesis. -/
theorem existsUnique_sourceMeaning_of_coordinates (profile : Profile) (input : Input)
    (accepted : coordinatesAdmitted input = true) :
    ∃! candidate, SourceMeaning profile input (detectedCoordinateCfg input.certified) candidate :=
  existsUnique_sourceMeaning profile input (detectedCoordinateCfg input.certified)
    (detected_all_calibrated input.certified accepted)

end TetraStereo.Engine.LocalizedChemicalRing

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.coordinatesAdmitted
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.existsUnique_sourceMeaning_of_coordinates
