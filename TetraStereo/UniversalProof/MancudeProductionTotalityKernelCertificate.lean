import TetraStereo.OneCenter.ProductionCIPRule1aGeneralSoundness
import TetraStereo.KernelOnly

/-! The production matching search returns a label under an explicit written-maximum
matching hypothesis. These checks do not assert that all chemical inputs satisfy it. -/

assert_kernel_only TetraStereo.OneCenter.RawMolecule.exhaustiveMancudeMatchingStats_supported_of_maximum
assert_kernel_only TetraStereo.OneCenter.RawMolecule.generalMancudeRule1aLabel?_exists_of_localized_maximum
assert_kernel_only TetraStereo.OneCenter.RawMolecule.mancudeRule1aLabel?_exists_of_localized_maximum
