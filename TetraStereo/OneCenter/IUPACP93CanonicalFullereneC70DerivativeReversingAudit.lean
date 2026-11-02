import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC70DerivativeParentAutomorphism

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

theorem iupacP93CanonicalFullereneC70Type4ReversingSymmetry_reversing :
    MolecularFullereneFaceOrientationReversing
      iupacP93CanonicalFullereneC70DerivativeInput
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry := by
  apply (molecularFullereneFaceOrientationReversingChecked_eq_true_iff
    iupacP93CanonicalFullereneC70DerivativeInput
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry).mp
  decide

theorem iupacP93CanonicalFullereneC70Type4ReversingSymmetry_derivativeAutomorphism :
    MolecularFullereneCarrierAutomorphism
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70DerivativeInput
      iupacP93CanonicalFullereneC70Type4ReversingSymmetry := by
  exact (iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.cageAgreement
    iupacP93CanonicalFullereneC70SharedNumberedCage.certificate
      |>.carrierAutomorphism_iff
        iupacP93CanonicalFullereneC70Type4ReversingSymmetry).mp
    iupacP93CanonicalFullereneC70Type4ReversingSymmetry_parentAutomorphism

theorem iupacP93CanonicalFullereneC70Type4ReversingSymmetry_fixedSites :
    mapMolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70DerivativeInput
        iupacP93CanonicalFullereneC70Type4ReversingSymmetry 7 = 7 ∧
      mapMolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70DerivativeInput
        iupacP93CanonicalFullereneC70Type4ReversingSymmetry 24 = 24 ∧
      mapMolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70DerivativeInput
        iupacP93CanonicalFullereneC70Type4ReversingSymmetry 15 = 15 ∧
      mapMolecularFullereneCarrierAtom iupacP93CanonicalFullereneC70DerivativeInput
        iupacP93CanonicalFullereneC70Type4ReversingSymmetry 34 = 34 := by
  decide

end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
