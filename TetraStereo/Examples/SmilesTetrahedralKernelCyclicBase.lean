import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.Examples.SmilesTetrahedralKernelProof

open TetraStereo.OneCenter

def cyclicAutomorphismParsed : RawMolecule :=
  match parseOpenSMILES "OC=1C=CC=CC1[C@H](C2=CC=CC=C2O)O" with
  | .ok mol => mol
  | .error _ => { atoms := [], bonds := [] }

def cyclicAutomorphismExpanded : RawMolecule :=
  cyclicAutomorphismParsed.normalizeUnspecifiedBonds.withExplicitHydrogens

theorem cyclicAutomorphism_parse :
    parseOpenSMILES "OC=1C=CC=CC1[C@H](C2=CC=CC=C2O)O" =
      .ok cyclicAutomorphismParsed := by
  rfl

end TetraStereo.Examples.SmilesTetrahedralKernelProof
