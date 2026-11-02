import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.ExplicitHydrogenValencePreservationKernelCertificate

open RawMolecule

/-!
# Kernel-only certificate: explicit-hydrogen valence preservation

The concrete bracket-carbon case catches double counting: the source carbon has three represented
single bonds and one inline bracket hydrogen.  Once that hydrogen is materialized as a real atom
and bond, the inline count must no longer contribute a second unit of valence.
-/

private def bracketCHBrClF : RawMolecule where
  atoms :=
    [ { AtomSpec.aliphatic Element.C with
          explicitHydrogens? := some 1
          tetrahedral? := some .clockwise },
      AtomSpec.aliphatic Element.Br,
      AtomSpec.aliphatic Element.Cl,
      AtomSpec.aliphatic Element.F ]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single } ]
  neighborOrder := [[1, 2, 3], [0], [0], [0]]

example : bracketCHBrClF.valenceOK? = true := by decide

example : bracketCHBrClF.withExplicitHydrogens.valenceOK? = true := by decide

end TetraStereo.OneCenter.ExplicitHydrogenValencePreservationKernelCertificate

assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_preserves_valenceOK
