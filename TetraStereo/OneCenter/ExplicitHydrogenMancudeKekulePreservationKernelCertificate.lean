import TetraStereo.OneCenter.ExplicitHydrogenMancudeKekulePreservation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Kernel-only certificate for localized Mancude/Kekulé preservation

The production hydrogen materializer must preserve the independent maximum-written-matching
condition consumed by complete Rule-1a discovery.
-/

assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_preserves_localizedMancudeKekuleAdmissible
