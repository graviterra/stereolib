import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator

set_option autoImplicit false

namespace TetraStereo.OneCenter.RawMolecule

/-!
# Mancude matching-cap retirement

The ordinary and authoritative Rule-1a labelers now perform the same exhaustive finite
maximum-matching computation.  These pointwise equalities prevent a size cutoff from being hidden
behind either the general component labeler or its public node-label dispatchers.
-/

theorem generalMancudeRule1aLabel?_eq_authoritative
    (mol : RawMolecule) (attached duplicated : Nat) :
    mol.generalMancudeRule1aLabel? attached duplicated =
      mol.generalMancudeRule1aLabelAuthoritative? attached duplicated :=
  rfl

theorem mancudeRule1aLabel?_eq_authoritative
    (mol : RawMolecule) (attached duplicated : Nat) :
    mol.mancudeRule1aLabel? attached duplicated =
      mol.mancudeRule1aLabelAuthoritative? attached duplicated :=
  rfl

theorem canonicalRule1aLabel?_eq_authoritative
    (mol : RawMolecule) (node : CanonicalBranchNode) :
    mol.canonicalRule1aLabel? node = mol.canonicalRule1aLabelAuthoritative? node :=
  rfl

end TetraStereo.OneCenter.RawMolecule
