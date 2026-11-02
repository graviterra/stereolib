import TetraStereo.OneCenter.CIPAuthoritativePublicOccurrenceRouting

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Occurrence-tree budget retirement

The public occurrence-local Rules 4--6 and axial/circular carrier entry points retain their
established names while routing through traversal bounded only by molecular depth.  Explicitly
budgeted helpers remain available to callers that intentionally request an operational cutoff.
-/

theorem buildOccurrenceAuxState?_eq_authoritative
    (mol : RawMolecule) (fuel center : Nat) :
    buildOccurrenceAuxState? mol fuel center =
      buildOccurrenceAuxStateAuthoritative? mol fuel center :=
  rfl

theorem exactCircularSharedRule3CarrierSense?_eq_capFree
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) :
    exactCircularSharedRule3CarrierSense? result mol state fuel center =
      exactCircularSharedRule3CarrierSenseCapFree? result mol state fuel center :=
  rfl

theorem branchExtendedTetrahedralPseudoSequence?_eq_capFree
    (mol : RawMolecule) (center ligand : Nat) :
    branchExtendedTetrahedralPseudoSequence? mol center ligand =
      branchExtendedTetrahedralPseudoSequenceCapFree? mol center ligand :=
  rfl

end TetraStereo.OneCenter
