import TetraStereo.OneCenter.AuthoritativeParserMaterializedEndpointRefinement
import TetraStereo.KernelOnly


























assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.exists_toSemanticMolecule?_of_noWildcard
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.originalAtomIndex_convertedAtomIndex
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.materializedCanonicalIndividualDoubleBondEndpoints_of_fullyRepresented
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.materializedCanonicalIndividualDoubleBondEndpoints_iff_fullyRepresented

assert_kernel_only TetraStereo.OneCenter.RawMolecule.hasNoWildcardAtom_eq_true_iff
assert_kernel_only TetraStereo.OneCenter.RawMolecule.exists_toSemanticMolecule?_of_hasNoWildcard

namespace TetraStereo.UniversalProof.ParserMaterializationProofs

open OneCenter

/-- The mechanical admission check accepts a represented carbon atom. -/
theorem wildcardAdmission_accepts_carbon :
    ({ atoms := [AtomSpec.aliphatic .C], bonds := [] } : RawMolecule).hasNoWildcardAtom = true := by
  decide

/-- A wildcard anywhere in the atom list is refused, even after a represented atom. -/
theorem wildcardAdmission_rejects_unknown :
    ({ atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .wildcard], bonds := [] } :
      RawMolecule).hasNoWildcardAtom = false := by
  decide

end TetraStereo.UniversalProof.ParserMaterializationProofs

assert_kernel_only TetraStereo.UniversalProof.ParserMaterializationProofs.wildcardAdmission_accepts_carbon
assert_kernel_only TetraStereo.UniversalProof.ParserMaterializationProofs.wildcardAdmission_rejects_unknown
