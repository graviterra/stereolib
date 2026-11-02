import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Default branch-width retirement

The chemistry-facing descriptor hierarchy, provisional auxiliary ordering, circular and axial
ranking, and projected Rule-6 promotion now route through the molecular-depth authoritative branch
comparator and key compiler.  Explicit-budget diagnostic helpers remain separately named.
-/

theorem branchDescriptorCanonicalKey?_eq_authoritative
    (mol : RawMolecule) (center ligand : Nat) :
    branchDescriptorCanonicalKey? mol center ligand =
      branchCanonicalKeyAuthoritative? mol center ligand :=
  rfl

theorem tentativeAuxiliaryFactAt?_eq_authoritative
    (mol : RawMolecule) (fuel atom : Nat) :
    tentativeAuxiliaryFactAt? mol fuel atom =
      tentativeAuxiliaryFactAtAuthoritative? mol atom :=
  rfl

theorem rawAuxiliaryOccurrenceSense_eq_authoritative
    (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (fact : RawDescriptorFact) :
    rawAuxiliaryOccurrenceSense mol node fact =
      rawAuxiliaryOccurrenceSenseAuthoritative mol node fact :=
  rfl

theorem rankBranchPositionsThroughCircularRule3?_eq_authoritative
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel center : Nat) (branches : List Nat) :
    rankBranchPositionsThroughCircularRule3? result mol fuel center branches =
      rankBranchPositionsThroughCircularRule3Authoritative? result mol center branches :=
  rfl

theorem rankBranchPositionsThroughExtendedTetrahedralPseudo?_eq_authoritative
    (mol : RawMolecule) (fuel center : Nat) (ligands : List Nat) :
    rankBranchPositionsThroughExtendedTetrahedralPseudo? mol fuel center ligands =
      rankBranchPositionsThroughExtendedTetrahedralPseudoAuthoritative? mol center ligands :=
  rfl

theorem rule6PromotionLayers?_eq_authoritative
    (mol : RawMolecule) (fuel center ligand reference : Nat) :
    rule6PromotionLayers? mol fuel center ligand reference =
      rule6PromotionLayersAuthoritative? mol center ligand reference :=
  rfl

end TetraStereo.OneCenter
