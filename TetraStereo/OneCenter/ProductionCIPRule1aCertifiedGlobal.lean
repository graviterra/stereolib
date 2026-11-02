import TetraStereo.OneCenter.ProductionCIPRule1aGlobalIntegration
import TetraStereo.OneCenter.ProductionCIPRule1aCertifiedShortcut

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-- The structurally certified executable dispatcher discharges the formerly abstract simple-cycle
branch obligation under only the ordinary raw-graph hypotheses. -/
theorem certifiedMancudeRule1aSimpleCycleBranchSound
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) :
    mol.MancudeRule1aSimpleCycleBranchSound := by
  exact mol.mancudeRule1aSimpleCycleBranchSound hwellFormed hunique

/-- Unconditional global Mancude Rule-1a soundness for every well-formed molecule with unique raw
bond records.  Unsupported components may still return `none`; every successful label is exact. -/
theorem certifiedMancudeRule1aSound
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) : mol.MancudeRule1aSound := by
  exact mol.mancudeRule1aSound_of_simpleCycleBranchSound hwellFormed hunique
    (mol.certifiedMancudeRule1aSimpleCycleBranchSound hwellFormed hunique)

/-- Final faithful exact-expansion/Rule-1a theorem with no Mancude or simple-cycle soundness
hypothesis remaining. -/
theorem branchCanonicalKey?_certifiedFaithfulExactExpansion_and_rule1aObservationCorrect
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand) :
    RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
        (key.toDeclarativeDigraph mol) ∧
      ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
        key.sourceNodeAtAddress? node.val = some source →
          key.RealizedRule1aObservationCorrectAt mol node source := by
  exact mol.branchCanonicalKey?_faithfulExactExpansion_and_rule1aObservationCorrect_of_global
    center ligand key hwellFormed hunique hkey hcomplete hrootBond
    (mol.certifiedMancudeRule1aSound hwellFormed hunique)

/-- The same final result stated with the normalized positive root-bond fact supplied by the
raw-molecule layer.  Positivity rules out a diagonal root and therefore supplies the adjacency
premise without an additional semantic assumption. -/
theorem branchCanonicalKey?_certifiedFaithfulExactExpansion_and_rule1aObservationCorrect_of_canonicalHierarchyBond_pos
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : 0 < mol.canonicalHierarchyBond center ligand center ligand) :
    RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
        (key.toDeclarativeDigraph mol) ∧
      ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
        key.sourceNodeAtAddress? node.val = some source →
          key.RealizedRule1aObservationCorrectAt mol node source := by
  have hdistinct : center ≠ ligand := by
    intro heq
    subst ligand
    simp at hrootBond
  exact mol.branchCanonicalKey?_certifiedFaithfulExactExpansion_and_rule1aObservationCorrect
    center ligand key hwellFormed hunique hkey hcomplete
    ((mol.canonicalHierarchyMoleculeGraph_root_adj_iff center ligand hdistinct).2 hrootBond)

end RawMolecule

end
end OneCenter
end TetraStereo
