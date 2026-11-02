import TetraStereo.OneCenter.ProductionCIPMultiplicity

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace DeclarativeCIP.RootedDigraph

universe u

variable {Atom : Type u}

/-!
# Final faithful-expansion assembly

This module keeps the last specification boundary explicit.  It packages already proved local,
multiplicity, root-bond, atom-bearing, and duplicate-distance facts into
`FaithfulExactExpansion`.  The imported specification separately proves that the strengthened
predicate is independent of the finite rooted-digraph representation.
-/

/-- Package the four independent clauses extending `ExactExpansion` into the strengthened
faithful-expansion boundary. -/
theorem faithfulExactExpansion_of_exact_components
    [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (hexact : ExactExpansion molecule externalParent ligand graph)
    (hrootBond : molecule.Adj externalParent ligand)
    (hatomChildren : AtomBearingChildren graph)
    (addressing : graph.Addressing)
    (hdistances : DuplicateDistancesCorrect graph externalParent addressing) :
    FaithfulExactExpansion molecule externalParent ligand graph :=
  ⟨hexact, hrootBond, hatomChildren,
    duplicateDistancesCorrect_all_of_one graph externalParent addressing hdistances⟩

/-- Assemble a faithful exact expansion directly from the local and exact-multiplicity component
proofs.  The same semantic addressing witnesses both exact child accounting and duplicate-distance
correctness. -/
theorem faithfulExactExpansion_of_components
    [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom)
    (hlocal : LocallyAdmissibleExpansion molecule ligand graph)
    (addressing : graph.Addressing)
    (hmultiplicities : AtomChildMultiplicities molecule externalParent graph)
    (hrootBond : molecule.Adj externalParent ligand)
    (hatomChildren : AtomBearingChildren graph)
    (hdistances : DuplicateDistancesCorrect graph externalParent addressing) :
    FaithfulExactExpansion molecule externalParent ligand graph :=
  faithfulExactExpansion_of_exact_components molecule externalParent ligand graph
    ⟨hlocal, addressing, hmultiplicities⟩ hrootBond hatomChildren addressing hdistances

end DeclarativeCIP.RootedDigraph

namespace RawMolecule

/-- Root adjacency in the normalized proof-facing molecule graph is exactly positivity of the
normalized root bond.  The distinctness hypothesis records the molecular-edge side condition used
by callers; the equality itself is the defining adjacency semantics of `MoleculeGraph`. -/
theorem canonicalHierarchyMoleculeGraph_root_adj_iff
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (_hdistinct : center ≠ ligand) :
    (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand ↔
      0 < mol.canonicalHierarchyBond center ligand center ligand := by
  rfl

/-- Package independently proved production component facts.  This theorem is useful when a caller
already has the multiplicity and distance witnesses; the theorem below discharges both from the
actual complete-build realization. -/
theorem branchCanonicalKey?_faithfulExactExpansion_of_components
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (hmultiplicities : RootedDigraph.AtomChildMultiplicities
      (mol.canonicalHierarchyMoleculeGraph center ligand) center
      (key.toDeclarativeDigraph mol))
    (hdistances : RootedDigraph.DuplicateDistancesCorrect
      (key.toDeclarativeDigraph mol) center (key.declarativeAddressing mol)) :
    RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      (key.toDeclarativeDigraph mol) := by
  have hlocal := mol.branchCanonicalKey?_locallyAdmissibleExpansion center ligand key
    hwellFormed hkey hcomplete
  have hatomChildren := mol.branchCanonicalKey?_atomBearingChildren center ligand key
    hwellFormed hkey hcomplete
  exact RootedDigraph.faithfulExactExpansion_of_components
    (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
    (key.toDeclarativeDigraph mol) hlocal (key.declarativeAddressing mol)
    hmultiplicities hrootBond hatomChildren hdistances

/-- A successful complete production hierarchy is a faithful exact declarative expansion, with
duplicate-root distances correct under every parent-preserving declarative addressing.

`WellFormed` excludes out-of-range bond endpoints, while `BondRecordsUnique` excludes repeated
unordered bond records (which would otherwise make the raw child generator emit duplicate
occurrences not represented by molecular bond order).  Root adjacency remains explicit because
`branchCanonicalKey?` is a total low-level function accepting any numeric ligand index. -/
theorem branchCanonicalKey?_faithfulExactExpansion
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand) :
    RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      (key.toDeclarativeDigraph mol) := by
  have hbuild := mol.branchCanonicalKey?_completeBuild center ligand key hkey hcomplete
  have hroot : key.RootedAt center ligand := canonicalCompleteBuild_root_source hbuild
  have hexact : key.ChildrenExact mol := hbuild.childrenExact
  have hmultiplicities := key.atomChildMultiplicities_of_rootedAt_childrenExact
    mol center ligand hwellFormed hunique hroot hexact
  have hdistances := key.duplicateDistancesCorrect_of_childrenExact
    mol center ligand hwellFormed hroot hexact
  exact mol.branchCanonicalKey?_faithfulExactExpansion_of_components center ligand key
    hwellFormed hkey hcomplete hrootBond hmultiplicities hdistances

/-- Convenient final production theorem stated with the normalized bond-order fact emitted by the
raw-molecule layer.  Positivity itself proves that center and ligand are distinct, after which the
root-adjacency helper supplies the corresponding declarative graph obligation. -/
theorem branchCanonicalKey?_faithfulExactExpansion_of_canonicalHierarchyBond_pos
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : 0 < mol.canonicalHierarchyBond center ligand center ligand) :
    RootedDigraph.FaithfulExactExpansion
      (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
      (key.toDeclarativeDigraph mol) := by
  have hdistinct : center ≠ ligand := by
    intro heq
    subst ligand
    simp at hrootBond
  exact mol.branchCanonicalKey?_faithfulExactExpansion center ligand key
    hwellFormed hunique hkey hcomplete
    ((mol.canonicalHierarchyMoleculeGraph_root_adj_iff center ligand hdistinct).2 hrootBond)

end RawMolecule

end
end OneCenter
end TetraStereo
