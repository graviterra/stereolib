import TetraStereo.OneCenter.IUPACP92SemanticGraphFaithfulExpansion
import TetraStereo.OneCenter.IUPACP92SemanticGraphRepresentationBridge
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false

/-!
# Canonical semantic production graph for P-92

This module packages the graph-native hierarchy as the fixed P-92 exact-digraph observation.
The molecule is always the canonical graph derived from the authoritative semantic source.  Node
codes are computed from the tree's de-duplicated canonical address list, rather than selected by
`Fintype.equivFin`. Neither the molecule nor its hierarchy is selected from a reviewed observation.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP

section

/-- Canonical finite list of hierarchy nodes in first-address order. -/
def p92SemanticHierarchyNodes {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex) : List tree.HierarchyNode :=
  tree.hierarchyAddresses.attach.dedup

theorem p92SemanticHierarchyNodes_nodup {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex) : (p92SemanticHierarchyNodes tree).Nodup := by
  exact List.nodup_dedup _

theorem p92SemanticHierarchyNodes_complete {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex) (node : tree.HierarchyNode) :
    node ∈ p92SemanticHierarchyNodes tree := by
  exact List.mem_dedup.mpr (List.mem_attach tree.hierarchyAddresses node)

/-- Computable address-order reindexing of the recursive hierarchy carrier. -/
def p92SemanticHierarchyNodeEquivFin {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex) :
    tree.HierarchyNode ≃ Fin (p92SemanticHierarchyNodes tree).length :=
  ((p92SemanticHierarchyNodes_nodup tree).getEquivOfForallMemList
    (p92SemanticHierarchyNodes tree) (p92SemanticHierarchyNodes_complete tree)).symm

/-- Executable immediate-parent relation on canonical hierarchy addresses.  The last address
component is the sibling slot, so this is propositionally identical to `HierarchyChild` without
its unbounded existential presentation. -/
def p92SemanticHierarchyChild {vertex : Type}
    (tree : OfficialCIPSourceTree vertex)
    (parent node : tree.HierarchyNode) : Prop :=
  match node.1.getLast? with
  | none => False
  | some slot => node.1 = parent.1 ++ [slot]

theorem p92SemanticHierarchyChild_iff {vertex : Type}
    (tree : OfficialCIPSourceTree vertex)
    (parent node : tree.HierarchyNode) :
    p92SemanticHierarchyChild tree parent node ↔ tree.HierarchyChild parent node := by
  constructor
  · intro executable
    unfold p92SemanticHierarchyChild at executable
    split at executable
    · contradiction
    · exact ⟨_, executable⟩
  · rintro ⟨slot, address⟩
    unfold p92SemanticHierarchyChild
    rw [address]
    simp

/-- Canonical finite graph code for a recursive source tree.  All data fields compute through the
explicit address list; only later proof-level comparison with the subtype-carrier graph uses an
isomorphism. -/
def p92SemanticFiniteRootedDigraph {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex) : P92FiniteRootedDigraph vertex := by
  let nodeEquiv := p92SemanticHierarchyNodeEquivFin tree
  refine
    { nodeCount := (p92SemanticHierarchyNodes tree).length
      root := nodeEquiv ⟨[], tree.nil_mem_hierarchyAddresses⟩
      child := fun parent node => p92SemanticHierarchyChild tree
        (nodeEquiv.symm parent) (nodeEquiv.symm node)
      label := fun node => tree.declarativeLabel (nodeEquiv.symm node)
      depth := fun node => (nodeEquiv.symm node).1.length
      root_depth := ?_
      child_depth := ?_
      reachable := ?_ }
  · rw [nodeEquiv.symm_apply_apply]
    rfl
  · intro parent node edge
    rw [p92SemanticHierarchyChild_iff] at edge
    rcases edge with ⟨slot, address⟩
    rw [address]
    simp
  · intro node
    have sourceReachable := tree.hierarchyReachable
      (nodeEquiv.symm node).1 (nodeEquiv.symm node).2
    have mapReachable : ∀ {target : tree.HierarchyNode},
        Relation.ReflTransGen tree.HierarchyChild
            ⟨[], tree.nil_mem_hierarchyAddresses⟩ target →
          Relation.ReflTransGen
            (fun parent child => p92SemanticHierarchyChild tree
              (nodeEquiv.symm parent) (nodeEquiv.symm child))
            (nodeEquiv ⟨[], tree.nil_mem_hierarchyAddresses⟩)
            (nodeEquiv target) := by
      intro target path
      induction path with
      | refl => exact .refl
      | tail path edge inductionHypothesis =>
          exact .tail inductionHypothesis (by
            rw [p92SemanticHierarchyChild_iff]
            simpa using edge)
    simpa using mapReachable sourceReachable

/-- Concrete decision procedure for the emitted graph's child relation.  This exposes the
computability already present in the last-address formulation without changing the independent
`P92FiniteRootedDigraph` reference type. -/
def p92SemanticFiniteRootedDigraph_childDecidable
    {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex) :
    DecidableRel (p92SemanticFiniteRootedDigraph tree).child := by
  intro parent node
  change Decidable (p92SemanticHierarchyChild tree
    ((p92SemanticHierarchyNodeEquivFin tree).symm parent)
    ((p92SemanticHierarchyNodeEquivFin tree).symm node))
  unfold p92SemanticHierarchyChild
  split <;> infer_instance

/-- Proof-level isomorphism between the subtype-address graph and its computable finite code. -/
noncomputable def p92SemanticFiniteRootedDigraphIso
    {vertex : Type} [DecidableEq vertex]
    (tree : OfficialCIPSourceTree vertex) :
    RootedDigraph.Iso tree.toDeclarativeDigraph
      (p92SemanticFiniteRootedDigraph tree).toRootedDigraph := by
  let nodeEquiv := p92SemanticHierarchyNodeEquivFin tree
  exact
    { toEquiv := nodeEquiv
      map_root := rfl
      map_child := by
        intro parent node
        change tree.HierarchyChild parent node ↔
          p92SemanticHierarchyChild tree
            (nodeEquiv.symm (nodeEquiv parent))
            (nodeEquiv.symm (nodeEquiv node))
        simp [p92SemanticHierarchyChild_iff]
      map_label := by
        intro node
        change tree.declarativeLabel node =
          tree.declarativeLabel (nodeEquiv.symm (nodeEquiv node))
        simp
      map_depth := by
        intro node
        change node.1.length = (nodeEquiv.symm (nodeEquiv node)).1.length
        simp }

/-- Literal source-only tree used by P-92 production.  It is total as data; faithful-expansion
proofs establish its generatedness when the requested root is a genuine molecular edge. -/
def p92SemanticOfficialSourceTree
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount) :
    OfficialCIPSourceTree (Fin source.molecule.atomCount) :=
  (p92CanonicalLocalizedMoleculeGraph source center ligand).buildSemanticOfficialSourceTree
    (source.molecule.atomCount + 1) (OfficialCIPNode.rootFromEdge center ligand)

/-- The source-derived exact-digraph observation emitted by the semantic hierarchy compiler. -/
def p92SemanticExactDigraphObservation
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount) :
    P92ExactDigraphAuthorityObservation where
  atomCount := source.molecule.atomCount
  molecule := p92CanonicalLocalizedMoleculeGraph source center ligand
  externalParent := center
  ligand := ligand
  graph := p92SemanticFiniteRootedDigraph
    (p92SemanticOfficialSourceTree source center ligand)

theorem p92SemanticOfficialSourceTree_generated
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (rootBond : (p92CanonicalLocalizedMoleculeGraph source center ligand).Adj center ligand) :
    (p92SemanticOfficialSourceTree source center ligand).GeneratedBy
      (p92CanonicalLocalizedMoleculeGraph source center ligand).semanticOfficialCIPChildren := by
  have different : ligand ≠ center := by
    intro same
    subst ligand
    simp [MoleculeGraph.Adj,
      (p92CanonicalLocalizedMoleculeGraph source center center).bond_self] at rootBond
  exact MoleculeGraph.buildSemanticOfficialSourceTree_generated
    (p92CanonicalLocalizedMoleculeGraph source center ligand)
      (source.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center ligand)
      (MoleculeGraph.semanticOfficialExpansionCompleteWithin_default
        (p92CanonicalLocalizedMoleculeGraph source center ligand) center ligand different)

/-- The finite encoding preserves the unconditional graph-native faithful expansion exactly. -/
theorem p92SemanticExactDigraphObservation_faithful
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (rootBond : (p92CanonicalLocalizedMoleculeGraph source center ligand).Adj center ligand) :
    (p92SemanticExactDigraphObservation source center ligand).Faithful := by
  let hierarchy : MoleculeGraph.SemanticOfficialHierarchy
      (p92CanonicalLocalizedMoleculeGraph source center ligand) center ligand :=
    { tree := p92SemanticOfficialSourceTree source center ligand
      generated := p92SemanticOfficialSourceTree_generated source center ligand rootBond
      rootSource := rfl }
  apply (RootedDigraph.faithfulExactExpansion_iso_iff
    (p92CanonicalLocalizedMoleculeGraph source center ligand) center ligand
    (p92SemanticFiniteRootedDigraphIso hierarchy.tree)).1
  exact hierarchy.faithfulExactExpansion rootBond

/-- Source representation is retained by the canonical observation without consulting a
reviewed graph or judgment. -/
theorem p92SemanticExactDigraphObservation_represents
    (source : AuthoritativeChemicalInput)
    (center ligand : Fin source.molecule.atomCount)
    (represented : P92CanonicalConstitutionRepresents source center ligand
      (p92CanonicalLocalizedMoleculeGraph source center ligand)) :
    (p92SemanticExactDigraphObservation source center ligand).Represents source :=
  represented

end

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SemanticFiniteRootedDigraphIso
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SemanticOfficialSourceTree_generated
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SemanticExactDigraphObservation_faithful
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92SemanticExactDigraphObservation_represents
