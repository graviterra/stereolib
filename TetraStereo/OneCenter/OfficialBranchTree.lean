import TetraStereo.OneCenter.OfficialHierarchicalDigraph
import TetraStereo.OneCenter.BranchSphereKey

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section
































































/-- A certified enumeration of a finite vertex type.

The branch expansion reads neighbours out of this list rather than a `Finset`, so the list itself is
part of the trusted input: dropping a vertex hides a substituent and duplicating one counts a
substituent twice, and both silently change a comparison.  Carrying `complete` and `nodup` here
makes an uncertified enumeration unrepresentable rather than merely discouraged. -/
structure VertexEnumeration (V : Type*) [Fintype V] [DecidableEq V] where
  vertices : List V
  complete : ∀ v : V, v ∈ vertices
  nodup : vertices.Nodup

/-- The canonical enumeration of `Fin n`. -/
def finVertexEnumeration (n : ℕ) : VertexEnumeration (Fin n) where
  vertices := List.finRange n
  complete := by intro v; simp
  nodup := List.nodup_finRange n

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A rooted expansion of the official hierarchical digraph.

Unlike a breadth-first frontier this keeps every node attached to its parent, which is what makes
branch ranking well defined. -/
inductive OfficialBranchTree (V : Type*) where
  | node (label : OfficialCIPNode V) (children : List (OfficialBranchTree V))

namespace OfficialBranchTree

/-- The node label at the root of this branch. -/
def label : OfficialBranchTree V → OfficialCIPNode V
  | .node l _ => l

/-- The immediate sub-branches. -/
def children : OfficialBranchTree V → List (OfficialBranchTree V)
  | .node _ cs => cs

end OfficialBranchTree

/-- Neighbour copies enumerated from an explicit vertex list.

Mirrors `officialNeighborCopies`, including one copy per unit of bond order, but avoids
`Finset.toList` so that the result reduces in the kernel. -/
def officialNeighborCopiesFrom (m : MoleculeGraph V) (vertices : VertexEnumeration V) (atom : V) :
    List (V × ℕ) :=
  (vertices.vertices.filter fun neighbor => decide (m.Adj atom neighbor)).flatMap fun neighbor =>
    (List.range (m.bond atom neighbor)).map fun copyIndex => (neighbor, copyIndex)

/-- Child copies from an explicit vertex list, removing the zero-index parent occurrence exactly as
`officialChildCopies` does. -/
def officialChildCopiesFrom (m : MoleculeGraph V) (vertices : VertexEnumeration V)
    (node : OfficialCIPNode V) : List (V × ℕ) :=
  match node.current? with
  | none => []
  | some current =>
      match node.parent? with
      | none => m.officialNeighborCopiesFrom vertices current
      | some parent =>
          (m.officialNeighborCopiesFrom vertices current).filter fun copy =>
            !(copy.1 == parent && copy.2 == 0)

/-- Official children from an explicit vertex list.  Duplicate and placeholder nodes remain leaves,
and multiple-bond copies keep their provenance, exactly as in `officialCIPChildren`. -/
def officialCIPChildrenFrom (m : MoleculeGraph V) (vertices : VertexEnumeration V)
    (node : OfficialCIPNode V) : List (OfficialCIPNode V) :=
  if node.isDuplicateLeaf then
    []
  else
    (m.officialChildCopiesFrom vertices node).map fun copy => node.extend copy.1 copy.2

/-- Expand one official digraph node into a branch tree, to the given depth.

Expansion mirrors `officialCIPChildren`, so duplicate, ring-duplicate and placeholder nodes remain
leaves and multiple-bond copies keep their provenance.  Only the *shape* of the result differs from
the breadth-first engine: parentage is retained. -/
def buildOfficialBranchTree (m : MoleculeGraph V) (vertices : VertexEnumeration V) :
    ℕ → OfficialCIPNode V → OfficialBranchTree V
  | 0, node => .node node []
  | fuel + 1, node =>
      .node node ((m.officialCIPChildrenFrom vertices node).map fun child =>
        m.buildOfficialBranchTree vertices fuel child)

/-- Pairwise comparison of two already-ranked branch lists.

A shorter list loses at exhaustion, matching `frontierExhaustionDecision`.  Comparison stops at the
first branch pair that separates, so the emitted trace records the decision that was actually
reached rather than every subsequent tie. -/
def compareOfficialBranchListTraceWith
    (cmp : OfficialBranchTree V → OfficialBranchTree V → List CIPRuleDecision) :
    List (OfficialBranchTree V) → List (OfficialBranchTree V) → List CIPRuleDecision
  | [], [] => []
  | [], _ :: _ => [CIPRuleEngine.frontierExhaustionDecision Ordering.lt]
  | _ :: _, [] => [CIPRuleEngine.frontierExhaustionDecision Ordering.gt]
  | left :: lefts, right :: rights =>
      let head := cmp left right
      if cipTraceOutcome head = Ordering.eq then
        head ++ compareOfficialBranchListTraceWith cmp lefts rights
      else
        head

/-- Rule-traced, parent-preserving comparison of two branch trees.

The root labels are compared first.  If they tie, each root's children are ranked against each other
by the same comparison one level shallower, ordered highest-first, and then compared pairwise.  A
sub-branch is therefore only ever compared against its opposite number in the ranking, never against
an unrelated node that happens to sit in the same sphere. -/
def compareOfficialBranchTreeTrace (m : MoleculeGraph V) :
    ℕ → OfficialBranchTree V → OfficialBranchTree V → List CIPRuleDecision
  | 0, _, _ => []
  | fuel + 1, left, right =>
      let head := m.compareOfficialNodeTrace left.label right.label
      if cipTraceOutcome head = Ordering.eq then
        let rankBefore := fun (a b : OfficialBranchTree V) =>
          cipTraceOutcome (m.compareOfficialBranchTreeTrace fuel a b) != Ordering.lt
        head ++
          compareOfficialBranchListTraceWith
            (fun a b => m.compareOfficialBranchTreeTrace fuel a b)
            (sortDescBy rankBefore left.children)
            (sortDescBy rankBefore right.children)
      else
        head

/-- Rank two branches rooted at the given official nodes, preserving parentage throughout. -/
def compareOfficialBranchFromTrace (m : MoleculeGraph V) (vertices : VertexEnumeration V) (fuel : ℕ)
    (left right : OfficialCIPNode V) : List CIPRuleDecision :=
  m.compareOfficialBranchTreeTrace fuel
    (m.buildOfficialBranchTree vertices fuel left)
    (m.buildOfficialBranchTree vertices fuel right)

/-- Proof-carrying parent-preserving branch comparison. -/
def compareOfficialBranchFromCertificate (m : MoleculeGraph V) (vertices : VertexEnumeration V) (fuel : ℕ)
    (left right : OfficialCIPNode V) : CIPTraceCertificate :=
  CIPTraceCertificate.ofTrace (m.compareOfficialBranchFromTrace vertices fuel left right)

/-- Rank the two ligand branches leaving `center` towards `left` and `right`. -/
def compareOfficialBranchEdges (m : MoleculeGraph V) (vertices : VertexEnumeration V) (fuel : ℕ)
    (center left right : V) : List CIPRuleDecision :=
  m.compareOfficialBranchFromTrace vertices fuel
    (OfficialCIPNode.rootFromEdge center left) (OfficialCIPNode.rootFromEdge center right)

@[simp] theorem compareOfficialBranchTreeTrace_zero (m : MoleculeGraph V)
    (left right : OfficialBranchTree V) :
    m.compareOfficialBranchTreeTrace 0 left right = [] :=
  rfl

@[simp] theorem buildOfficialBranchTree_zero (m : MoleculeGraph V) (vertices : VertexEnumeration V)
    (node : OfficialCIPNode V) :
    m.buildOfficialBranchTree vertices 0 node = .node node [] :=
  rfl

/-- A duplicate leaf never expands, so its branch tree is a single node at any depth. -/
theorem buildOfficialBranchTree_of_duplicateLeaf (m : MoleculeGraph V) (vertices : VertexEnumeration V)
    (fuel : ℕ) (node : OfficialCIPNode V) (h : node.isDuplicateLeaf = true) :
    m.buildOfficialBranchTree vertices fuel node = .node node [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp [buildOfficialBranchTree, officialCIPChildrenFrom, h]

/-- With no fuel the comparison is empty, hence ties; every decision is reached by spending fuel. -/
theorem compareOfficialBranchFromTrace_zero (m : MoleculeGraph V) (vertices : VertexEnumeration V)
    (left right : OfficialCIPNode V) :
    m.compareOfficialBranchFromTrace vertices 0 left right = [] :=
  rfl

end MoleculeGraph

end
end OneCenter
end TetraStereo
