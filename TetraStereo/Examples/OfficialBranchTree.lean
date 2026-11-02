import TetraStereo.OneCenter.OfficialBranchTree

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace OfficialBranchTree

open OneCenter

/-!
  A branch pair that the breadth-first official comparator cannot separate.

  Both ligands of `sphereTieDemo` present the same atom multiset in every sphere:

  * sphere 1 — one carbon;
  * sphere 2 — one oxygen and one carbon;
  * sphere 3 — one carbon.

  They differ only in *where* the sphere-3 carbon hangs.  In the left branch it is attached to the
  oxygen; in the right branch it is attached to the carbon.  Under the sequence rules the left
  branch wins: the oxygen outranks the carbon at sphere 2, so the two oxygen sub-branches are
  compared against each other first, and the left oxygen carries a substituent where the right
  oxygen is a leaf.

  Comparing sorted whole spheres cannot see this, because the spheres are equal as multisets.  No
  amount of fuel changes that — the information is destroyed when parentage is dropped.
-/

/-- Unordered skeleton bonds of the demonstration molecule.

Left branch from the centre `0`: `1` carries an oxygen `2` and a carbon `3`, and the oxygen carries
a further carbon `4`.  Right branch: `5` carries an oxygen `6` and a carbon `7`, and this time the
*carbon* carries the further carbon `8`. -/
def sphereTieBonds : List (Fin 9 × Fin 9) :=
  [ (0, 1), (1, 2), (1, 3), (2, 4)
  , (0, 5), (5, 6), (5, 7), (7, 8) ]

/-- Carbon skeleton with oxygens at `2` and `6`. -/
def sphereTieDemo : MoleculeGraph (Fin 9) where
  atomZ := fun atom => if atom = 2 ∨ atom = 6 then 8 else 6
  atomMass := fun _ => 0
  bond := fun u v =>
    if sphereTieBonds.contains (u, v) || sphereTieBonds.contains (v, u) then 1 else 0
  bond_symm := by decide
  bond_self := by decide

/-- Every vertex of the demonstration molecule, as a kernel-reducible enumeration. -/
def sphereTieVertices : VertexEnumeration (Fin 9) := finVertexEnumeration 9

/-- Branch root leaving the centre towards the left ligand. -/
def leftRoot : OfficialCIPNode (Fin 9) :=
  OfficialCIPNode.rootFromEdge 0 1

/-- Branch root leaving the centre towards the right ligand. -/
def rightRoot : OfficialCIPNode (Fin 9) :=
  OfficialCIPNode.rootFromEdge 0 5

/-- Sphere 1 ties: both ligands are carbon, with the same provenance.

The breadth-first comparator must therefore expand to decide this pair.  No theorem here states what
it then returns, and that is deliberate: expanding calls `sortOfficialLayer` (`List.mergeSort`, which
is well-founded recursion) and `officialNeighborCopies` (`Finset.toList`, which needs choice), so its
result on this molecule cannot be evaluated in the kernel at all.  The contrast below is between a
comparator that produces a checkable answer and one that cannot be run. -/
theorem rootLabels_tie :
    cipTraceOutcome (sphereTieDemo.compareOfficialNodeTrace leftRoot rightRoot) = Ordering.eq := by
  decide

/-- The comparator separates them and ranks the left branch higher.

The outcome agrees with CIP on *this* molecule, but the mechanism that produces it does not: the
comparison descends into the ranked oxygen sub-branch before finishing sphere II, and that ordering
is wrong in general.  See the status note in `OneCenter/OfficialBranchTree.lean`.  This theorem
records current behaviour; it is not evidence that the comparator is correct. -/
theorem branchTree_separates :
    cipTraceOutcome (sphereTieDemo.compareOfficialBranchEdges sphereTieVertices 6 0 1 5) = Ordering.gt := by
  decide

/-- The separation is antisymmetric: swapping the two ligands reverses the outcome. -/
theorem branchTree_separates_swapped :
    cipTraceOutcome (sphereTieDemo.compareOfficialBranchEdges sphereTieVertices 6 0 5 1) = Ordering.lt := by
  decide

/-- A branch is tied with itself, so the new comparator is reflexive here rather than merely
discriminating. -/
theorem branchTree_self_ties :
    cipTraceOutcome (sphereTieDemo.compareOfficialBranchEdges sphereTieVertices 6 0 1 1) = Ordering.eq := by
  decide

end OfficialBranchTree
end Examples
end TetraStereo
