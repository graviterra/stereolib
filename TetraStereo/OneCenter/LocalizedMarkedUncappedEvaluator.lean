import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator
import TetraStereo.OneCenter.LocalizedMarkedUncappedOperations
import TetraStereo.OneCenter.LocalizedMarkedGeneratedFactUniqueness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The uncapped instance of recursive promotion-context evaluation

This is a complete executable recursive instance, using the existing uncapped partition/ranker
at the proved reroot-support bound, not a final-result fallback. Every internally opened context
uses those operations. Structural recursion is the same shared construction whose bounded
instance is exactly the accepted original evaluator.

The step-totality theorem covers arbitrary auxiliary states at every reached actual frame.
On single-bond inputs, the generated-state theorem additionally eliminates duplicate-key
refusal from the internally constructed promotion extension.
It does not imply a unique ordering, nondegenerate geometry, consensus success or faithful
chemical priority. Those semantic obligations and the cage output-agreement proof remain open.
Production defaults and the earlier accepted constructor remain unchanged.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator

open LocalizedMarkedOperationEvaluator LocalizedMarkedReachableConfigurations
open LocalizedGenericMarkedRecalculation (Geometry structuralDepth frameAtomsOf WellFormedBonds)
open AuthoritativeCIPMancudeTotality

def operations (mol : RawMolecule) : Operations where
  ordinary := LocalizedMarkedUncappedOperations.ordinary? mol
  marked := LocalizedMarkedUncappedOperations.marked? mol

def assignCenter? (mol : RawMolecule) (geom : Geometry) (center : Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  LocalizedMarkedOperationEvaluator.assignCenter? mol (operations mol) geom center

def assign (mol : RawMolecule) (geom : Geometry) :
    List (Nat × LocalizedTetrahedralRSPseudoDescriptor) :=
  LocalizedMarkedOperationEvaluator.assign mol (operations mol) geom

/-- Every operation used by a reached context has a result under the chemical intake conditions;
the temporary state is arbitrary, so generated fact lists need no label-correctness assumption. -/
theorem reached_operations_total (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (roots : List CanonicalRerootCursor)
    (frame : occurrenceLigandFrame? mol node = some roots) :
    (∃ sorted adjacent, (operations mol).ordinary state node = some (sorted, adjacent) ∧
      sorted.Perm [0, 1, 2, 3] ∧ adjacent.length = 3) ∧
    (∀ mark ∈ frameAtomsOf roots, ∃ ranking, (operations mol).marked state node mark = some ranking ∧
      ranking.positions.Perm [0, 1, 2, 3]) :=
  LocalizedMarkedUncappedOperations.operations_exist mol wellFormed unique valence kekule
    state node reached roots frame

/-- The actual generated extension and subsequent marked ranking both succeed. The temporary
labels and their key uniqueness are derived, not supplied as data-level premises. -/
theorem generated_marked_ranking_exists (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : LocalizedMarkedReachedFrameNeighbors.SingleBonded mol)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol) (depth : Nat) (geom : Geometry)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (roots : List CanonicalRerootCursor) (frame : occurrenceLigandFrame? mol node = some roots)
    (mark : Nat) (member : mark ∈ frameAtomsOf roots) :
    ∃ ranking,
      ((LocalizedGenericMarkedRecalculation.appendFacts? []
        (underWith mol (operations mol) geom [] node (facts mol (operations mol) depth) mark)).bind
          (fun temp => (operations mol).marked temp node mark)) = some ranking ∧
      ranking.positions.Perm [0, 1, 2, 3] := by
  rw [LocalizedMarkedGeneratedFactUniqueness.generated_extension_succeeds mol (operations mol)
    wellFormed single unique depth geom node mark]
  exact (reached_operations_total mol wellFormed unique valence kekule
    (underWith mol (operations mol) geom [] node (facts mol (operations mol) depth) mark)
    node reached roots frame).2 mark member

/-- Increasing the recursion depth beyond its molecular structural bound does not change output. -/
theorem assignCenter_stable (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (geom : Geometry) (center : Nat) (valid : center < mol.atomCount) (k : Nat) :
    descriptor? mol (operations mol) (structuralDepth mol (canonicalCenterRoot center) + k)
        geom [] none (canonicalCenterRoot center) = assignCenter? mol geom center := by
  have endpoints : WellFormedBonds mol := fun bond member =>
    ⟨(wellFormed bond member).1, (wellFormed bond member).2.1⟩
  exact LocalizedMarkedOperationEvaluator.assignCenter?_stable mol (operations mol)
    endpoints geom center valid k

end TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator.reached_operations_total
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator.assignCenter_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedUncappedEvaluator.generated_marked_ranking_exists
