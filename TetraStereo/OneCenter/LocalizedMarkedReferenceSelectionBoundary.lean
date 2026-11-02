import TetraStereo.OneCenter.SmilesRule4bReferenceFrontierFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The ranked-reference boundary also reaches the unrestricted promoted comparator

`SmilesRule4bReferenceFrontierFidelity` already supplies an admitted, finite acyclic molecule,
its actually generated auxiliary state, and a Rule-4b reference-selection discrepancy. The raw
selector counts every uppercase fact in the nearest occupied frontier; its ranked-source
counterpart first restricts that population to the highest hierarchy rank. The existing witness
contains one double bond and therefore is not a single-bonded retained-context example.

This module connects that existing witness to the unrestricted comparator used by the experimental
marked evaluator. Its constitutional and Rule-4a stages tie, its ordinary Rule-4b stage decides
`gt`, and every Rule-6 reference preserves that decision without using promotion. The actual
two-child insertion sort consequently has the opposite order to the existing ranked-source
control. No generated marked state, whole marked-evaluator output, or equality of that control
with the independent retained-context molecular specification is claimed.

This is a Rule-4b selection boundary upstream of Rule 6. It is not a counterexample to the
independent canonical promoted-address construction, nor to retained-path Rule-1b observations.

The final section also removes the witness's remote double bond. Its atom and edge lists and
the two observed ligand branches are retained, every bond record is single, and the exact same
reference discrepancies hold on the fixed supplied state. That state's generation on the modified
molecule is deliberately not asserted.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary

/-- The uncapped constitutional comparison also ties on the existing two ligand occurrences. -/
theorem unrestricted_constitutional_tie :
    compareCursorBranchAtAuthoritative? witnessMolecule 8 .rule2 leftCursor rightCursor =
      some .eq := by
  decide

/-- Removing the width cutoff does not introduce an earlier Rule-4a decision in this witness. -/
theorem unrestricted_rule4a_tie :
    compareOccurrenceDescriptorAtTiedRootAuthoritative? witnessMolecule witnessAuxState 8 .rule4a
      leftCursor rightCursor = some .eq := by
  decide

/-- The unrestricted Rule-4b entry point uses the same whole-frontier reference population. -/
theorem unrestricted_rule4b_decision :
    compareOccurrenceRule4bUnrestrictedAuthoritative? witnessMolecule witnessAuxState 8
      leftCursor rightCursor = some .gt := by
  simp [compareOccurrenceRule4bUnrestrictedAuthoritative?, live_left_references,
    live_right_references]

/-- The actual unrestricted ordinary comparison is decided by Rule 4b. -/
theorem unrestricted_ordinary_decision :
    compareOccurrenceBranchesUnrestrictedAuthoritative? witnessMolecule witnessAuxState 8
      leftCursor rightCursor = some { ordering := .gt } := by
  simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, unrestricted_constitutional_tie,
    unrestricted_rule4a_tie, unrestricted_rule4b_decision]

/-- Any fixed Rule-6 reference leaves the earlier decision intact; the promotion-use bit is false. -/
theorem promoted_decision (reference : Nat) :
    compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
      witnessMolecule witnessAuxState reference 8 leftCursor rightCursor =
        some { ordering := .gt, pseudo := false } := by
  simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?,
    unrestricted_ordinary_decision]

/-- The actual promoted child-sort callback retains the left-before-right order for every mark. -/
theorem promoted_pair_sort (reference : Nat) :
    sortCursorsBy?
      (fun left right =>
        (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          witnessMolecule witnessAuxState reference 8 left right).map
            Rule6TrackedDecision.ordering)
      [leftCursor, rightCursor] = some [leftCursor, rightCursor] := by
  simp [sortCursorsBy?, insertCursorBy?, promoted_decision]

/-- Replacing only the earlier reference selector with the existing ranked-source control gives
the opposite two-child order. This control is not a theorem about the full retained evaluator. -/
theorem ranked_source_pair_sort :
    sortCursorsBy?
      (fun left right =>
        (compareOccurrenceBranchesSource? witnessMolecule witnessAuxState 8 left right).map
          OccurrenceComparison.ordering)
      [leftCursor, rightCursor] = some [rightCursor, leftCursor] := by
  simp [sortCursorsBy?, insertCursorBy?, source_branch_comparison]

/-- Promotion cannot repair this earlier-reference decision: both exact sort results disagree. -/
theorem promoted_sort_disagrees_with_ranked_source (reference : Nat) :
    sortCursorsBy?
      (fun left right =>
        (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          witnessMolecule witnessAuxState reference 8 left right).map
            Rule6TrackedDecision.ordering)
      [leftCursor, rightCursor] ≠
    sortCursorsBy?
      (fun left right =>
        (compareOccurrenceBranchesSource? witnessMolecule witnessAuxState 8 left right).map
          OccurrenceComparison.ordering)
      [leftCursor, rightCursor] := by
  rw [promoted_pair_sort, ranked_source_pair_sort]
  decide

/-! ## The reference-selection discrepancy persists with only single bond records -/

/-- The remote formyl bond becomes single. The ligand atoms and supplied state are unchanged. -/
def singleBondMolecule : RawMolecule :=
  { witnessMolecule with
    bonds := witnessMolecule.bonds.map fun bond => { bond with kind := .single } }

theorem singleBondMolecule_admissible : singleBondMolecule.admissible? = true := by
  decide

/-- Removing the double-bond order preserves every unordered edge of the original witness. -/
theorem singleBondMolecule_edges :
    singleBondMolecule.bonds.map RawBond.edgeKey = witnessMolecule.bonds.map RawBond.edgeKey := by
  decide

theorem singleBondMolecule_records :
    ∀ bond ∈ singleBondMolecule.bonds, bond.kind = .single := by
  intro bond member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Exact reference populations on the modified molecule and the fixed supplied state. -/
theorem singleBond_reference_populations :
    occurrenceRule4bReferences singleBondMolecule witnessAuxState 8 [leftCursor] = [RS.R] ∧
    occurrenceRule4bReferences singleBondMolecule witnessAuxState 8 [rightCursor] =
      [RS.R, RS.S] ∧
    occurrenceSourceRule4bReferences singleBondMolecule witnessAuxState 8 leftCursor = [RS.S] ∧
    occurrenceSourceRule4bReferences singleBondMolecule witnessAuxState 8 rightCursor = [RS.R] := by
  decide

/-- A fixed-state single-bond counterexample to identifying raw and ranked reference selection. -/
theorem singleBond_reference_discrepancy :
    occurrenceRule4bReferences singleBondMolecule witnessAuxState 8 [leftCursor] ≠
      occurrenceSourceRule4bReferences singleBondMolecule witnessAuxState 8 leftCursor := by
  rw [singleBond_reference_populations.1, singleBond_reference_populations.2.2.1]
  decide

end TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.unrestricted_constitutional_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.unrestricted_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.unrestricted_rule4b_decision
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.unrestricted_ordinary_decision
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.promoted_decision
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.promoted_pair_sort
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.ranked_source_pair_sort
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.promoted_sort_disagrees_with_ranked_source
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.singleBondMolecule_admissible
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.singleBondMolecule_edges
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.singleBondMolecule_records
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.singleBond_reference_populations
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReferenceSelectionBoundary.singleBond_reference_discrepancy
