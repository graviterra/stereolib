import TetraStereo.OneCenter.LocalizedChemicalRingWitnessLabelMatch
import TetraStereo.OneCenter.LocalizedAcyclicCarrierInjectivity
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Matching witness readers at an original root match the optional labels stored at their
exact raw occurrence histories. Strict dependency, real provenance, and the detected carrier
unit are derived from the boundary payload. Neither generated descriptor correctness nor
independence from the occurrence history is assumed or concluded. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedStateReader LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingWitnessLabelMatch

/-- The real raw node of a root-first path, with the current atom first in its stored history.
The empty-path defaults make the definition total; readback below uses nonempty paths. -/
def rawPathNode {n : Nat} (root : Fin n) (path : List (Fin n)) :
    RawMolecule.CanonicalBranchNode where
  atom := (path.getLast?.getD root).val
  parent := (path.dropLast.getLast?.getD root).val
  history := (root :: path).reverse.map Fin.val
  provenance := .realAtom

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- An actual carrier with a nonempty root-boundary payload is a strict real dependency,
and its molecular unit identifies the path's actual terminal atom. No acyclicity is used. -/
theorem root_payload_facts (single : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedCIPOccurrence carrierFuel) (rootAddress : target.1.address = [])
    (cursor : input.LocalizedRerootCursor carrierFuel) (path : List input.Atom)
    (terminal : input.Atom) (last : path.getLast? = some terminal)
    (payload : cursor.occurrence.1.node = boundaryNode [target.1.root] path) :
    input.LocalizedDepthDependency cursor.occurrence target ∧
      cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      (input.molecularFrameUnit cursor.occurrence.1).atom = terminal := by
  have carrierLast := input.carrierOccurrence_history_getLast_eq_root single cursor.occurrence
  have boundaryLast : cursor.occurrence.1.node.history.getLast? = some target.1.root := by
    simp only [payload, boundaryNode_history, List.singleton_append, List.getLast?_reverse,
      List.head?_cons]
  have sourceRoot : cursor.occurrence.1.root = target.1.root :=
    Option.some.inj (carrierLast.symm.trans boundaryLast)
  have derived : input.DeclarativeLocalizedOccurrenceSubtree cursor.occurrence.1.root []
      (carrierFuel + 1) (OfficialCIPNode.root cursor.occurrence.1.root) cursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp cursor.occurrence.2
  have aligned : (OfficialCIPNode.root cursor.occurrence.1.root).history.length =
      ([] : List Nat).length + 1 := rfl
  have historyLength := input.declarativeLocalizedOccurrenceSubtree_history_length derived aligned
  rw [payload, boundaryNode_history] at historyLength
  simp only [List.singleton_append, List.length_reverse, List.length_cons] at historyLength
  have addressLength : cursor.occurrence.1.address.length = path.length := by omega
  have positive : 0 < path.length := by
    cases path with
    | nil => simp at last
    | cons _ _ => simp
  have unit : input.molecularFrameUnit cursor.occurrence.1 =
      (⟨target.1.root, path⟩ : OccurrenceUnit input.Atom) := by
    simp only [molecularFrameUnit, sourceRoot, payload, boundaryNode,
      List.singleton_append, List.reverse_reverse, List.tail_cons]
  refine ⟨⟨sourceRoot, ?_⟩, ?_, ?_⟩
  · simpa only [rootAddress, List.length_nil, addressLength] using positive
  · rw [payload]
    rfl
  · rw [unit]
    change path.getLast?.getD target.1.root = terminal
    rw [last]
    rfl

/-- At a detected terminal, the root reader is exactly the raw fact-label lookup of the
witness history. All dependency, provenance, and carrier-unit side conditions are derived. -/
theorem reader_eq_path_fact (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = []) (cursor : input.LocalizedRerootCursor carrierFuel)
    (path : List input.Atom) (terminal : input.Atom) (last : path.getLast? = some terminal)
    (detected : IsDetectedCenter input.moleculeGraph terminal)
    (payload : cursor.occurrence.1.node = boundaryNode [target.1.root] path) :
    rawStateReader input state target cursor =
      (state.factAt? (rawPathNode target.1.root path)).map factLabel := by
  obtain ⟨dependency, real, atom⟩ :=
    root_payload_facts single target rootAddress cursor path terminal last payload
  apply rawStateReader_eq_factAt?_label input single state target cursor dependency real
    (by rw [atom]; exact detected) (rawPathNode target.1.root path)
  · simp only [rawPathNode, payload, boundaryNode_history, List.singleton_append]
  · rfl

/-- The accepted occurrence-level label correspondence gives exact optional fact-label
equality at the two history-defined raw nodes. Missing facts remain missing facts; no label
existence or descriptor execution result is asserted. -/
theorem fact_labels_eq_of_pathLabelsAgree (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (p q : List input.Atom) (nonemptyP : p ≠ []) (nonemptyQ : q ≠ [])
    (detectedP : IsDetectedCenter input.moleculeGraph (pathTerminal p nonemptyP))
    (detectedQ : IsDetectedCenter input.moleculeGraph (pathTerminal q nonemptyQ))
    (matched : PathLabelsAgree treeL treeR
      (rawStateReader input state target) (rawStateReader input state target) [target.1.root] p q) :
    (state.factAt? (rawPathNode target.1.root p)).map factLabel =
      (state.factAt? (rawPathNode target.1.root q)).map factLabel := by
  obtain ⟨x, y, payloadL, payloadR, labels⟩ := matched
  have readL := reader_eq_path_fact single state target rootAddress (nodeSource input treeL x)
    p (pathTerminal p nonemptyP) (List.getLast?_eq_some_getLast nonemptyP) detectedP payloadL
  have readR := reader_eq_path_fact single state target rootAddress (nodeSource input treeR y)
    q (pathTerminal q nonemptyQ) (List.getLast?_eq_some_getLast nonemptyQ) detectedQ payloadR
  exact readL.symm.trans (labels.trans readR)

end TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch.rawPathNode
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch.root_payload_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch.reader_eq_path_fact
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch.fact_labels_eq_of_pathLabelsAgree
