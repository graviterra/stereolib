import TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Actual witness labels below an arbitrary carrier target are optional raw fact labels at
their complete original-root histories. The existing target history is prepended to each
residual witness; the reader is not silently replaced by a freshly rooted reader.

Root identity, strict dependency, provenance and terminal-unit correspondence follow from
the actual carrier and boundary payload. No successful label, fact lookup, execution, or
history independence is assumed. The original root-only interface remains unchanged.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedStateReader LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingWitnessLabelMatch LocalizedChemicalRingWitnessFactMatch

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- The path after the original root, including the target's existing root-first prefix. -/
def boundaryPath (target : input.LocalizedCIPOccurrence carrierFuel) (p : List input.Atom) :
    List input.Atom := target.1.node.history.reverse.tail ++ p

/-- Actual carrier history identifies the original root at the head of the boundary. -/
theorem root_cons_boundaryPath (single : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedCIPOccurrence carrierFuel) (p : List input.Atom) :
    target.1.root :: boundaryPath target p = target.1.node.history.reverse ++ p := by
  have head : target.1.node.history.reverse.head? = some target.1.root := by
    rw [List.head?_reverse]
    exact input.carrierOccurrence_history_getLast_eq_root single target
  have initialPath : target.1.root :: target.1.node.history.reverse.tail =
      target.1.node.history.reverse := List.cons_head?_tail (by simpa only [Option.mem_def] using head)
  exact congrArg (fun xs => xs ++ p) initialPath

theorem boundaryPath_length (single : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedCIPOccurrence carrierFuel) (p : List input.Atom) :
    (boundaryPath target p).length + 1 = target.1.node.history.length + p.length := by
  have length := congrArg List.length (root_cons_boundaryPath single target p)
  simpa only [List.length_cons, List.length_append, List.length_reverse] using length

/-- The full raw history is the new witness in reverse, followed by the unchanged target
history. This is the exact history used by the existing fact lookup and execution bridges. -/
theorem boundaryPath_raw_history (single : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedCIPOccurrence carrierFuel) (p : List input.Atom) :
    (rawPathNode target.1.root (boundaryPath target p)).history =
      (p.reverse ++ target.1.node.history).map Fin.val := by
  change (target.1.root :: boundaryPath target p).reverse.map Fin.val = _
  rw [root_cons_boundaryPath single target p, List.reverse_append, List.reverse_reverse]

/-- A permutation fixing the boundary acts only on the appended residual witness. -/
theorem boundaryPath_map (target : input.LocalizedCIPOccurrence carrierFuel)
    (π : Equiv.Perm input.Atom)
    (fixed : ∀ atom ∈ target.1.node.history.reverse, π atom = atom) (p : List input.Atom) :
    (boundaryPath target p).map π = boundaryPath target (p.map π) := by
  have initialPath : target.1.node.history.reverse.tail.map π = target.1.node.history.reverse.tail := by
    calc
      _ = target.1.node.history.reverse.tail.map id := List.map_congr_left fun atom member =>
        fixed atom (List.mem_of_mem_tail member)
      _ = _ := List.map_id _
  simp only [boundaryPath, List.map_append, initialPath]

private theorem occurrence_history_length (target : input.LocalizedCIPOccurrence carrierFuel) :
    target.1.node.history.length = target.1.address.length + 1 := by
  have derived : input.DeclarativeLocalizedOccurrenceSubtree target.1.root []
      (carrierFuel + 1) (OfficialCIPNode.root target.1.root) target.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  exact input.declarativeLocalizedOccurrenceSubtree_history_length derived rfl

/-- A nonempty witness beneath the actual history boundary is a strict real dependency of
that target. Its molecular unit still uses the original root and the entire extended path. -/
theorem extended_payload_facts (single : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) (p : List input.Atom)
    (terminal : input.Atom) (last : p.getLast? = some terminal)
    (payload : cursor.occurrence.1.node = boundaryNode target.1.node.history.reverse p) :
    input.LocalizedDepthDependency cursor.occurrence target ∧
      cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      (input.molecularFrameUnit cursor.occurrence.1).atom = terminal := by
  have carrierLast := input.carrierOccurrence_history_getLast_eq_root single cursor.occurrence
  have boundaryLast : cursor.occurrence.1.node.history.getLast? = some target.1.root := by
    rw [payload, boundaryNode_history, ← root_cons_boundaryPath single target p,
      List.getLast?_reverse, List.head?_cons]
  have sourceRoot : cursor.occurrence.1.root = target.1.root :=
    Option.some.inj (carrierLast.symm.trans boundaryLast)
  have targetLength := occurrence_history_length target
  have cursorLength := occurrence_history_length cursor.occurrence
  rw [payload, boundaryNode_history] at cursorLength
  simp only [List.length_reverse, List.length_append] at cursorLength
  have nonempty : p ≠ [] := by
    intro empty
    rw [empty] at last
    cases last
  have positive : 0 < p.length := by
    cases p with
    | nil => exact False.elim (nonempty rfl)
    | cons head tail => simp
  have unit : input.molecularFrameUnit cursor.occurrence.1 =
      (⟨target.1.root, boundaryPath target p⟩ : OccurrenceUnit input.Atom) := by
    simp only [molecularFrameUnit, sourceRoot, payload, boundaryNode_history, List.reverse_reverse]
    rw [← root_cons_boundaryPath single target p]
    rfl
  refine ⟨⟨sourceRoot, by omega⟩, ?_, ?_⟩
  · rw [payload]
    rfl
  · rw [unit]
    change (boundaryPath target p).getLast?.getD target.1.root = terminal
    unfold boundaryPath
    rw [List.getLast?_append_of_ne_nil _ nonempty, last]
    rfl

/-- The actual target reader at a detected witness terminal is its exact optional raw fact
label. Dependency, reality and detected-unit identification are derived from the payload. -/
theorem reader_eq_extended_path_fact (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) (p : List input.Atom)
    (terminal : input.Atom) (last : p.getLast? = some terminal)
    (detected : IsDetectedCenter input.moleculeGraph terminal)
    (payload : cursor.occurrence.1.node = boundaryNode target.1.node.history.reverse p) :
    rawStateReader input state target cursor =
      (state.factAt? (rawPathNode target.1.root (boundaryPath target p))).map factLabel := by
  obtain ⟨dependency, real, atom⟩ := extended_payload_facts single target cursor p terminal last payload
  apply rawStateReader_eq_factAt?_label input single state target cursor dependency real
    (by rw [atom]; exact detected) (rawPathNode target.1.root (boundaryPath target p))
  · rw [boundaryPath_raw_history single target p, payload, boundaryNode_history,
      List.reverse_append, List.reverse_reverse]
  · rfl

/-- Actual matched labels on the SAME boundary witness correspondence give optional fact
label equality at the complete original-root histories. Neither optional label need exist. -/
theorem fact_labels_eq_of_boundary_pathLabelsAgree (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence carrierFuel)
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (p q : List input.Atom) (nonemptyP : p ≠ []) (nonemptyQ : q ≠ [])
    (detectedP : IsDetectedCenter input.moleculeGraph (pathTerminal p nonemptyP))
    (detectedQ : IsDetectedCenter input.moleculeGraph (pathTerminal q nonemptyQ))
    (matched : PathLabelsAgree treeL treeR
      (rawStateReader input state target) (rawStateReader input state target)
      target.1.node.history.reverse p q) :
    (state.factAt? (rawPathNode target.1.root (boundaryPath target p))).map factLabel =
      (state.factAt? (rawPathNode target.1.root (boundaryPath target q))).map factLabel := by
  obtain ⟨x, y, payloadL, payloadR, labels⟩ := matched
  have readL := reader_eq_extended_path_fact single state target (nodeSource input treeL x)
    p (pathTerminal p nonemptyP) (List.getLast?_eq_some_getLast nonemptyP) detectedP payloadL
  have readR := reader_eq_extended_path_fact single state target (nodeSource input treeR y)
    q (pathTerminal q nonemptyQ) (List.getLast?_eq_some_getLast nonemptyQ) detectedQ payloadR
  exact readL.symm.trans (labels.trans readR)

end TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch.boundaryPath
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch.root_cons_boundaryPath
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch.boundaryPath_length
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch.boundaryPath_raw_history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch.boundaryPath_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch.extended_payload_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch.reader_eq_extended_path_fact
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch.fact_labels_eq_of_boundary_pathLabelsAgree
