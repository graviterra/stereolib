import TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport
import TetraStereo.OneCenter.LocalizedMarkedGeneratedSnapshotSupport
import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! A stored generated label is an actual recursive descriptor computation at a determined
remaining depth. The proof retains the full occurrence history and the inherited context.
It works for the shared recursion of the immediate and distant-reference evaluators, without
assuming chemical correctness or replacing a recorded label by an oracle. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingGeneratedLabelExecution

open LocalizedChemicalRingSenseTransport
open LocalizedMarkedOperationEvaluator (Operations underWith mem_tiedChildren_actual)
open LocalizedMarkedTerminalReferenceScope (Descends StrictDescendant descendant_reached)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)
open LocalizedMarkedGeneratedFactUniqueness (factOf_key)
open LocalizedMarkedRetainedStateReader (factLabel factLabel_factOf)
open LocalizedGenericMarkedRecalculation (Geometry factOf)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Exact fuel accounting for every fact emitted by the actual shared recursion. -/
theorem factsWith_source_budget (step : Step) (mol : RawMolecule) (ops : Operations) (depth : Nat) :
    ∀ geom state ctx source fact,
      fact ∈ factsWith step mol ops depth geom state ctx source →
      ∃ target label remaining, Descends mol source target ∧
        remaining + target.history.length + 1 = depth + source.history.length ∧
        descriptorWith step mol ops remaining geom state ctx target = some label ∧
        fact = factOf target label := by
  induction depth with
  | zero => simp [factsWith]
  | succ depth ih =>
      intro geom state ctx source fact member
      rw [factsWith_succ] at member
      rcases List.mem_append.mp member with own | descendant
      · obtain ⟨label, present, rfl⟩ := List.mem_map.mp own
        exact ⟨source, label, depth, .refl, by omega, Option.mem_toList.mp present, rfl⟩
      · obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp descendant
        obtain ⟨target, label, remaining, path, budget, computed, value⟩ :=
          ih geom state ctx child fact member
        have growth := congrArg List.length (mol.canonicalChildren_history source child edge)
        simp only [List.length_cons] at growth
        exact ⟨target, label, remaining, (Relation.ReflTransGen.single edge).trans path,
          by omega, computed, value⟩

/-- A promotion snapshot uses the same inherited reference at every emitted occurrence;
its remaining descriptor depth is fixed by the difference of actual history lengths. -/
theorem snapshot_source_budget (step : Step) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source : Node) (mark : Nat)
    (fact : OccurrenceAuxFact)
    (member : fact ∈ underWith mol ops geom state source (factsWith step mol ops depth) mark) :
    ∃ target label remaining, StrictDescendant mol source target ∧
      remaining + target.history.length = depth + source.history.length ∧
      descriptorWith step mol ops remaining geom state (some mark) target = some label ∧
      fact = factOf target label := by
  obtain ⟨child, selected, member⟩ := List.mem_flatMap.mp member
  have edge := mem_tiedChildren_actual mol ops state source child selected
  obtain ⟨target, label, remaining, path, budget, computed, value⟩ :=
    factsWith_source_budget step mol ops depth geom state (some mark) child fact member
  have growth := congrArg List.length (mol.canonicalChildren_history source child edge)
  simp only [List.length_cons] at growth
  exact ⟨target, label, remaining, ⟨child, edge, path⟩, by omega, computed, value⟩

/-- Readback of a successful snapshot lookup as the actual descriptor execution. The query
is identified by its full key among reached occurrences; its atom and parent are not assumed
to be supplied correctly by an arbitrary fact record. -/
theorem snapshot_label_execution (step : Step) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source : Node)
    (sourceReached : Reached mol source) (mark : Nat) (query : Node)
    (queryReached : Reached mol query) (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
      query).map factLabel = some label) :
    descriptorWith step mol ops (depth + source.history.length - query.history.length)
      geom state (some mark) query = some label := by
  obtain ⟨fact, lookup, factValue⟩ := Option.map_eq_some_iff.mp observed
  have key : fact.key = canonicalOccurrenceKey query := by
    simpa only [beq_iff_eq] using List.find?_some lookup
  obtain ⟨target, ownLabel, remaining, path, budget, computed, value⟩ :=
    snapshot_source_budget step mol ops depth geom state source mark fact (List.mem_of_find?_eq_some lookup)
  have targetReached : Reached mol target := by
    obtain ⟨child, edge, rest⟩ := path
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  obtain ⟨targetRoot, _, targetPath⟩ := targetReached
  obtain ⟨queryRoot, _, queryPath⟩ := queryReached
  rw [value, factOf_key] at key
  have same : target = query := LocalizedMarkedTerminalGaugeRefusal.generated_eq_of_key
    (generated_of_reachedFrom mol targetRoot target targetPath)
    (generated_of_reachedFrom mol queryRoot query queryPath) key
  subst target
  rw [value, factLabel_factOf] at factValue
  subst ownLabel
  have remainingEq : remaining = depth + source.history.length - query.history.length := by omega
  simpa only [remainingEq] using computed

/-- Matched successful recorded labels at equal-depth histories are executions at one and
the same recursive budget and inherited context. This supplies the execution premise of the
physical decoder, but does not assert agreement of its descendant fact lists. -/
theorem matched_snapshot_labels_execute (step : Step) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source : Node)
    (sourceReached : Reached mol source) (mark : Nat) (left right : Node)
    (leftReached : Reached mol left) (rightReached : Reached mol right)
    (sameDepth : left.history.length = right.history.length)
    (matched : ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
      left).map factLabel =
      ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt? right).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
      left).map factLabel = some label) :
    let remaining := depth + source.history.length - left.history.length
    descriptorWith step mol ops remaining geom state (some mark) left = some label ∧
      descriptorWith step mol ops remaining geom state (some mark) right = some label := by
  refine ⟨snapshot_label_execution step mol ops depth geom state source sourceReached mark
    left leftReached label observed, ?_⟩
  have rightObserved := matched.symm.trans observed
  simpa only [sameDepth] using snapshot_label_execution step mol ops depth geom state source
    sourceReached mark right rightReached label rightObserved

end TetraStereo.OneCenter.LocalizedChemicalRingGeneratedLabelExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingGeneratedLabelExecution.factsWith_source_budget
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingGeneratedLabelExecution.snapshot_source_budget
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingGeneratedLabelExecution.snapshot_label_execution
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingGeneratedLabelExecution.matched_snapshot_labels_execute
