import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution
import TetraStereo.OneCenter.LocalizedChemicalRingGeneratedLabelExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-!
# Exact generated-label execution for prepared contexts

Every stored label is an actual recursive descriptor at the depth determined by its full
history. Conversely, every successful descriptor along an actual canonical descent is emitted
when the budget reaches that occurrence. Thus a prepared snapshot's optional label equals the
actual descriptor, including absence/refusal, without assuming chemical correctness or a desired
label. All canonical first children are included; no selected-first-edge premise remains.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedMarkedTerminalReferenceScope (Descends StrictDescendant descendant_reached)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)
open LocalizedMarkedGeneratedFactUniqueness (factOf_key)
open LocalizedMarkedRetainedStateReader (factLabel factLabel_factOf)
open LocalizedGenericMarkedRecalculation (Geometry factOf)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Exact fuel accounting for every fact emitted by the actual shared recursion. -/
theorem factsOfStep_source_budget (step : PreparedStep) (mol : RawMolecule) (depth : Nat) :
    ∀ geom state ctx source fact,
      fact ∈ factsOfStep step mol depth geom state ctx source →
      ∃ target label remaining, Descends mol source target ∧
        remaining + target.history.length + 1 = depth + source.history.length ∧
        descriptorOfStep step mol remaining geom state ctx target = some label ∧
        fact = factOf target label := by
  induction depth with
  | zero => simp [factsOfStep]
  | succ depth ih =>
      intro geom state ctx source fact member
      rw [factsOfStep_succ] at member
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


private theorem history_length_le {mol : RawMolecule} {source query : Node}
    (path : Descends mol source query) : source.history.length ≤ query.history.length := by
  induction path with
  | refl => exact le_rfl
  | tail path edge ih =>
      have growth := congrArg List.length (mol.canonicalChildren_history _ _ edge)
      simp only [List.length_cons] at growth
      omega

/-- Converse of generated-fact execution: a successful descriptor at the exact residual
budget is emitted along every actual canonical descent in this forest. -/
theorem factsOfStep_contains (step : PreparedStep) (mol : RawMolecule) (depth : Nat) :
    ∀ geom state ctx source query remaining label,
      Descends mol source query →
      remaining + query.history.length + 1 = depth + source.history.length →
      descriptorOfStep step mol remaining geom state ctx query = some label →
      factOf query label ∈ factsOfStep step mol depth geom state ctx source := by
  induction depth with
  | zero =>
      intro geom state ctx source query remaining label path budget _
      have monotone := history_length_le path
      omega
  | succ depth ih =>
      intro geom state ctx source query remaining label path budget computed
      rw [factsOfStep_succ]
      rcases path.cases_head with same | ⟨child, edge, rest⟩
      · subst query
        have sameDepth : remaining = depth := by omega
        subst remaining
        exact List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨label, Option.mem_toList.mpr computed, rfl⟩))
      · have growth := congrArg List.length (mol.canonicalChildren_history source child edge)
        simp only [List.length_cons] at growth
        have childBudget : remaining + query.history.length + 1 = depth + child.history.length := by
          omega
        exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨child, edge, ih geom state ctx child query remaining label rest childBudget computed⟩))

/-- All-child snapshots retain exact descriptor-depth accounting and the same list context. -/
theorem snapshot_source_budget (step : PreparedStep) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source : Node) (M : MarkContext)
    (fact : OccurrenceAuxFact)
    (member : fact ∈ childrenUnder mol (factsOfStep step mol depth) geom state source M) :
    ∃ target label remaining, StrictDescendant mol source target ∧
      remaining + target.history.length = depth + source.history.length ∧
      descriptorOfStep step mol remaining geom state M target = some label ∧
      fact = factOf target label := by
  obtain ⟨child, edge, member⟩ := List.mem_flatMap.mp member
  obtain ⟨target, label, remaining, path, budget, computed, value⟩ :=
    factsOfStep_source_budget step mol depth geom state M child fact member
  have growth := congrArg List.length (mol.canonicalChildren_history source child edge)
  simp only [List.length_cons] at growth
  exact ⟨target, label, remaining, ⟨child, edge, path⟩, by omega, computed, value⟩

/-- Successful execution at a strict descendant is emitted at the exact residual budget. -/
theorem snapshot_contains (step : PreparedStep) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source query : Node) (M : MarkContext)
    (path : StrictDescendant mol source query)
    (adequate : query.history.length ≤ depth + source.history.length)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (computed : descriptorOfStep step mol (depth + source.history.length - query.history.length)
      geom state M query = some label) :
    factOf query label ∈ childrenUnder mol (factsOfStep step mol depth) geom state source M := by
  obtain ⟨child, edge, rest⟩ := path
  have growth := congrArg List.length (mol.canonicalChildren_history source child edge)
  simp only [List.length_cons] at growth
  have budget : (depth + source.history.length - query.history.length) + query.history.length + 1 =
      depth + child.history.length := by omega
  exact List.mem_flatMap.mpr ⟨child, edge,
    factsOfStep_contains step mol depth geom state M child query _ label rest budget computed⟩

/-- A missing stored label is an actual refusal, once the concrete path and budget are given. -/
theorem snapshot_absence_refusal (step : PreparedStep) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source query : Node) (M : MarkContext)
    (path : StrictDescendant mol source query)
    (adequate : query.history.length ≤ depth + source.history.length)
    (absent : ((childrenUnder mol (factsOfStep step mol depth) geom state source M).factAt?
      query).map factLabel = none) :
    descriptorOfStep step mol (depth + source.history.length - query.history.length)
      geom state M query = none := by
  cases computed : descriptorOfStep step mol (depth + source.history.length - query.history.length)
      geom state M query with
  | none => rfl
  | some label =>
      have emitted := snapshot_contains step mol depth geom state source query M path adequate label computed
      have lookup := Option.map_eq_none_iff.mp absent
      have impossible := (List.find?_eq_none.mp lookup) (factOf query label) emitted
      simp [factOf_key] at impossible

/-- Readback of a successful snapshot lookup as the actual descriptor execution. The query
is identified by its full key among reached occurrences; its atom and parent are not assumed
to be supplied correctly by an arbitrary fact record. -/
theorem snapshot_label_execution (step : PreparedStep) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source : Node)
    (sourceReached : Reached mol source) (M : MarkContext) (query : Node)
    (queryReached : Reached mol query) (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((childrenUnder mol (factsOfStep step mol depth) geom state source M).factAt?
      query).map factLabel = some label) :
    descriptorOfStep step mol (depth + source.history.length - query.history.length)
      geom state M query = some label := by
  obtain ⟨fact, lookup, factValue⟩ := Option.map_eq_some_iff.mp observed
  have key : fact.key = canonicalOccurrenceKey query := by
    simpa only [beq_iff_eq] using List.find?_some lookup
  obtain ⟨target, ownLabel, remaining, path, budget, computed, value⟩ :=
    snapshot_source_budget step mol depth geom state source M fact (List.mem_of_find?_eq_some lookup)
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

/-- Exact optional label execution, covering both stored labels and genuine refusals. -/
theorem snapshot_label_eq_descriptor (step : PreparedStep) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source query : Node) (M : MarkContext)
    (sourceReached : Reached mol source) (path : StrictDescendant mol source query)
    (adequate : query.history.length ≤ depth + source.history.length) :
    ((childrenUnder mol (factsOfStep step mol depth) geom state source M).factAt? query).map factLabel =
      descriptorOfStep step mol (depth + source.history.length - query.history.length)
        geom state M query := by
  have queryReached : Reached mol query := by
    obtain ⟨child, edge, rest⟩ := path
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  cases observed : ((childrenUnder mol (factsOfStep step mol depth) geom state source M).factAt?
      query).map factLabel with
  | none => exact (snapshot_absence_refusal step mol depth geom state source query M path adequate observed).symm
  | some label => exact (snapshot_label_execution step mol depth geom state source sourceReached M
      query queryReached label observed).symm

/-- The actual joint evaluator reads precisely the recursive result at the query's history,
with the same full inherited context and a derived residual depth. -/
theorem generated_label_eq_descriptor (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (source query : Node) (references : List input.Atom)
    (sourceReached : Reached mol source) (path : StrictDescendant mol source query)
    (adequate : query.history.length ≤ depth + source.history.length) :
    ((generated input mol depth geom source references).factAt? query).map factLabel =
      preparedDescriptor? mol (jointOperations input mol)
        (depth + source.history.length - query.history.length) geom [] (references.map Fin.val) query :=
  snapshot_label_eq_descriptor (rawStepPrepared? (jointOperations input mol)) mol depth geom []
    source query (references.map Fin.val) sourceReached path adequate

/-- The descriptor read from a strict descendant uses a strictly smaller recursion budget. -/
theorem residual_depth_lt {mol : RawMolecule} {source query : Node} (depth : Nat)
    (path : StrictDescendant mol source query)
    (adequate : query.history.length ≤ depth + source.history.length) :
    depth + source.history.length - query.history.length < depth := by
  obtain ⟨child, edge, rest⟩ := path
  have growth := congrArg List.length (mol.canonicalChildren_history source child edge)
  simp only [List.length_cons] at growth
  have monotone := history_length_le rest
  omega

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.factsOfStep_source_budget
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.factsOfStep_contains
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.snapshot_source_budget
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.snapshot_contains
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.snapshot_absence_refusal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.snapshot_label_execution
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.snapshot_label_eq_descriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.generated_label_eq_descriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution.residual_depth_lt
