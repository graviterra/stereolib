import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessExecution
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
A promotion snapshot selects its first child through `tiedChildren`. Its shared `factsWith`
recursion then enumerates ALL canonical descendants, even below a node whose descriptor
refuses. An actual selected first child, raw descent and sufficient history budget therefore
make a missing stored fact an actual descriptor refusal at the uniquely determined depth.

No state uniqueness, physical correctness, or successful-label premise is needed for the
absence-to-refusal endpoint. Selection and sufficient depth are explicit structural premises;
carrier membership alone is not substituted for actual execution selection.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingBoundaryWitnessExecution (snapshotWith)
open LocalizedMarkedOperationEvaluator (Operations tiedChildren underWith mem_tiedChildren_actual)
open LocalizedMarkedTerminalReferenceScope (Descends)
open LocalizedMarkedGeneratedFactUniqueness (factOf_key)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (Geometry factOf)

abbrev Node := RawMolecule.CanonicalBranchNode

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
theorem factsWith_contains (step : Step) (mol : RawMolecule) (ops : Operations) (depth : Nat) :
    ∀ geom state ctx source query remaining label,
      Descends mol source query →
      remaining + query.history.length + 1 = depth + source.history.length →
      descriptorWith step mol ops remaining geom state ctx query = some label →
      factOf query label ∈ factsWith step mol ops depth geom state ctx source := by
  induction depth with
  | zero =>
      intro geom state ctx source query remaining label path budget _
      have monotone := history_length_le path
      omega
  | succ depth ih =>
      intro geom state ctx source query remaining label path budget computed
      rw [factsWith_succ]
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

/-- Only the first edge must be selected by the current snapshot. All subsequent edges
are the actual canonical-child relation; their history growth fixes the execution depth. -/
theorem underWith_contains (step : Step) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (source child query : Node) (mark : Nat)
    (selected : child ∈ tiedChildren mol ops state source)
    (path : Descends mol child query)
    (adequate : query.history.length ≤ depth + source.history.length)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (computed : descriptorWith step mol ops (depth + source.history.length - query.history.length)
      geom state (some mark) query = some label) :
    factOf query label ∈ underWith mol ops geom state source (factsWith step mol ops depth) mark := by
  have edge := mem_tiedChildren_actual mol ops state source child selected
  have growth := congrArg List.length (mol.canonicalChildren_history source child edge)
  simp only [List.length_cons] at growth
  have budget : (depth + source.history.length - query.history.length) + query.history.length + 1 =
      depth + child.history.length := by omega
  exact List.mem_flatMap.mpr ⟨child, selected,
    factsWith_contains step mol ops depth geom state (some mark) child query _ label path budget computed⟩

/-- Absence is a genuine refusal once the actual selected path and its budget are known.
No uniqueness of the generated state is needed: any emitted matching key contradicts absence. -/
theorem underWith_absence_refusal (step : Step) (mol : RawMolecule) (ops : Operations)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (source child query : Node) (mark : Nat)
    (selected : child ∈ tiedChildren mol ops state source)
    (path : Descends mol child query)
    (adequate : query.history.length ≤ depth + source.history.length)
    (absent : ((underWith mol ops geom state source (factsWith step mol ops depth) mark).factAt?
      query).map factLabel = none) :
    descriptorWith step mol ops (depth + source.history.length - query.history.length)
      geom state (some mark) query = none := by
  cases computed : descriptorWith step mol ops (depth + source.history.length - query.history.length)
      geom state (some mark) query with
  | none => rfl
  | some label =>
      have emitted := underWith_contains step mol ops depth geom state source child query mark
        selected path adequate label computed
      have lookup := Option.map_eq_none_iff.mp absent
      have impossible := (List.find?_eq_none.mp lookup) (factOf query label) emitted
      simp [factOf_key] at impossible

/-- Membership in the actual sparse-operation snapshot, with empty initial state. -/
theorem snapshot_contains (step : Step) (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (source child query : Node) (mark : Nat)
    (selected : child ∈ tiedChildren mol (sparseOperations input mol) [] source)
    (path : Descends mol child query)
    (adequate : query.history.length ≤ depth + source.history.length)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (computed : descriptorWith step mol (sparseOperations input mol)
      (depth + source.history.length - query.history.length) geom [] (some mark) query = some label) :
    factOf query label ∈ snapshotWith step input mol depth geom source mark :=
  underWith_contains step mol (sparseOperations input mol) depth geom [] source child query mark
    selected path adequate label computed

/-- Actual snapshot absence implies the actual descriptor's refusal, at its exact remaining
depth and inherited reference. This is the execution consumer of a missing matched witness. -/
theorem snapshot_absence_refusal (step : Step) (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (source child query : Node) (mark : Nat)
    (selected : child ∈ tiedChildren mol (sparseOperations input mol) [] source)
    (path : Descends mol child query)
    (adequate : query.history.length ≤ depth + source.history.length)
    (absent : ((snapshotWith step input mol depth geom source mark).factAt? query).map factLabel = none) :
    descriptorWith step mol (sparseOperations input mol)
      (depth + source.history.length - query.history.length) geom [] (some mark) query = none :=
  underWith_absence_refusal step mol (sparseOperations input mol) depth geom [] source child query mark
    selected path adequate absent

/-- Specialization to the isolated inherited-reference fallback, with no change to the
production default or to the selected first child. -/
theorem candidate_absence_refusal (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (depth : Nat) (geom : Geometry) (source child query : Node) (mark : Nat)
    (selected : child ∈ tiedChildren mol (sparseOperations input mol) [] source)
    (path : Descends mol child query)
    (adequate : query.history.length ≤ depth + source.history.length)
    (absent : ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol depth geom
      source mark).factAt? query).map factLabel = none) :
    LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      (depth + source.history.length - query.history.length) geom [] (some mark) query = none :=
  snapshot_absence_refusal LocalizedChemicalRingInheritedFallback.rawStep? input mol depth geom
    source child query mark selected path adequate absent

end TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness.factsWith_contains
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness.underWith_contains
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness.underWith_absence_refusal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness.snapshot_contains
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness.snapshot_absence_refusal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
