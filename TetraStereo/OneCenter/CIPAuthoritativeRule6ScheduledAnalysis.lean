import TetraStereo.OneCenter.CIPAuthoritativeRule6Scheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler

open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open ProductionCIPOccurrenceDiscovery
open AuthoritativeCIPRule6P92Enumeration

/-!
# Public exact-once analysis for the authoritative Rule-6 scheduler

The uncapped authoritative evaluator already has a unique complete occurrence model.  This module
closes its final assembly seam: the decoded model is projected over every molecule-derived final
root exactly once, and every public member retains either an ordinary certified derivation or the
exact authoritative P-92 Rule-6 branch judgment.
-/

/-- The concrete unique state computed by the dependency-ready authoritative scheduler. -/
noncomputable def authoritativeSolvedState {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat) : State discovery :=
  OccurrenceScheduler.decode (authoritativeOccurrenceSystem discovery fuel)
    (@DepthDependency mol discovery)
    (OccurrenceScheduler.closure (authoritativeOccurrenceSystem discovery fuel)
      (@DepthDependency mol discovery))

/-- The concrete state is a complete authoritative occurrence model. -/
theorem authoritativeSolvedState_cipModel {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat) :
    (authoritativeOccurrenceSystem discovery fuel).CIPModel
      (authoritativeSolvedState discovery fuel) := by
  exact authoritativeSchedulerClosure_cipModel discovery fuel

/-- One final public assignment retains its exact molecule-derived unit and solved label. -/
structure AuthoritativeScheduledAssignment {mol : RawMolecule}
    (discovery : Discovery mol) where
  unit : FinalUnit mol
  label : Label discovery

/-- Project one final occurrence from any total occurrence state. -/
def authoritativeScheduledAssignmentAt? {mol : RawMolecule}
    (discovery : Discovery mol) (state : State discovery)
    (unit : FinalUnit mol) : Option (AuthoritativeScheduledAssignment discovery) :=
  match state (finalOccurrence discovery unit) with
  | none => none
  | some label => some { unit, label }

/-- A successful local projection retains exactly the requested physical final unit. -/
theorem authoritativeScheduledAssignmentAt?_unit {mol : RawMolecule}
    (discovery : Discovery mol) (state : State discovery)
    (unit : FinalUnit mol) (assignment : AuthoritativeScheduledAssignment discovery)
    (computed : authoritativeScheduledAssignmentAt? discovery state unit = some assignment) :
    assignment.unit = unit := by
  unfold authoritativeScheduledAssignmentAt? at computed
  cases stateEq : state (finalOccurrence discovery unit) with
  | none => simp [stateEq] at computed
  | some label =>
      simp [stateEq] at computed
      subst assignment
      rfl

/-- A successful local projection is exactly a solved-state label at that final occurrence. -/
theorem authoritativeScheduledAssignmentAt?_label {mol : RawMolecule}
    (discovery : Discovery mol) (state : State discovery)
    (unit : FinalUnit mol) (assignment : AuthoritativeScheduledAssignment discovery)
    (computed : authoritativeScheduledAssignmentAt? discovery state unit = some assignment) :
    state (finalOccurrence discovery unit) = some assignment.label := by
  unfold authoritativeScheduledAssignmentAt? at computed
  cases stateEq : state (finalOccurrence discovery unit) with
  | none => simp [stateEq] at computed
  | some label =>
      simp [stateEq] at computed
      subst assignment
      rfl

/-- Public authoritative final assignments, in canonical molecule-root order. -/
noncomputable def analyzeAuthoritativeScheduledTetrahedral {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat) :
    List (AuthoritativeScheduledAssignment discovery) :=
  (allRoots mol).filterMap
    (authoritativeScheduledAssignmentAt? discovery
      (authoritativeSolvedState discovery fuel))

/-- Public membership is exactly the local solved-state projection at the retained unit. -/
theorem mem_analyzeAuthoritativeScheduledTetrahedral_iff {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat)
    (assignment : AuthoritativeScheduledAssignment discovery) :
    assignment ∈ analyzeAuthoritativeScheduledTetrahedral discovery fuel ↔
      authoritativeScheduledAssignmentAt? discovery
        (authoritativeSolvedState discovery fuel) assignment.unit = some assignment := by
  classical
  constructor
  · intro present
    rw [analyzeAuthoritativeScheduledTetrahedral, List.mem_filterMap] at present
    obtain ⟨unit, _unitPresent, emitted⟩ := present
    have retained := authoritativeScheduledAssignmentAt?_unit
      discovery (authoritativeSolvedState discovery fuel) unit assignment emitted
    rw [retained]
    exact emitted
  · intro emitted
    rw [analyzeAuthoritativeScheduledTetrahedral, List.mem_filterMap]
    exact ⟨assignment.unit, root_mem_allRoots mol assignment.unit, emitted⟩

/-- The authoritative scheduled assignment list has no duplicate entries. -/
theorem analyzeAuthoritativeScheduledTetrahedral_nodup {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat) :
    (analyzeAuthoritativeScheduledTetrahedral discovery fuel).Nodup := by
  classical
  unfold analyzeAuthoritativeScheduledTetrahedral
  apply (allRoots_nodup mol).filterMap
  intro left right assignment leftComputed rightComputed
  have leftUnit := authoritativeScheduledAssignmentAt?_unit
    discovery (authoritativeSolvedState discovery fuel) left assignment leftComputed
  have rightUnit := authoritativeScheduledAssignmentAt?_unit
    discovery (authoritativeSolvedState discovery fuel) right assignment rightComputed
  exact leftUnit.symm.trans rightUnit

/-- Projecting public assignments to physical final units remains duplicate-free. -/
theorem analyzeAuthoritativeScheduledTetrahedral_units_nodup {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat) :
    ((analyzeAuthoritativeScheduledTetrahedral discovery fuel).map
      AuthoritativeScheduledAssignment.unit).Nodup := by
  classical
  apply (analyzeAuthoritativeScheduledTetrahedral_nodup discovery fuel).map_on
  intro left leftPresent right rightPresent sameUnit
  have leftComputed :=
    (mem_analyzeAuthoritativeScheduledTetrahedral_iff discovery fuel left).mp leftPresent
  have rightComputed :=
    (mem_analyzeAuthoritativeScheduledTetrahedral_iff discovery fuel right).mp rightPresent
  rw [sameUnit] at leftComputed
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

/-- Exact proof-relevant semantics of one public authoritative assignment: the solved state's
ordinary/Rule-6 derivation produces precisely this retained label at precisely this final unit. -/
def ExactDeclarativeAuthoritativeScheduledAssignment {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat)
    (assignment : AuthoritativeScheduledAssignment discovery) : Prop :=
  AuthoritativeDerivation discovery fuel (authoritativeSolvedState discovery fuel)
    (finalOccurrence discovery assignment.unit) (some assignment.label)

/-- Public list membership is equivalent to the independent derivation relation, not merely
implied by it. -/
theorem mem_analyzeAuthoritativeScheduledTetrahedral_iff_exactDeclarative
    {mol : RawMolecule} (discovery : Discovery mol) (fuel : Nat)
    (assignment : AuthoritativeScheduledAssignment discovery) :
    assignment ∈ analyzeAuthoritativeScheduledTetrahedral discovery fuel ↔
      ExactDeclarativeAuthoritativeScheduledAssignment discovery fuel assignment := by
  let state := authoritativeSolvedState discovery fuel
  let target := finalOccurrence discovery assignment.unit
  have model := authoritativeSolvedState_cipModel discovery fuel
  constructor
  · intro present
    have computed :=
      (mem_analyzeAuthoritativeScheduledTetrahedral_iff discovery fuel assignment).mp present
    have assigned := authoritativeScheduledAssignmentAt?_label
      discovery state assignment.unit assignment computed
    have derived := model target
    simpa [ExactDeclarativeAuthoritativeScheduledAssignment, state, target,
      authoritativeOccurrenceSystem, assigned] using derived
  · intro derived
    have requestedStep : authoritativeDerive? discovery fuel state target =
        some assignment.label :=
      (authoritativeDerivation_iff_derive? discovery fuel state target
        (some assignment.label)).mp (by
          simpa [ExactDeclarativeAuthoritativeScheduledAssignment, state, target] using derived)
    have modelDerived := model target
    have modelStep : authoritativeDerive? discovery fuel state target = state target :=
      (authoritativeDerivation_iff_derive? discovery fuel state target (state target)).mp (by
        simpa [authoritativeOccurrenceSystem, state, target] using modelDerived)
    have assigned : state target = some assignment.label :=
      modelStep.symm.trans requestedStep
    apply (mem_analyzeAuthoritativeScheduledTetrahedral_iff
      discovery fuel assignment).mpr
    simp [authoritativeScheduledAssignmentAt?, state, target, assigned]

/-- Refusal of a particular retained unit/label pair is exactly negation of its declarative
authoritative derivation. -/
theorem not_mem_analyzeAuthoritativeScheduledTetrahedral_iff_not_exactDeclarative
    {mol : RawMolecule} (discovery : Discovery mol) (fuel : Nat)
    (assignment : AuthoritativeScheduledAssignment discovery) :
    assignment ∉ analyzeAuthoritativeScheduledTetrahedral discovery fuel ↔
      ¬ ExactDeclarativeAuthoritativeScheduledAssignment discovery fuel assignment :=
  (mem_analyzeAuthoritativeScheduledTetrahedral_iff_exactDeclarative
    discovery fuel assignment).not

/-- Independent public meaning of one scheduled authoritative assignment. -/
def DeclarativeAuthoritativeScheduledAssignment {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat)
    (assignment : AuthoritativeScheduledAssignment discovery) : Prop :=
  let state := authoritativeSolvedState discovery fuel
  let target := finalOccurrence discovery assignment.unit
  OrdinaryDerivation discovery fuel state target assignment.label ∨
    ∃ aux roots result,
      authoritativeOccurrenceRule6Result? mol aux fuel
          (sourceNode discovery target) roots = some result ∧
        assignment.label.fact = result.fact ∧
        AuthoritativeRule6BranchDescriptorJudgment
          (authoritativeOccurrenceRule6PositionRankingBackend
            mol aux fuel result.roots result.ligands)
          result.parity result.sorted result.adjacent result.groupCount
            assignment.label.fact.descriptor

/-- Every public assignment is justified by the exact ordinary or authoritative Rule-6 branch. -/
theorem analyzeAuthoritativeScheduledTetrahedral_member_conforms {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat)
    (assignment : AuthoritativeScheduledAssignment discovery)
    (present : assignment ∈ analyzeAuthoritativeScheduledTetrahedral discovery fuel) :
    DeclarativeAuthoritativeScheduledAssignment discovery fuel assignment := by
  have computed :=
    (mem_analyzeAuthoritativeScheduledTetrahedral_iff discovery fuel assignment).mp present
  have assigned := authoritativeScheduledAssignmentAt?_label
    discovery (authoritativeSolvedState discovery fuel) assignment.unit assignment computed
  exact authoritativeModel_assignment_certified_at discovery fuel
    (authoritativeSolvedState_cipModel discovery fuel)
    (finalOccurrence discovery assignment.unit) assignment.label assigned

/-- When the ordinary evaluator is silent, a public member necessarily carries the exact uncapped
P-92 Rule-6 branch judgment. -/
theorem analyzeAuthoritativeScheduledTetrahedral_member_rule6_of_ordinaryNone
    {mol : RawMolecule} (discovery : Discovery mol) (fuel : Nat)
    (assignment : AuthoritativeScheduledAssignment discovery)
    (present : assignment ∈ analyzeAuthoritativeScheduledTetrahedral discovery fuel)
    (ordinaryNone : ordinaryLabel? discovery fuel
      (authoritativeSolvedState discovery fuel)
      (finalOccurrence discovery assignment.unit) = none) :
    ∃ aux roots result,
      authoritativeOccurrenceRule6Result? mol aux fuel
          (sourceNode discovery (finalOccurrence discovery assignment.unit)) roots =
        some result ∧
      assignment.label.fact = result.fact ∧
      AuthoritativeRule6BranchDescriptorJudgment
        (authoritativeOccurrenceRule6PositionRankingBackend
          mol aux fuel result.roots result.ligands)
        result.parity result.sorted result.adjacent result.groupCount
          assignment.label.fact.descriptor := by
  have computed :=
    (mem_analyzeAuthoritativeScheduledTetrahedral_iff discovery fuel assignment).mp present
  have assigned := authoritativeScheduledAssignmentAt?_label
    discovery (authoritativeSolvedState discovery fuel) assignment.unit assignment computed
  exact authoritativeModel_rule6_assignment_sound discovery fuel
    (authoritativeSolvedState_cipModel discovery fuel)
    (finalOccurrence discovery assignment.unit) assignment.label assigned ordinaryNone

/-- Every solved final-unit label is represented by its literal public assignment. -/
theorem exists_mem_analyzeAuthoritativeScheduledTetrahedral_of_assigned
    {mol : RawMolecule} (discovery : Discovery mol) (fuel : Nat)
    (unit : FinalUnit mol) (label : Label discovery)
    (assigned : authoritativeSolvedState discovery fuel
      (finalOccurrence discovery unit) = some label) :
    ∃ assignment : AuthoritativeScheduledAssignment discovery,
      assignment ∈ analyzeAuthoritativeScheduledTetrahedral discovery fuel ∧
        assignment.unit = unit ∧ assignment.label = label := by
  let assignment : AuthoritativeScheduledAssignment discovery := { unit, label }
  have computed : authoritativeScheduledAssignmentAt? discovery
      (authoritativeSolvedState discovery fuel) unit = some assignment := by
    simp [authoritativeScheduledAssignmentAt?, assigned, assignment]
  exact ⟨assignment,
    (mem_analyzeAuthoritativeScheduledTetrahedral_iff discovery fuel assignment).mpr computed,
    rfl, rfl⟩

/-- Every public authoritative physical unit has literal multiplicity one. -/
theorem authoritativeScheduledAssignment_unit_count_eq_one {mol : RawMolecule}
    (discovery : Discovery mol) (fuel : Nat)
    (assignment : AuthoritativeScheduledAssignment discovery)
    (present : assignment ∈ analyzeAuthoritativeScheduledTetrahedral discovery fuel) :
    List.count assignment.unit
      ((analyzeAuthoritativeScheduledTetrahedral discovery fuel).map
        AuthoritativeScheduledAssignment.unit) = 1 := by
  exact List.count_eq_one_of_mem
    (analyzeAuthoritativeScheduledTetrahedral_units_nodup discovery fuel)
    (List.mem_map.mpr ⟨assignment, present, rfl⟩)

end TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler
