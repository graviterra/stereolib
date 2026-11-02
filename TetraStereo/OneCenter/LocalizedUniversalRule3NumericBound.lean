import TetraStereo.Certificate.WeightedDemandBound
import TetraStereo.OneCenter.LocalizedUniversalRule3Evaluation

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand

















































/-! ## Input-derived occurrence count and cursor cardinality -/

/-- The single executable occurrence quantity used by this module: the length of the finite
occurrence carrier.  Kept as a named definition so that later expressions can share one `Nat`
instead of re-reading the carrier. -/
def universalRule3OccurrenceCount (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Nat :=
  (input.localizedOccurrenceCarrier fuel).length

/-- Executable cursor cardinality `occurrenceCount * (occurrenceCount + 1)`.  The occurrence count
is bound once by the `let`, so runtime evaluation reads the carrier a single time. -/
def universalRule3CursorCard (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Nat :=
  let occurrenceCount := input.universalRule3OccurrenceCount fuel
  occurrenceCount * (occurrenceCount + 1)

/-- The uniform evaluator budget asserted by this module: twice the cursor cardinality plus one.
It is derived from the input alone and depends on no target, view, root list, ranking or desired
descriptor. -/
def universalRule3EvaluationBound (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Nat :=
  2 * input.universalRule3CursorCard fuel + 1

@[simp] theorem universalRule3OccurrenceCount_eq (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.universalRule3OccurrenceCount fuel = (input.localizedOccurrenceCarrier fuel).length := rfl

/-- The executable cursor-cardinality expression is exactly the `Fintype.card` of the cursor type.
The proof is the existing exact card identity `localizedRerootCursor_card`; no enumeration of the
proof-only instance happens at runtime. -/
theorem universalRule3CursorCard_eq_fintypeCard (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    [Fintype (input.LocalizedRerootCursor fuel)] :
    input.universalRule3CursorCard fuel = Fintype.card (input.LocalizedRerootCursor fuel) := by
  show (input.localizedOccurrenceCarrier fuel).length *
      ((input.localizedOccurrenceCarrier fuel).length + 1) =
    Fintype.card (input.LocalizedRerootCursor fuel)
  exact (input.localizedRerootCursor_card fuel).symm

/-! ## The computed universal bound is at most `2 * card + 1` -/










theorem prepareUniversalRule3EvaluationOutcome_bound_le_universal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (prepareUniversalRule3EvaluationOutcome input roots target view).1 ≤
      input.universalRule3EvaluationBound carrierFuel := by
  cases computed : input.preparePreflightExtendedDemandPlan roots with
  | ok plan =>
      have boundEq :
          (prepareUniversalRule3EvaluationOutcome input roots target view).1 = plan.bound := by
        simp [prepareUniversalRule3EvaluationOutcome, computed]
      rw [boundEq]
      letI := input.localizedRerootCursorFintype carrierFuel
      have computedAtCard :
          prepare (input.preflightExtendedWeightedDemandGraph carrierFuel)
              (Fintype.card (input.LocalizedRerootCursor carrierFuel) + 1) roots = .ok plan := by
        change prepare (input.preflightExtendedWeightedDemandGraph carrierFuel)
            (input.preflightExtendedDemandTraversalBudget carrierFuel) roots = .ok plan at computed
        rw [input.preflightExtendedDemandTraversalBudget_eq_card_add_one carrierFuel] at computed
        exact computed
      have planBound : plan.bound ≤
          2 * Fintype.card (input.LocalizedRerootCursor carrierFuel) + 1 :=
        prepare_bound_of_ok (input.preflightExtendedWeightedDemandGraph carrierFuel) roots plan
          computedAtCard
      show plan.bound ≤ 2 * input.universalRule3CursorCard carrierFuel + 1
      rw [input.universalRule3CursorCard_eq_fintypeCard carrierFuel]
      exact planBound
  | error failure =>
      have boundZero :
          (prepareUniversalRule3EvaluationOutcome input roots target view).1 = 0 := by
        simp [prepareUniversalRule3EvaluationOutcome, computed]
      rw [boundZero]
      exact Nat.zero_le _

/-! ## The actual extended frame at the universal budget -/

/-- **Main universal numeric stability theorem.**  At the explicit input-derived budget
`universalRule3EvaluationBound carrierFuel = 2 * card + 1` and at every larger budget, the actual
executable extended two-pass evaluator agrees with the universal outcome frame, for arbitrary root
lists, targets and dependency views.  There is no acyclicity, root-validity, ranking, desired
answer, successful-callback or `Propagates` hypothesis: the constructor's own outcome selects the
value, and `prepareUniversalRule3EvaluationOutcome_stable` supplies stability at every budget above
the computed outcome bound. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_eq_universalOutcome_of_universalBound_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ evaluationBudget,
      input.universalRule3EvaluationBound carrierFuel ≤ evaluationBudget →
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view evaluationBudget roots =
          (prepareUniversalRule3EvaluationOutcome input roots target view).2 := by
  intro evaluationBudget enough
  exact input.prepareUniversalRule3EvaluationOutcome_stable roots target view evaluationBudget
    (Nat.le_trans
      (input.prepareUniversalRule3EvaluationOutcome_bound_le_universal roots target view) enough)

/-- The same equality at exactly the universal budget. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_universalBound_eq_universalOutcome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (input.universalRule3EvaluationBound carrierFuel) roots =
      (prepareUniversalRule3EvaluationOutcome input roots target view).2 :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec?_eq_universalOutcome_of_universalBound_le
    roots target view (input.universalRule3EvaluationBound carrierFuel) (Nat.le_refl _)

/-! ## Relation to the legacy production fuel

The production fuel is not asserted to dominate the universal cardinal bound.  The only bridge is
the following explicitly conditional statement, which additionally relates production evaluation
directly to the universal outcome frame. -/

/-- Under the explicit side condition that the universal cardinal bound fits inside the fixed
production fuel, the production evaluation equals the universal outcome frame.  No theorem in this
module asserts that side condition: the production fuel is parameterized by `carrierFuel` while the
universal bound is parameterized by the occurrence count, so the comparison is genuinely
input-dependent. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_eq_universalOutcome_of_productionFuelBound_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (enough : input.universalRule3EvaluationBound carrierFuel ≤
      localizedDescriptorBearingRule3EvaluationFuel carrierFuel) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) roots =
      (prepareUniversalRule3EvaluationOutcome input roots target view).2 :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec?_eq_universalOutcome_of_universalBound_le
    roots target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) enough

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
