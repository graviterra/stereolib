import TetraStereo.OneCenter.LocalizedRule3EndpointPreflight
import TetraStereo.OneCenter.LocalizedRule3EndpointCallbackDemand
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Preflight-pruned Rule-3 callback demand

`LocalizedRule3EndpointPreflight` proves that a false Boolean endpoint-pair readiness
preflight makes the executable ordinary and odd spatial short-circuit compilers return `none`
for *every* view and *every* Rule-3 frame callback.  Consequently, when readiness is false there
is no callback dependence in the final result.  The existing evaluators may still perform
callbacks before refusing; the guarded twins below avoid that work.

This module makes that pruning explicit.

* `rule3PreflightShortSpatialCallbackRequests` is the ordinary spatial demand guarded by
  `ordinaryPairReady`; `rule3PreflightShortOddCallbackRequests` is the odd analogue guarded by
  `oddPairReady`.
* Both are pointwise subsets of the unguarded short demands.
* `rule3PreflightShortSpatial_callback_local` and `rule3PreflightShortOdd_callback_local` prove
  callback locality for the *existing* executable spatial compilers from agreement only on the
  guarded requests: on ready inputs the guarded list is the original list, and on non-ready
  inputs both sides are `none` by the preflight refusal theorem.
* `rule3PreflightExtendedNodeCallbackRequests` guards the odd route by `oddPairReady` and the
  ordinary route by `ordinaryPairReady`, falling back to the existing `rule3NodeCallbackRequests`
  when neither route certificate applies.  It is a pointwise subset of the current
  `rule3ExtendedNodeCallbackRequests`, and
  `rule3PreflightExtendedNode_callback_local` proves locality of the existing
  `localizedRule3ExtendedShortCircuitNodeWithExec?` at any target, view and exclusion list from
  agreement on this narrower graph.

No chemical relation, evaluator branch, or recursion is added.  In particular this module does
not assert any general acyclicity statement; it only supplies the narrower request graph and its
locality so that an existing rank-stability argument can be instantiated on it.
-/

/-- Ordinary spatial callback demand, pruned by the Boolean endpoint-pair preflight.  When the
physical endpoint frame is absent or either endpoint pair is not ready, the spatial compiler
has a callback-independent result, so the pruned demand is empty. -/
def rule3PreflightShortSpatialCallbackRequests (input : CertifiedLocalizedCIPInput)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    List (List (input.LocalizedRerootCursor fuel)) :=
  if input.ordinaryPairReady occurrence then
    input.rule3ShortSpatialCallbackRequests occurrence
  else
    []

/-- Odd-cumulene spatial callback demand, pruned by the Boolean endpoint-pair preflight.  When the
odd-cumulene endpoint frame is absent or either endpoint pair is not ready, the odd spatial
compiler has a callback-independent result, so the pruned demand is empty. -/
def rule3PreflightShortOddCallbackRequests (input : CertifiedLocalizedCIPInput)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    List (List (input.LocalizedRerootCursor fuel)) :=
  if input.oddPairReady occurrence then
    input.rule3ShortOddCallbackRequests occurrence
  else
    []

@[simp] theorem rule3PreflightShortSpatialCallbackRequests_eq_of_ready
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (ready : input.ordinaryPairReady occurrence = true) :
    input.rule3PreflightShortSpatialCallbackRequests occurrence =
      input.rule3ShortSpatialCallbackRequests occurrence := by
  simp [rule3PreflightShortSpatialCallbackRequests, ready]

@[simp] theorem rule3PreflightShortSpatialCallbackRequests_eq_nil_of_notReady
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (notReady : input.ordinaryPairReady occurrence = false) :
    input.rule3PreflightShortSpatialCallbackRequests occurrence = [] := by
  simp [rule3PreflightShortSpatialCallbackRequests, notReady]

@[simp] theorem rule3PreflightShortOddCallbackRequests_eq_of_ready
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (ready : input.oddPairReady occurrence = true) :
    input.rule3PreflightShortOddCallbackRequests occurrence =
      input.rule3ShortOddCallbackRequests occurrence := by
  simp [rule3PreflightShortOddCallbackRequests, ready]

@[simp] theorem rule3PreflightShortOddCallbackRequests_eq_nil_of_notReady
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (notReady : input.oddPairReady occurrence = false) :
    input.rule3PreflightShortOddCallbackRequests occurrence = [] := by
  simp [rule3PreflightShortOddCallbackRequests, notReady]

/-- The guarded ordinary demand can only remove requests: it is a pointwise subset of the
existing short spatial demand, independently of the callback, the view and the target. -/
theorem rule3PreflightShortSpatialCallbackRequests_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    ∀ request ∈ input.rule3PreflightShortSpatialCallbackRequests occurrence,
      request ∈ input.rule3ShortSpatialCallbackRequests occurrence := by
  intro request present
  cases ready : input.ordinaryPairReady occurrence with
  | false => simp [rule3PreflightShortSpatialCallbackRequests, ready] at present
  | true => simpa only [rule3PreflightShortSpatialCallbackRequests, ready, if_true] using present

/-- The guarded odd demand can only remove requests: it is a pointwise subset of the existing
short odd spatial demand. -/
theorem rule3PreflightShortOddCallbackRequests_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    ∀ request ∈ input.rule3PreflightShortOddCallbackRequests occurrence,
      request ∈ input.rule3ShortOddCallbackRequests occurrence := by
  intro request present
  cases ready : input.oddPairReady occurrence with
  | false => simp [rule3PreflightShortOddCallbackRequests, ready] at present
  | true => simpa only [rule3PreflightShortOddCallbackRequests, ready, if_true] using present

/-- Callback locality of the existing executable ordinary spatial compiler from agreement on the
preflight-pruned demand.  If the pair preflight is true, the pruned demand is the original short
spatial demand and `rule3ShortSpatial_callback_local` applies.  If it is false, the preflight
refusal theorem makes both results `none`, independently of callbacks. -/
theorem rule3PreflightShortSpatial_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn
      (input.rule3PreflightShortSpatialCallbackRequests occurrence) before after) :
    input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence view before =
      input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence view after := by
  cases ready : input.ordinaryPairReady occurrence with
  | true =>
      refine input.rule3ShortSpatial_callback_local target occurrence view before after ?_
      intro cursors member
      exact agree cursors (by
        simpa only [rule3PreflightShortSpatialCallbackRequests, ready, if_true] using member)
  | false =>
      rw [input.localizedRule3ShortCircuitSpatialUnitWithExec?_eq_none_of_pairNotReady
            target occurrence view before ready,
          input.localizedRule3ShortCircuitSpatialUnitWithExec?_eq_none_of_pairNotReady
            target occurrence view after ready]

/-- Callback locality of the existing executable odd spatial compiler from agreement on the
preflight-pruned odd demand. -/
theorem rule3PreflightShortOdd_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn
      (input.rule3PreflightShortOddCallbackRequests occurrence) before after) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view before =
      input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view after := by
  cases ready : input.oddPairReady occurrence with
  | true =>
      refine input.rule3ShortOddSpatial_callback_local target occurrence view before after ?_
      intro cursors member
      exact agree cursors (by
        simpa only [rule3PreflightShortOddCallbackRequests, ready, if_true] using member)
  | false =>
      rw [input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_none_of_pairNotReady
            target occurrence view before ready,
          input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_none_of_pairNotReady
            target occurrence view after ready]

/-- Guarded executable ordinary spatial twin: compute the existing spatial unit only after the
pair preflight succeeds. -/
def rule3PreflightShortCircuitSpatialUnitWithExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3ShortCircuitSpatialResult fuel) :=
  if input.ordinaryPairReady occurrence then
    input.localizedRule3ShortCircuitSpatialUnitWithExec? target occurrence view callback
  else
    none

/-- Guarded executable odd spatial twin: compute the existing odd spatial unit only after the
odd pair preflight succeeds. -/
def rule3PreflightShortCircuitOddSpatialUnitWithExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3ShortCircuitOddSpatialResult fuel) :=
  if input.oddPairReady occurrence then
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec? target occurrence view callback
  else
    none

/-- The guarded ordinary twin agrees with the existing compiler at every callback, including
every refusal: on ready inputs it is the same call, and on non-ready inputs the preflight refusal
theorem makes both sides `none`. -/
theorem rule3PreflightShortCircuitSpatialUnitWithExec?_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.rule3PreflightShortCircuitSpatialUnitWithExec?
        target occurrence view callback =
      input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence view callback := by
  cases ready : input.ordinaryPairReady occurrence with
  | true => simp [rule3PreflightShortCircuitSpatialUnitWithExec?, ready]
  | false =>
      simp [rule3PreflightShortCircuitSpatialUnitWithExec?, ready,
        input.localizedRule3ShortCircuitSpatialUnitWithExec?_eq_none_of_pairNotReady
          target occurrence view callback ready]

/-- The guarded odd twin agrees with the existing odd compiler at every callback, including every
refusal. -/
theorem rule3PreflightShortCircuitOddSpatialUnitWithExec?_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.rule3PreflightShortCircuitOddSpatialUnitWithExec?
        target occurrence view callback =
      input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view callback := by
  cases ready : input.oddPairReady occurrence with
  | true => simp [rule3PreflightShortCircuitOddSpatialUnitWithExec?, ready]
  | false =>
      simp [rule3PreflightShortCircuitOddSpatialUnitWithExec?, ready,
        input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_none_of_pairNotReady
          target occurrence view callback ready]

/-- Actual requests of the extended evaluator under both preflights.  A checked odd route uses
the pruned odd demand, a checked ordinary route uses the pruned ordinary spatial demand, and the
remaining route keeps the existing successor demand analysis unchanged. -/
def rule3PreflightExtendedNodeCallbackRequests (input : CertifiedLocalizedCIPInput)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | some _ => input.rule3PreflightShortOddCallbackRequests occurrence
  | none =>
    match input.localizedRule3OrdinaryRouteCertificate? occurrence with
    | some _ => input.rule3PreflightShortSpatialCallbackRequests occurrence
    | none => input.rule3NodeCallbackRequests occurrence

/-- The preflight-pruned extended demand is contained in the current extended demand graph.
The statement is independent of target, view, callback answers, geometry and exclusions. -/
theorem rule3PreflightExtendedNodeCallbackRequests_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    ∀ request ∈ input.rule3PreflightExtendedNodeCallbackRequests occurrence,
      request ∈ input.rule3ExtendedNodeCallbackRequests occurrence := by
  intro request present
  unfold rule3PreflightExtendedNodeCallbackRequests at present
  cases odd : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      simp only [odd] at present
      have inShort := input.rule3PreflightShortOddCallbackRequests_subset
        occurrence request present
      simpa only [rule3ExtendedNodeCallbackRequests, odd] using inShort
  | none =>
      simp only [odd] at present
      cases ordinary : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some certificate =>
          simp only [ordinary] at present
          have inShort := input.rule3PreflightShortSpatialCallbackRequests_subset
            occurrence request present
          simpa only [rule3ExtendedNodeCallbackRequests, rule3NodeCallbackRequests,
            odd, ordinary] using inShort
      | none =>
          simp only [ordinary] at present
          simpa only [rule3ExtendedNodeCallbackRequests, rule3NodeCallbackRequests,
            odd, ordinary] using present

/-- Callback locality of the existing extended short-circuit node evaluator from agreement on
the preflight-pruned request graph.  The exclusion list, target and dependency view are
arbitrary.  On a checked odd route the odd preflight applies (`rule3ShortOddSpatial_callback_local`
when ready, universal refusal otherwise); on a checked ordinary route the ordinary preflight
applies; on the remaining route the existing successor locality theorem is used verbatim. -/
theorem rule3PreflightExtendedNode_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn
      (input.rule3PreflightExtendedNodeCallbackRequests occurrence) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view before excluded =
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view after excluded := by
  unfold localizedRule3ExtendedShortCircuitNodeWithExec?
  cases odd : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      have oddAgree : input.Rule3CallbackAgreesOn
          (input.rule3PreflightShortOddCallbackRequests occurrence) before after := by
        simpa only [rule3PreflightExtendedNodeCallbackRequests, odd] using agree
      rw [input.rule3PreflightShortOdd_callback_local
        target occurrence view before after oddAgree]
  | none =>
      cases ordinary : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some certificate =>
          unfold localizedRule3ShortCircuitNodeWithExec?
          simp only [ordinary]
          have spatialAgree : input.Rule3CallbackAgreesOn
              (input.rule3PreflightShortSpatialCallbackRequests occurrence) before after := by
            simpa only [rule3PreflightExtendedNodeCallbackRequests, odd, ordinary] using agree
          rw [input.rule3PreflightShortSpatial_callback_local
            target occurrence view before after spatialAgree]
      | none =>
          have nodeAgree : input.Rule3CallbackAgreesOn
              (input.rule3NodeCallbackRequests occurrence) before after := by
            simpa only [rule3PreflightExtendedNodeCallbackRequests, odd, ordinary] using agree
          exact input.rule3Node_callback_local
            target occurrence view before after nodeAgree excluded

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
