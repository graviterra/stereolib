import TetraStereo.OneCenter.LocalizedExtendedFallbackNoRead
import TetraStereo.OneCenter.LocalizedRule3ActualDemandReaderLocality
import TetraStereo.OneCenter.LocalizedRule3OddOriginalTargetDemand
import TetraStereo.OneCenter.LocalizedParametricExtendedRule3Key
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Outward locality of the actual extended Rule-3 requests and whole-state node agreement

`LocalizedRule3ShortCircuitOddNode` defines the actual extended Rule-3 callback demand

```
rule3ExtendedNodeCallbackRequests occurrence =
  match localizedRule3OddRouteCertificate? occurrence with
  | none => rule3NodeCallbackRequests occurrence
  | some _ => rule3ShortOddCallbackRequests occurrence
```

and `LocalizedParametricExtendedRule3Key` proves a full `Option` congruence of the parametric
extended node from callback agreement on exactly that request list together with reader agreement
on its executable-reachable support.

This module supplies the missing *actual* locality input for a physical occurrence `O` and a
strictly shallower original descriptor target `T` of the same rooted carrier
(`LocalizedDepthDependency O T`):

* `rule3ExtendedActualRequest_outward` — every cursor occurring in every request actually emitted
  by `rule3ExtendedNodeCallbackRequests O` is an outward cursor of `T`.
* `rule3ExtendedNodeCallbackRequests_mem_short` — every emitted extended request is a request of
  one of the two already-analysed short lists, `rule3ShortOddCallbackRequests O` or
  `rule3ShortSpatialCallbackRequests O`.

The first result is assembled from the three actual branches only:

* the checked odd route delegates to `rule3ShortOddActualRequest_outward`
  (`LocalizedRule3OddOriginalTargetDemand`);
* the failed odd route with a successful ordinary route delegates to `rule3ActualRequest_outward`
  (`LocalizedRule3OriginalTargetDemand`), i.e. to the ordinary *short* spatial requests;
* the joint route-certificate failure makes the request list empty
  (`rule3ExtendedNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone`,
  `LocalizedExtendedFallbackNoRead`).

The arbitrary eager odd request list `rule3OddCallbackRequests` is deliberately **not** claimed:
on the rooted path `T-P=O=C=D` its initial left endpoint can request `T` itself.  The extended
short-circuit evaluator never demands it on the odd route.

## Whole-state reader agreement

With the outward request support in hand, `LocalizedRerootReadersAgreeOnRequests_of_outwardCursors`
(`LocalizedRule3ActualDemandReaderLocality`) turns it into agreement between the unrestricted
whole-state reader and the restricted dependency reader on exactly the actual extended requests.
Feeding that to `localizedRule3ExtendedShortCircuitNodeWithRead?_congr_of_callbackAgree`
(`LocalizedParametricExtendedRule3Key`) yields full `Option` equality of the parametric extended
node with

* the same original descriptor target `T`,
* the same restricted dependency view `localizedDependencyView state T`,
* the same exclusion list,
* two callbacks that are only required to agree on the actual requests,

but an arbitrary whole-state reader on the left and the shipped restricted reader on the right.
Composing with the unconditional restricted-reader specialization
`..._eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel` identifies the
right-hand side with the shipped executable extended node, including every fail-closed `none`.

## Scope and residual work

Only the **direct extended single-node wrapper** is covered.  The recursive key/frame/node
recursion with the whole-state reader is not claimed: its recursive calls build the frame with the
same reader at every deeper occurrence, which requires an outward inductive argument on the
recursion rather than the single request list analysed here.  No callback totality, no successful
key or descriptor premise, and no reader totality is assumed or asserted.

## Kernel authority

Every exported declaration is guarded by `assert_kernel_only`.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Structural support of the actual extended requests -/

/-- **Every actual extended request is a short odd or short spatial request.**  This is the
case analysis of the actual demand definition:

* a checked odd route emits exactly `rule3ShortOddCallbackRequests`;
* a failed odd route with a successful ordinary route emits exactly
  `rule3ShortSpatialCallbackRequests`;
* a failed odd route with a failed ordinary route emits nothing at all, by the joint-failure
  emptiness theorem of `LocalizedExtendedFallbackNoRead`.

The lemma is exported on its own so that recursive consumers of the extended request list can
reduce its outward support to the two already-established short lists. -/
theorem rule3ExtendedNodeCallbackRequests_mem_short
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ExtendedNodeCallbackRequests occurrence) :
    request ∈ input.rule3ShortOddCallbackRequests occurrence ∨
      request ∈ input.rule3ShortSpatialCallbackRequests occurrence := by
  cases odd : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      exact Or.inl (by
        simpa only [rule3ExtendedNodeCallbackRequests, odd] using member)
  | none =>
      have nodeMember : request ∈ input.rule3NodeCallbackRequests occurrence := by
        simpa only [rule3ExtendedNodeCallbackRequests, odd] using member
      cases ordinary : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some certificate =>
          exact Or.inr (by
            simpa only [rule3NodeCallbackRequests, ordinary] using nodeMember)
      | none =>
          have nil := input.rule3NodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
            occurrence ordinary odd
          rw [nil] at nodeMember
          exact absurd nodeMember (by simp)

/-- **Outward support of the actual extended short-circuit Rule-3 requests.**  Let `O` be a
physical occurrence and `T` a strictly shallower original descriptor target of the same rooted
carrier.  Then every cursor occurring in every request actually emitted by
`rule3ExtendedNodeCallbackRequests O` is an outward cursor of `T`: it is path valid, strictly
deeper than `T` in the same rooted carrier, and records an incoming cut of strictly smaller
address length.

This is the request-locality export consumed by the whole-state reader agreement below and by
sibling outward recursive work.  It is stated independently of any node equality and uses no
successful key, comparison, callback result or descriptor premise. -/
theorem rule3ExtendedActualRequest_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T) :
    ∀ request ∈ input.rule3ExtendedNodeCallbackRequests O,
      ∀ cursor ∈ request, OutwardRerootCursor input T cursor := by
  intro request member cursor cursorMem
  rcases input.rule3ExtendedNodeCallbackRequests_mem_short O request member with
    oddMember | spatialMember
  · exact input.rule3ShortOddActualRequest_outward O T deeper
      request oddMember cursor cursorMem
  · exact input.rule3ActualRequest_outward O T deeper
      request spatialMember cursor cursorMem

/-- **Empty extended demand under joint route-certificate failure, restated at this module's
API.**  This is a named re-export of the emptiness theorem of `LocalizedExtendedFallbackNoRead`
together with the definitional odd-route delegation, so that consumers of this module can use the
empty branch without reaching into that module's naming. -/
theorem rule3ExtendedNodeCallbackRequests_nil_of_jointRouteCertificateNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none) :
    input.rule3ExtendedNodeCallbackRequests occurrence = [] :=
  input.rule3ExtendedNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
    occurrence ordinaryNone oddNone

/-! ## Whole-state reader agreement on the actual extended requests -/

/-- **Reader agreement at the actual extended requests.**  The unrestricted whole-state reader and
the shipped restricted dependency reader agree on every cursor executable-reachable from every
cursor occurring in every actual extended request, as soon as every such cursor is outward of the
descriptor target.  This is the per-request reader premise of the node congruence, discharged by
`rule3ExtendedActualRequest_outward`. -/
theorem LocalizedRerootReadersAgreeOnRequests_of_extendedActualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    input.LocalizedRerootReadersAgreeOnRequests
      (input.localizedWholeStateReader state)
      (fun cursor => input.localizedDependencyLabel T
        (input.localizedDependencyView state T) cursor)
      (input.rule3ExtendedNodeCallbackRequests O) :=
  input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors T state
    (input.rule3ExtendedNodeCallbackRequests O)
    (input.rule3ExtendedActualRequest_outward O T deeper)

/-! ## Whole-state parametric extended node -/

/-- **Whole-state versus restricted extended node, callbacks agreeing only on actual requests.**
For a physical occurrence `O` strictly below the original descriptor target `T`, the parametric
extended short-circuit node over the whole auxiliary state and the parametric extended node over
the restricted dependency view are exactly equal, as full `Option` values, with

* the same target `T`, view `localizedDependencyView state T` and exclusion list;
* arbitrary callbacks `before`/`after` agreeing only on `rule3ExtendedNodeCallbackRequests O`;
* an arbitrary whole-state reader versus the shipped restricted reader.

The reader premise is discharged by `LocalizedRerootReadersAgreeOnRequests_of_extendedActualRequests`;
the callback premise remains an explicit hypothesis. -/
theorem localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_restricted_of_deeper
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (callbackAgree : input.Rule3CallbackAgreesOn
      (input.rule3ExtendedNodeCallbackRequests O) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedShortCircuitNodeWithRead?
        T O (input.localizedDependencyView state T)
        (input.localizedWholeStateReader state) before excluded =
      input.localizedRule3ExtendedShortCircuitNodeWithRead?
        T O (input.localizedDependencyView state T)
        (fun cursor => input.localizedDependencyLabel T
          (input.localizedDependencyView state T) cursor) after excluded :=
  input.localizedRule3ExtendedShortCircuitNodeWithRead?_congr_of_callbackAgree
    T O (input.localizedDependencyView state T)
    (input.localizedWholeStateReader state)
    (fun cursor => input.localizedDependencyLabel T
      (input.localizedDependencyView state T) cursor)
    before after callbackAgree
    (input.LocalizedRerootReadersAgreeOnRequests_of_extendedActualRequests
      O T deeper state)
    excluded

/-- **Whole-state versus shipped executable extended node at the same callback.**  With one
supplied callback on both sides (agreeing with itself trivially) the whole-state parametric
extended node equals the shipped executable extended node built from the actual restricted
dependency view `localizedDependencyView state T`, at the same target, occurrence, callback and
exclusion list.  Both sides carry full `Option` agreement, including every fail-closed `none` and
the odd physical-unit exclusion policy. -/
theorem localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_Exec?_of_deeper
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedShortCircuitNodeWithRead?
        T O (input.localizedDependencyView state T)
        (input.localizedWholeStateReader state) callback excluded =
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        T O (input.localizedDependencyView state T) callback excluded := by
  rw [input.localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_restricted_of_deeper
    O T deeper state callback callback (by intro cursors _member; rfl) excluded]
  exact
    input.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel
      T O (input.localizedDependencyView state T) callback excluded

/-- **Whole-state extended node versus shipped executable node, callbacks agreeing only on the
actual requests.**  The two callbacks may differ off the actual extended demand; only their
values on `rule3ExtendedNodeCallbackRequests O` are used.  The right-hand side is the shipped
executable node at the restricted dependency view. -/
theorem localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_Exec?_of_deeper_of_callbackAgree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (callbackAgree : input.Rule3CallbackAgreesOn
      (input.rule3ExtendedNodeCallbackRequests O) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedShortCircuitNodeWithRead?
        T O (input.localizedDependencyView state T)
        (input.localizedWholeStateReader state) before excluded =
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        T O (input.localizedDependencyView state T) after excluded := by
  rw [input.localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_restricted_of_deeper
    O T deeper state before after callbackAgree excluded]
  exact
    input.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel
      T O (input.localizedDependencyView state T) after excluded

/-- **Direct wrapper specialization at the shipped recursive frame callback.**  Instantiating the
callback of the equal-callback theorem with the actual executable extended frame builder at an
arbitrary budget keeps the same full `Option` equality between the whole-state parametric node and
the shipped executable node, at the actual restricted dependency view.  This is the exact shape of
the callback that the shipped recursive extended node supplies at successor fuel. -/
theorem localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_Exec?_of_deeper_extendedFrameExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (budget : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedShortCircuitNodeWithRead?
        T O (input.localizedDependencyView state T)
        (input.localizedWholeStateReader state)
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          T (input.localizedDependencyView state T) budget) excluded =
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        T O (input.localizedDependencyView state T)
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          T (input.localizedDependencyView state T) budget) excluded :=
  input.localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_Exec?_of_deeper
    O T deeper state
    (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      T (input.localizedDependencyView state T) budget)
    excluded

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ExtendedNodeCallbackRequests_mem_short
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ExtendedActualRequest_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ExtendedNodeCallbackRequests_nil_of_jointRouteCertificateNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootReadersAgreeOnRequests_of_extendedActualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_restricted_of_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_Exec?_of_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_Exec?_of_deeper_of_callbackAgree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?_wholeState_eq_Exec?_of_deeper_extendedFrameExec
