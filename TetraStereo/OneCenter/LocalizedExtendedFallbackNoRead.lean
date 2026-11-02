import TetraStereo.OneCenter.LocalizedParametricExtendedRule3Key
import TetraStereo.OneCenter.LocalizedRule3NodeCallbackDemand
import TetraStereo.OneCenter.LocalizedRule3OriginalSpatialExecutable
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness
import TetraStereo.OneCenter.LocalizedActualMonocycleFallbackExclusion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Extended Rule-3 fallback without hidden restricted reads

`LocalizedParametricExtendedRule3Key` exposes the extended Rule-3 node with one parameterized
direct Rules-4/5 label reader.  On an occurrence whose executable route certificates are both
`none` (neither the ordinary individual-bond route nor the planar odd-cumulene route applies) the
parametric node delegates to the actual original/eager evaluator
`localizedDescriptorBearingRule3NodeWithExec?`, which has no reader parameter.  This module proves
that on that actual guarded branch the original evaluator is *completely insensitive* to the
target, the dependency view, the Rule-3 callback and the exclusion list, and that it issues no
Rule-3 callback requests at all.

The route coverage is exactly the executable one:

* a `branched` cumulative-axis entry would make `localizedRule3OrdinaryRouteCertificate?` return
  `some`, so joint `none` excludes it;
* a `terminalStart` entry with `doubleBondCount = 1` would also make the ordinary certificate
  return `some`;
* a `terminalStart` entry with `doubleBondCount ≠ 1` and `Odd doubleBondCount` would make
  `localizedRule3OddRouteCertificate?` return `some`;
* the remaining non-ring cases are `¬ edge` (original node returns `some none`), `internal` (also
  `some none`), a failing entry/topology lookup (original node returns `none`) and an even
  non-ordinary terminal axis (also `some none`).  None of them reads a callback, a Rule-4/5 label,
  a target or an exclusion list;
* a `ringClosure` entry is excluded from monocyclic perception by the actual declarative ring
  closure theorem of `LocalizedActualMonocycleFallbackExclusion`: the cyclic authority route is
  then either `fullyCyclicCumulene` or `ordinaryNonmonocyclic`, both of which make the required
  monocyclic EZ evaluator return `none` before any endpoint or Rule-4/5 read, and the ring branch
  of the original node then returns `none` without reading the exclusion list.

Consequently, under joint route-certificate failure, the original fallback is one fixed `Option`
value across *all* targets, views, callbacks, readers and exclusion lists (an exact `Option`
equality, not merely `isSome`), and its callback-request list is empty.  The final corollary
transfers this to the parametric extended node itself: on that actual guarded branch the
parameterized reader is never consulted, so no reader parameterization is needed there.

## Main results

* `localizedDescriptorBearingRule3NodeWithExec?_eq_none_of_ringClosureEntry` — an actual
  `ringClosure` entry forces the original eager node to `none`, for every target, view, callback
  and exclusion list.
* `localizedDescriptorBearingRule3NodeWithExec?_eq_of_jointRouteCertificateNone` — joint
  ordinary/odd route-certificate failure makes the original eager node's exact `Option` result
  independent of both targets, both views, both callbacks and both exclusion lists.
* `rule3OriginalNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone` — under the same joint
  failure the original node enumerates no Rule-3 callback requests at all.
* `rule3NodeCallbackRequests_eq_nil_of_jointRouteCertificateNone` and
  `rule3ExtendedNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone` — the ordinary and the
  extended node seams enumerate no callback requests either, so the request-local reader
  congruence of the parametric seam has no retained request to certify on this branch.
* `localizedRule3ShortCircuitNodeWithRead?_eq_of_jointRouteCertificateNone` — the ordinary node
  seam is exactly independent of both readers and of every remaining parameter.
* `localizedRule3ExtendedShortCircuitNodeWithRead?_eq_of_jointRouteCertificateNone` — the
  parametric extended node of `LocalizedParametricExtendedRule3Key` is exactly equal for arbitrary
  readers, targets, views, callbacks and exclusion lists on that actual guarded branch.
* `localizedExtendedShortCircuitRule3NodeWithRead?_eq_of_jointRouteCertificateNone` — the same
  exact independence at every fuel index of the recursive extended node.

## Kernel authority

Every exported declaration is guarded by `assert_kernel_only`.  The only input from the sibling
module is the actual declarative ring-closure exclusion
`localizedMonocyclicDoubleBondAt?_eq_none_of_declarativeRingClosure` of the terminal-green sibling
`LocalizedActualMonocycleFallbackExclusion`.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-! ## Executable route-case algebra -/

/-- A successful executable cumulative-axis entry forces the real physical order-two edge that is
the outer guard of the original eager node.  The endpoint frame underlying the entry is recovered
from its executable twin and its declarative soundness. -/
theorem localizedOccurrenceHasRule3DoubleBondEdge_of_cumulatedAxisEntryExec?_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {entry : input.LocalizedRule3CumulatedAxisEntry carrierFuel}
    (computed : input.localizedRule3CumulatedAxisEntryExec? occurrence = some entry) :
    input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  unfold localizedRule3CumulatedAxisEntryExec? at computed
  cases frameComputed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp [frameComputed] at computed
  | some frame =>
      have originalComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence =
          some frame :=
        (input.localizedRule3PhysicalEndpointCursorFrameExec?_eq_original occurrence).symm.trans
          frameComputed
      have derived :=
        input.localizedRule3PhysicalEndpointCursorFrame?_sound occurrence frame originalComputed
      exact ⟨derived.1, frame.right, frame.left, derived.2.1, derived.2.2.1,
        derived.2.2.2.1⟩

/-- A successful executable `ringClosure` entry carries the actual declarative cumulated-axis
entry at the same endpoint frame and closure cursor. -/
theorem declarativeLocalizedRule3CumulatedAxisEntry_of_exec?_ringClosure
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.ringClosure initial closure)) :
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
      (.ringClosure initial closure) := by
  have originalEntry : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure) :=
    (input.localizedRule3CumulatedAxisEntryExec?_eq_original occurrence).symm.trans entry
  exact input.localizedRule3CumulatedAxisEntry?_sound occurrence
    (.ringClosure initial closure) originalEntry

/-- An actual executable `ringClosure` entry excludes exact monocyclic double-bond perception at
the oriented endpoint bond.  This is the executable form of the sibling module's declarative
ring-closure exclusion. -/
theorem localizedMonocyclicDoubleBondAtExec?_eq_none_of_ringClosureEntry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.ringClosure initial closure)) :
    input.localizedMonocyclicDoubleBondAtExec? initial.left initial.right = none := by
  have derived :=
    declarativeLocalizedRule3CumulatedAxisEntry_of_exec?_ringClosure input occurrence entry
  have originalNone :=
    input.localizedMonocyclicDoubleBondAt?_eq_none_of_declarativeRingClosure
      occurrence initial closure derived
  rw [input.localizedMonocyclicDoubleBondAtExec?_eq_original]
  exact originalNone

/-- Under an actual ring closure with failed monocyclic perception, the executable cyclic
authority route is either the fully cyclic cumulene route or the ordinary nonmonocyclic route.  In
particular it is never an `ordinaryMonocyclicPolicy` route. -/
theorem localizedRule3CyclicAuthorityRouteExec?_eq_of_ringClosureEntry_ringNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.ringClosure initial closure))
    (ringNone : input.localizedMonocyclicDoubleBondAtExec? initial.left initial.right = none) :
    input.localizedRule3CyclicAuthorityRouteExec? occurrence =
      match input.localizedCyclicCumuleneComponentContainingExec? initial.left with
      | none => some (.ordinaryNonmonocyclic initial closure)
      | some component => some (.fullyCyclicCumulene initial closure component) := by
  unfold localizedRule3CyclicAuthorityRouteExec?
  unfold localizedRule3RingClosureMoleculeRouteExec?
  cases hcomponent : input.localizedCyclicCumuleneComponentContainingExec? initial.left with
  | none => simp [entry, hcomponent, ringNone]
  | some component => simp [entry, hcomponent]

/-- Under an actual ring closure with failed monocyclic perception, the required monocyclic EZ
evaluator returns `none` before consulting its endpoint key-frame callback.  Both possible cyclic
authority routes (`fullyCyclicCumulene` and `ordinaryNonmonocyclic`) are immediate refusals. -/
theorem localizedRule3RequiredMonocyclicEZWithExec?_eq_none_of_ringClosureEntry_ringNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.ringClosure initial closure))
    (ringNone : input.localizedMonocyclicDoubleBondAtExec? initial.left initial.right = none) :
    input.localizedRule3RequiredMonocyclicEZWithExec? target occurrence view callback = none := by
  unfold localizedRule3RequiredMonocyclicEZWithExec?
  rw [localizedRule3CyclicAuthorityRouteExec?_eq_of_ringClosureEntry_ringNone
    input occurrence entry ringNone]
  cases hcomponent : input.localizedCyclicCumuleneComponentContainingExec? initial.left with
  | none => simp [hcomponent]
  | some component => simp [hcomponent]

/-- Under an actual ring closure with failed monocyclic perception, the original node's ring
callback-request list is empty: the route is never `ordinaryMonocyclicPolicy`, so no endpoint
request is emitted. -/
theorem rule3RingCallbackRequests_eq_nil_of_ringClosureEntry_ringNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.ringClosure initial closure))
    (ringNone : input.localizedMonocyclicDoubleBondAtExec? initial.left initial.right = none) :
    input.rule3RingCallbackRequests occurrence = [] := by
  unfold rule3RingCallbackRequests
  rw [localizedRule3CyclicAuthorityRouteExec?_eq_of_ringClosureEntry_ringNone
    input occurrence entry ringNone]
  cases hcomponent : input.localizedCyclicCumuleneComponentContainingExec? initial.left with
  | none => simp [hcomponent]
  | some component => simp [hcomponent]

/-! ## The three route branches eliminated by the ordinary certificate -/

/-- A `branched` entry with the real edge guard makes the executable ordinary route certificate
return `some`, contradicting its failure. -/
theorem false_of_ordinaryRouteCertificate?_eq_none_of_branched
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (noneEq : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {first second : input.LocalizedRerootCursor carrierFuel}
    {rest : List (input.LocalizedRerootCursor carrierFuel)}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.branched initial first second rest)) :
    False := by
  have originalEntry : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.branched initial first second rest) :=
    (input.localizedRule3CumulatedAxisEntryExec?_eq_original occurrence).symm.trans entry
  have derived := input.localizedRule3CumulatedAxisEntry?_sound occurrence
    (.branched initial first second rest) originalEntry
  have route : input.LocalizedRule3OrdinaryRoute occurrence :=
    ⟨edge, Or.inl ⟨initial, first, second, rest, derived⟩⟩
  have detected :=
    input.localizedRule3OrdinaryRouteCertificate?_isSome_of_route occurrence route
  rw [noneEq] at detected
  simp at detected

/-- A one-double-bond terminal axis with the real edge guard makes the executable ordinary route
certificate return `some`, contradicting its failure. -/
theorem false_of_ordinaryRouteCertificate?_eq_none_of_terminalOrdinary
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (noneEq : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.terminalStart initial))
    {axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel}
    (frame : input.localizedRule3CumulatedEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
    (ordinary : axis.doubleBondCount = 1) :
    False := by
  have originalFrame : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis :=
    (input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_original
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence).symm.trans frame
  have derived := input.localizedRule3CumulatedEndpointCursorFrame?_sound
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence axis originalFrame
  have route : input.LocalizedRule3OrdinaryRoute occurrence :=
    ⟨edge, Or.inr ⟨axis, derived, ordinary⟩⟩
  have detected :=
    input.localizedRule3OrdinaryRouteCertificate?_isSome_of_route occurrence route
  rw [noneEq] at detected
  simp at detected

/-- A terminal nonordinary odd axis with the real edge guard makes the executable odd route
certificate return `some`, contradicting its failure. -/
theorem false_of_oddRouteCertificate?_eq_none_of_terminalOdd
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (noneEq : input.localizedRule3OddRouteCertificate? occurrence = none)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.terminalStart initial))
    {axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel}
    (frame : input.localizedRule3CumulatedEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
    (notOrdinary : axis.doubleBondCount ≠ 1)
    (odd : Odd axis.doubleBondCount) :
    False := by
  have originalFrame : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis :=
    (input.localizedRule3CumulatedEndpointCursorFrameExec?_eq_original
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence).symm.trans frame
  have derived := input.localizedRule3CumulatedEndpointCursorFrame?_sound
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence axis originalFrame
  have route : input.LocalizedRule3OddRoute occurrence :=
    ⟨edge, axis, derived, notOrdinary, odd⟩
  have detected :=
    input.localizedRule3OddRouteCertificate?_isSome_of_route occurrence route
  rw [noneEq] at detected
  simp at detected

/-! ## Export 1: an actual ring closure forces the original node to `none` -/

/-- **Ring-closure fallback refusal.**  If the executable cumulative-axis entry is an actual
`ringClosure`, then the original/eager descriptor-bearing node returns `none` for every target,
dependency view, Rule-3 callback and exclusion list.  The excluded physical unit is never
consulted: the required monocyclic EZ evaluator refuses at the cyclic authority route and the
route itself is `fullyCyclicCumulene` or `ordinaryNonmonocyclic`. -/
theorem localizedDescriptorBearingRule3NodeWithExec?_eq_none_of_ringClosureEntry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (entry : input.localizedRule3CumulatedAxisEntryExec? occurrence =
      some (.ringClosure initial closure)) :
    input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view callback excluded = none := by
  have edge :=
    localizedOccurrenceHasRule3DoubleBondEdge_of_cumulatedAxisEntryExec?_some
      input occurrence entry
  have ringNone :=
    localizedMonocyclicDoubleBondAtExec?_eq_none_of_ringClosureEntry
      input occurrence entry
  have requiredNone :=
    localizedRule3RequiredMonocyclicEZWithExec?_eq_none_of_ringClosureEntry_ringNone
      input target occurrence view callback entry ringNone
  have routeEq :=
    localizedRule3CyclicAuthorityRouteExec?_eq_of_ringClosureEntry_ringNone
      input occurrence entry ringNone
  unfold localizedDescriptorBearingRule3NodeWithExec?
  simp only [dif_pos edge, entry, requiredNone, routeEq]
  cases hcomponent : input.localizedCyclicCumuleneComponentContainingExec? initial.left <;>
    simp [hcomponent]

/-! ## Export 2: joint route-certificate failure makes the original node fully independent -/

/-- **Joint-failure independence of the original fallback.**  If neither the ordinary
individual-bond route certificate nor the planar odd-cumulene route certificate is available,
then the original/eager descriptor-bearing node has exactly the same `Option` result for arbitrary
targets, dependency views, Rule-3 callbacks and exclusion lists.  This is an exact `Option`
equality, not a statement about `isSome`.  Both route certificates are necessary: with the
ordinary certificate alone, an odd terminal axis still reads its endpoint callbacks and Rule-4/5
labels. -/
theorem localizedDescriptorBearingRule3NodeWithExec?_eq_of_jointRouteCertificateNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target₁ target₂ : input.LocalizedCIPOccurrence carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view₁ : input.LocalizedDependencyView target₁)
    (view₂ : input.LocalizedDependencyView target₂)
    (callback₁ callback₂ : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded₁ excluded₂ : List input.LocalizedRule3PhysicalUnitId)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none) :
    input.localizedDescriptorBearingRule3NodeWithExec?
        target₁ occurrence view₁ callback₁ excluded₁ =
      input.localizedDescriptorBearingRule3NodeWithExec?
        target₂ occurrence view₂ callback₂ excluded₂ := by
  unfold localizedDescriptorBearingRule3NodeWithExec?
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · simp only [dif_pos edge]
    cases entry : input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | none => rfl
    | some value =>
        cases value with
        | internal initial previousAxis => rfl
        | branched initial first second rest =>
            exact False.elim
              (false_of_ordinaryRouteCertificate?_eq_none_of_branched
                input occurrence ordinaryNone edge entry)
        | ringClosure initial closure =>
            have ringNone :=
              localizedMonocyclicDoubleBondAtExec?_eq_none_of_ringClosureEntry
                input occurrence entry
            have requiredNone₁ :=
              localizedRule3RequiredMonocyclicEZWithExec?_eq_none_of_ringClosureEntry_ringNone
                input target₁ occurrence view₁ callback₁ entry ringNone
            have requiredNone₂ :=
              localizedRule3RequiredMonocyclicEZWithExec?_eq_none_of_ringClosureEntry_ringNone
                input target₂ occurrence view₂ callback₂ entry ringNone
            have routeEq :=
              localizedRule3CyclicAuthorityRouteExec?_eq_of_ringClosureEntry_ringNone
                input occurrence entry ringNone
            simp only [entry, requiredNone₁, requiredNone₂, routeEq]
        | terminalStart initial =>
            dsimp only
            cases frame : input.localizedRule3CumulatedEndpointCursorFrameExec?
                (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
            | none => rfl
            | some axis =>
                dsimp only
                by_cases ordinary : axis.doubleBondCount = 1
                · exact False.elim
                    (false_of_ordinaryRouteCertificate?_eq_none_of_terminalOrdinary
                      input occurrence ordinaryNone edge entry frame ordinary)
                · simp only [dif_neg ordinary]
                  by_cases odd : Odd axis.doubleBondCount
                  · exact False.elim
                      (false_of_oddRouteCertificate?_eq_none_of_terminalOdd
                        input occurrence oddNone edge entry frame ordinary odd)
                  · simp only [dif_neg odd]
  · simp only [dif_neg edge]

/-! ## Export 3: under joint failure the original node enumerates no callback request -/

/-- **Empty original callback demand.**  If both executable route certificates fail, the original
eager node's potential callback-request list is empty.  The branched, ordinary-terminal and odd
terminal branches are impossible by the certificates; the ring-closure branch emits no request
because monocyclic perception is refused by the actual declarative ring closure. -/
theorem rule3OriginalNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none) :
    input.rule3OriginalNodeCallbackRequests occurrence = [] := by
  unfold rule3OriginalNodeCallbackRequests
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · simp only [if_pos edge]
    cases entry : input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | none => rfl
    | some value =>
        cases value with
        | internal initial previousAxis => rfl
        | branched initial first second rest =>
            exact False.elim
              (false_of_ordinaryRouteCertificate?_eq_none_of_branched
                input occurrence ordinaryNone edge entry)
        | ringClosure initial closure =>
            have ringNone :=
              localizedMonocyclicDoubleBondAtExec?_eq_none_of_ringClosureEntry
                input occurrence entry
            exact rule3RingCallbackRequests_eq_nil_of_ringClosureEntry_ringNone
              input occurrence entry ringNone
        | terminalStart initial =>
            dsimp only
            cases frame : input.localizedRule3CumulatedEndpointCursorFrameExec?
                (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
            | none => rfl
            | some axis =>
                dsimp only
                by_cases ordinary : axis.doubleBondCount = 1
                · exact False.elim
                    (false_of_ordinaryRouteCertificate?_eq_none_of_terminalOrdinary
                      input occurrence ordinaryNone edge entry frame ordinary)
                · simp only [if_neg ordinary]
                  by_cases odd : Odd axis.doubleBondCount
                  · exact False.elim
                      (false_of_oddRouteCertificate?_eq_none_of_terminalOdd
                        input occurrence oddNone edge entry frame ordinary odd)
                  · simp only [if_neg odd]
  · simp only [if_neg edge]

/-- **Empty ordinary-node callback demand.**  The ordinary short-circuit node's request list also
vanishes under joint route-certificate failure, since it then coincides with the original node's
request list. -/
theorem rule3NodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none) :
    input.rule3NodeCallbackRequests occurrence = [] := by
  unfold rule3NodeCallbackRequests
  rw [ordinaryNone]
  exact rule3OriginalNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
    input occurrence ordinaryNone oddNone

/-- **Empty extended-node callback demand.**  The extended short-circuit node's request list also
vanishes under joint route-certificate failure: the failed odd certificate delegates to the
ordinary node, whose failed ordinary certificate delegates to the request-free original node.  In
particular the parametric extended seam's request-local reader congruence has no retained request
to certify on this branch. -/
theorem rule3ExtendedNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none) :
    input.rule3ExtendedNodeCallbackRequests occurrence = [] := by
  unfold rule3ExtendedNodeCallbackRequests
  rw [oddNone]
  exact rule3NodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
    input occurrence ordinaryNone oddNone

/-- **Reader independence of the ordinary node seam.**  The ordinary short-circuit node seam is
likewise exactly independent of both readers, targets, views, callbacks and exclusion lists under
joint route-certificate failure: its own ordinary certificate fails, so it falls through to the
original eager evaluator handled by Export 2. -/
theorem localizedRule3ShortCircuitNodeWithRead?_eq_of_jointRouteCertificateNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target₁ target₂ : input.LocalizedCIPOccurrence carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view₁ : input.LocalizedDependencyView target₁)
    (view₂ : input.LocalizedDependencyView target₂)
    (read₁ read₂ : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (callback₁ callback₂ : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded₁ excluded₂ : List input.LocalizedRule3PhysicalUnitId)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none) :
    input.localizedRule3ShortCircuitNodeWithRead?
        target₁ occurrence view₁ read₁ callback₁ excluded₁ =
      input.localizedRule3ShortCircuitNodeWithRead?
        target₂ occurrence view₂ read₂ callback₂ excluded₂ := by
  unfold localizedRule3ShortCircuitNodeWithRead?
  simp only [ordinaryNone]
  exact localizedDescriptorBearingRule3NodeWithExec?_eq_of_jointRouteCertificateNone
    input target₁ target₂ occurrence view₁ view₂ callback₁ callback₂ excluded₁ excluded₂
    ordinaryNone oddNone

/-! ## Final corollary: no reader parameterization is needed on the guarded branch -/

/-- **Reader independence of the parametric extended node.**  On an occurrence where both route
certificates fail, the parametric extended Rule-3 node of
`LocalizedParametricExtendedRule3Key` is exactly equal for two arbitrary readers, targets,
dependency views, Rule-3 callbacks and exclusion lists.  The extended node delegates first past
the failed odd route to the ordinary node seam and then, past the failed ordinary route, to the
original eager fallback; by Export 2 that fallback is independent of all of these parameters.
Hence on this actual guarded branch the restricted Rules-4/5 reader is never consulted and no
reader parameterization is required. -/
theorem localizedRule3ExtendedShortCircuitNodeWithRead?_eq_of_jointRouteCertificateNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target₁ target₂ : input.LocalizedCIPOccurrence carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view₁ : input.LocalizedDependencyView target₁)
    (view₂ : input.LocalizedDependencyView target₂)
    (read₁ read₂ : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (callback₁ callback₂ : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded₁ excluded₂ : List input.LocalizedRule3PhysicalUnitId)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none) :
    input.localizedRule3ExtendedShortCircuitNodeWithRead?
        target₁ occurrence view₁ read₁ callback₁ excluded₁ =
      input.localizedRule3ExtendedShortCircuitNodeWithRead?
        target₂ occurrence view₂ read₂ callback₂ excluded₂ := by
  unfold localizedRule3ExtendedShortCircuitNodeWithRead?
  simp only [oddNone]
  simp only [localizedRule3ShortCircuitNodeWithRead?, ordinaryNone]
  exact localizedDescriptorBearingRule3NodeWithExec?_eq_of_jointRouteCertificateNone
    input target₁ target₂ occurrence view₁ view₂ callback₁ callback₂ excluded₁ excluded₂
    ordinaryNone oddNone

/-- **Reader independence of the fuel-indexed extended node.**  At every fuel index, the
parametric recursive extended node is exactly independent of both readers, targets, views and
exclusion lists under joint route-certificate failure.  At zero both sides are the shared
structural node; at a successor both sides call the extended node seam, which is independent by the
previous corollary regardless of the frame callbacks they pass. -/
theorem localizedExtendedShortCircuitRule3NodeWithRead?_eq_of_jointRouteCertificateNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target₁ target₂ : input.LocalizedCIPOccurrence carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view₁ : input.LocalizedDependencyView target₁)
    (view₂ : input.LocalizedDependencyView target₂)
    (read₁ read₂ : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat)
    (excluded₁ excluded₂ : List input.LocalizedRule3PhysicalUnitId)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none) :
    input.localizedExtendedShortCircuitRule3NodeWithRead?
        target₁ occurrence view₁ read₁ fuel excluded₁ =
      input.localizedExtendedShortCircuitRule3NodeWithRead?
        target₂ occurrence view₂ read₂ fuel excluded₂ := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [localizedExtendedShortCircuitRule3NodeWithRead?]
      exact localizedRule3ExtendedShortCircuitNodeWithRead?_eq_of_jointRouteCertificateNone
        input target₁ target₂ occurrence view₁ view₂ read₁ read₂
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target₁ view₁ read₁ fuel)
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target₂ view₂ read₂ fuel)
        excluded₁ excluded₂ ordinaryNone oddNone

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceHasRule3DoubleBondEdge_of_cumulatedAxisEntryExec?_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedRule3CumulatedAxisEntry_of_exec?_ringClosure
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedMonocyclicDoubleBondAtExec?_eq_none_of_ringClosureEntry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3CyclicAuthorityRouteExec?_eq_of_ringClosureEntry_ringNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3RequiredMonocyclicEZWithExec?_eq_none_of_ringClosureEntry_ringNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3RingCallbackRequests_eq_nil_of_ringClosureEntry_ringNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.false_of_ordinaryRouteCertificate?_eq_none_of_branched
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.false_of_ordinaryRouteCertificate?_eq_none_of_terminalOrdinary
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.false_of_oddRouteCertificate?_eq_none_of_terminalOdd
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDescriptorBearingRule3NodeWithExec?_eq_none_of_ringClosureEntry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDescriptorBearingRule3NodeWithExec?_eq_of_jointRouteCertificateNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3OriginalNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3NodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ExtendedNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitNodeWithRead?_eq_of_jointRouteCertificateNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_of_jointRouteCertificateNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeWithRead?_eq_of_jointRouteCertificateNone
