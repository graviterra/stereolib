import TetraStereo.OneCenter.LocalizedExtendedActualRequestLocality
import TetraStereo.OneCenter.LocalizedParametricExtendedRule3Key
import TetraStereo.OneCenter.LocalizedRule3ActualDemandReaderLocality
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



































































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Generic `List.mapM` congruence -/

/-- Pointwise agreement on the members of a list lifts through `List.mapM`.  Membership is enough
because `mapM` only applies the function to list members. -/
private theorem list_mapM_congr_on {α β : Type*}
    (first second : α → Option β) :
    ∀ values : List α,
      (∀ value, value ∈ values → first value = second value) →
      values.mapM first = values.mapM second
  | [], _ => rfl
  | value :: values, agrees => by
      simp [List.mapM_cons, agrees value (by simp),
        list_mapM_congr_on first second values
          (fun member memberPresent => agrees member (by simp [memberPresent]))]

/-! ## The mutual fuel induction -/

/-- **Mutual whole-state/restricted locality of the extended key and frame.**

`requestOutward` is the honest actual request support: for every strict dependency `O` of the
descriptor target, every cursor occurring in every request actually emitted by the extended node
demand `rule3ExtendedNodeCallbackRequests O` is outward of the target.  It is discharged below by
`rule3ExtendedActualRequest_outward`.

The two conclusions are:

* at every exclusion list, every fuel and every outward cursor, the extended key built through the
  unrestricted whole-state reader equals the extended key built through the restricted dependency
  reader;
* at every fuel and every frame list all of whose cursors are outward, the two-pass frame built
  through the whole-state reader equals the frame built through the restricted dependency reader.

The induction is on the actual shared structural fuel.  It uses no equality of built keys and no
successful-callback or successful-geometry premise. -/
theorem recursive_compilers_extended_wholeState_eq_restricted_of_requestOutward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (requestOutward : ∀ (O : input.LocalizedCIPOccurrence carrierFuel),
      input.LocalizedDepthDependency O target →
      ∀ request ∈ input.rule3ExtendedNodeCallbackRequests O,
        ∀ cursor ∈ request, OutwardRerootCursor input target cursor)
    (fuel : Nat) :
    (∀ (excluded : List input.LocalizedRule3PhysicalUnitId)
        (cursor : input.LocalizedRerootCursor carrierFuel),
        OutwardRerootCursor input target cursor →
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
            (input.localizedDependencyView state target)
            (input.localizedWholeStateReader state) fuel excluded cursor =
          input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
            (input.localizedDependencyView state target)
            (fun cursor => input.localizedDependencyLabel target
              (input.localizedDependencyView state target) cursor) fuel excluded cursor) ∧
    (∀ (cursors : List (input.LocalizedRerootCursor carrierFuel)),
        (∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) →
        input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
            (input.localizedDependencyView state target)
            (input.localizedWholeStateReader state) fuel cursors =
          input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
            (input.localizedDependencyView state target)
            (fun cursor => input.localizedDependencyLabel target
              (input.localizedDependencyView state target) cursor) fuel cursors) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro excluded cursor _outward
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?]
      · intro cursors _allOutward
        simp only [buildLocalizedExtendedShortCircuitRule3FrameWithRead?]
  | succ fuel ih =>
      obtain ⟨ihKey, ihFrame⟩ := ih
      refine ⟨?_, ?_⟩
      · /- ## Key at successor fuel -/
        intro excluded cursor outward
        have requestsOutward :
            ∀ request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence,
              ∀ member ∈ request, OutwardRerootCursor input target member :=
          requestOutward cursor.occurrence outward.2.1
        /- The predecessor frames agree on every actual request list, because every request list
        is outward. -/
        have callbackAgree : input.Rule3CallbackAgreesOn
            (input.rule3ExtendedNodeCallbackRequests cursor.occurrence)
            (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
              (input.localizedDependencyView state target)
              (input.localizedWholeStateReader state) fuel)
            (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
              (input.localizedDependencyView state target)
              (fun cursor => input.localizedDependencyLabel target
                (input.localizedDependencyView state target) cursor) fuel) := by
          intro cursors requested
          exact ihFrame cursors
            (fun cursor cursorMember => requestsOutward cursors requested cursor cursorMember)


        have nodeEq :
            input.localizedRule3ExtendedShortCircuitNodeWithRead?
                target cursor.occurrence (input.localizedDependencyView state target)
                (input.localizedWholeStateReader state)
                (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
                  (input.localizedDependencyView state target)
                  (input.localizedWholeStateReader state) fuel)
                excluded =
              input.localizedRule3ExtendedShortCircuitNodeWithRead?
                target cursor.occurrence (input.localizedDependencyView state target)
                (fun cursor => input.localizedDependencyLabel target
                  (input.localizedDependencyView state target) cursor)
                (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
                  (input.localizedDependencyView state target)
                  (fun cursor => input.localizedDependencyLabel target
                    (input.localizedDependencyView state target) cursor) fuel)
                excluded :=
          input.localizedRule3ExtendedShortCircuitNodeWithRead?_congr_of_callbackAgree
            target cursor.occurrence (input.localizedDependencyView state target)
            (input.localizedWholeStateReader state)
            (fun cursor => input.localizedDependencyLabel target
              (input.localizedDependencyView state target) cursor)
            (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
              (input.localizedDependencyView state target)
              (input.localizedWholeStateReader state) fuel)
            (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
              (input.localizedDependencyView state target)
              (fun cursor => input.localizedDependencyLabel target
                (input.localizedDependencyView state target) cursor) fuel)
            callbackAgree
            (input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors
              target state (input.rule3ExtendedNodeCallbackRequests cursor.occurrence)
              requestsOutward)
            excluded
        /- Every executable child of an outward cursor is outward, so the child key pass is the
        key induction hypothesis. -/
        have childrenEq : (input.executableLocalizedRerootChildren cursor).mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
                (input.localizedDependencyView state target)
                (input.localizedWholeStateReader state) fuel excluded) =
            (input.executableLocalizedRerootChildren cursor).mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
                (input.localizedDependencyView state target)
                (fun cursor => input.localizedDependencyLabel target
                  (input.localizedDependencyView state target) cursor) fuel excluded) := by
          refine list_mapM_congr_on _ _ _ ?_
          intro child present
          exact ihKey excluded child
            (input.outward_edge_preserves target cursor child outward present)
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?,
          executableLocalizedRerootChildren?_eq_some, bind, Option.bind,
          nodeEq, childrenEq]
      · /- ## Frame at successor fuel -/
        intro cursors allOutward
        /- The raw key pass has the same exclusion list `[]` on both sides. -/
        have rawEq : cursors.mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
                (input.localizedDependencyView state target)
                (input.localizedWholeStateReader state) fuel []) =
            cursors.mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
                (input.localizedDependencyView state target)
                (fun cursor => input.localizedDependencyLabel target
                  (input.localizedDependencyView state target) cursor) fuel []) :=
          list_mapM_congr_on _ _ cursors
            (fun cursor cursorMember => ihKey [] cursor (allOutward cursor cursorMember))
        /- Consequently the coupled topology resolution and the coupled excluded physical units
        are the same term on both sides, and the second key pass at that exclusion list is again
        the key induction hypothesis. -/
        have keysEq : ∀ (excluded : List input.LocalizedRule3PhysicalUnitId),
            cursors.mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
                (input.localizedDependencyView state target)
                (input.localizedWholeStateReader state) fuel excluded) =
            cursors.mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
                (input.localizedDependencyView state target)
                (fun cursor => input.localizedDependencyLabel target
                  (input.localizedDependencyView state target) cursor) fuel excluded) :=
          fun excluded => list_mapM_congr_on _ _ cursors
            (fun cursor cursorMember => ihKey excluded cursor (allOutward cursor cursorMember))
        simp only [buildLocalizedExtendedShortCircuitRule3FrameWithRead?, rawEq, keysEq]

/-! ## Actual request support -/

/-- The actual extended request support of `LocalizedExtendedActualRequestLocality`, restated at
exactly the shape consumed by the mutual induction: for every strict dependency occurrence of the
target, every cursor in every actual extended request list is outward of the target. -/
theorem extendedActualRequestsOutward_of_deeper
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    ∀ (O : input.LocalizedCIPOccurrence carrierFuel),
      input.LocalizedDepthDependency O target →
      ∀ request ∈ input.rule3ExtendedNodeCallbackRequests O,
        ∀ cursor ∈ request, OutwardRerootCursor input target cursor :=
  fun O deeper => input.rule3ExtendedActualRequest_outward O target deeper

/-! ## Key locality -/

/-- **Whole-state versus restricted extended key on an outward cursor.**  Full `Option` equality
of the extended recursive key at every fuel, exclusion list and outward cursor, between the
unrestricted whole-state reader and the shipped restricted dependency reader. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_restricted_of_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (outward : OutwardRerootCursor input target cursor) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel excluded cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
        (input.localizedDependencyView state target)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor) fuel excluded cursor :=
  (recursive_compilers_extended_wholeState_eq_restricted_of_requestOutward input target state
    (input.extendedActualRequestsOutward_of_deeper target) fuel).1 excluded cursor outward

/-! ## Frame locality -/

/-- **Whole-state versus restricted two-pass frame on an all-outward cursor list.**  Full
`Option` equality of the extended frame at every fuel and every list all of whose cursors are
outward.  The exclusion pass and the coupled topology resolution are the actual ones; no topology
or successful-key premise is assumed. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameWithRead?_wholeState_eq_restricted_of_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (allOutward : ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
        (input.localizedDependencyView state target)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor) fuel cursors :=
  (recursive_compilers_extended_wholeState_eq_restricted_of_requestOutward input target state
    (input.extendedActualRequestsOutward_of_deeper target) fuel).2 cursors allOutward

/-! ## Recursive node locality -/





theorem localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_restricted_of_deeper
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency occurrence target)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedExtendedShortCircuitRule3NodeWithRead? target occurrence
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel excluded =
      input.localizedExtendedShortCircuitRule3NodeWithRead? target occurrence
        (input.localizedDependencyView state target)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor) fuel excluded := by
  cases fuel with
  | zero =>
      simp only [localizedExtendedShortCircuitRule3NodeWithRead?]
  | succ fuel =>
      have requestsOutward :
          ∀ request ∈ input.rule3ExtendedNodeCallbackRequests occurrence,
            ∀ member ∈ request, OutwardRerootCursor input target member :=
        input.rule3ExtendedActualRequest_outward occurrence target deeper
      have callbackAgree : input.Rule3CallbackAgreesOn
          (input.rule3ExtendedNodeCallbackRequests occurrence)
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
            (input.localizedDependencyView state target)
            (input.localizedWholeStateReader state) fuel)
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
            (input.localizedDependencyView state target)
            (fun cursor => input.localizedDependencyLabel target
              (input.localizedDependencyView state target) cursor) fuel) := by
        intro cursors requested
        exact
          (recursive_compilers_extended_wholeState_eq_restricted_of_requestOutward input target
            state (input.extendedActualRequestsOutward_of_deeper target) fuel).2 cursors
            (fun cursor cursorMember => requestsOutward cursors requested cursor cursorMember)
      simp only [localizedExtendedShortCircuitRule3NodeWithRead?]
      exact input.localizedRule3ExtendedShortCircuitNodeWithRead?_congr_of_callbackAgree
        target occurrence (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor)
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
          (input.localizedDependencyView state target)
          (input.localizedWholeStateReader state) fuel)
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
          (input.localizedDependencyView state target)
          (fun cursor => input.localizedDependencyLabel target
            (input.localizedDependencyView state target) cursor) fuel)
        callbackAgree
        (input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors
          target state (input.rule3ExtendedNodeCallbackRequests occurrence) requestsOutward)
        excluded

/-! ## Whole-state versus shipped executable

The restricted-dependency parametric recursion is exactly the shipped executable recursion by the
unconditional specializations of `LocalizedParametricExtendedRule3Key`.  Composing with the
restricted equalities above yields whole-state versus executable equality, including every
fail-closed `none`. -/

/-- **Whole-state versus executable extended key.** -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_Exec?_of_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (outward : OutwardRerootCursor input target cursor) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel excluded cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target
        (input.localizedDependencyView state target) fuel excluded cursor :=
  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_restricted_of_outward
      target state fuel excluded cursor outward).trans
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_eq_buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_of_localizedDependencyLabel
      target (input.localizedDependencyView state target) fuel excluded cursor)

/-- **Whole-state versus executable two-pass frame.** -/
theorem buildLocalizedExtendedShortCircuitRule3FrameWithRead?_wholeState_eq_Exec?_of_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (allOutward : ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target
        (input.localizedDependencyView state target) fuel cursors :=
  (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_wholeState_eq_restricted_of_outward
      target state fuel cursors allOutward).trans
    (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_eq_buildLocalizedExtendedShortCircuitRule3FrameExec?_of_localizedDependencyLabel
      target (input.localizedDependencyView state target) fuel cursors)

/-- **Whole-state versus executable recursive extended node.** -/
theorem localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_Exec?_of_deeper
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency occurrence target)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedExtendedShortCircuitRule3NodeWithRead? target occurrence
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel excluded =
      input.localizedExtendedShortCircuitRule3NodeExec? target occurrence
        (input.localizedDependencyView state target) fuel excluded :=
  (input.localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_restricted_of_deeper
      target occurrence deeper state fuel excluded).trans
    (input.localizedExtendedShortCircuitRule3NodeWithRead?_eq_localizedExtendedShortCircuitRule3NodeExec?_of_localizedDependencyLabel
      target occurrence (input.localizedDependencyView state target) fuel excluded)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the generic mutual induction, the actual request-support interface,
the key and frame restricted equalities, the recursive node restricted equality, and the three
whole-state versus executable equalities.  The request support is the proved actual statement of
`LocalizedExtendedActualRequestLocality`, not an assumption. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.recursive_compilers_extended_wholeState_eq_restricted_of_requestOutward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedActualRequestsOutward_of_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_restricted_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_wholeState_eq_restricted_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_restricted_of_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_Exec?_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_wholeState_eq_Exec?_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_Exec?_of_deeper
