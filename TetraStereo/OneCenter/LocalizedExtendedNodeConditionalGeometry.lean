import TetraStereo.OneCenter.LocalizedExtendedNodePhysicalProjection
import TetraStereo.OneCenter.LocalizedRule3GeometryRefusalSync

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false









































































namespace TetraStereo.OneCenter

universe u

/-- The bind of a `some` value in the `Option` monad is definitionally the applied continuation.
The same private helper is used by the accepted endpoint and projection layers. -/
private theorem option_some_bind_apply
    {α β : Type u} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

namespace CertifiedLocalizedCIPInput

/-! ## Two-target endpoint synchronization from request-local callback facts

`LocalizedRule3GeometryRefusalSync` proves the short endpoint selector's `isSome` equality between
two callbacks at a *fixed* target and view.  `LocalizedExtendedNodePhysicalProjection` proves that,
at a *fixed* callback, the selector's `isSome` does not depend on the target, the view or the
reader.  Composing the two gives the two-target form needed by the node theorem: no endpoint
success, candidate shape or reference selection is assumed. -/

/-- **Two-target short endpoint synchronization.**  The two endpoint selectors at two arbitrary
targets, two arbitrary dependency views, two arbitrary readers and two arbitrary callbacks have
equal success flags under request-local callback agreement and conditional two-key shape on the
actual endpoint request list. -/
theorem localizedRule3ConditionalEndpointSelector_isSome_eq_of_targets
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor) after) :
    (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        targetOne viewOne readOne before endpoint partner endpointCursor).isSome =
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        targetTwo viewTwo readTwo after endpoint partner endpointCursor).isSome := by
  have sameTarget :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_callbackShape
      targetOne viewOne readOne readTwo before after endpoint partner endpointCursor
      isSomeAgree beforeShape afterShape
  have sameCallback :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_sameCallback
      targetOne targetTwo viewOne viewTwo readTwo readTwo after endpoint partner
      endpointCursor
  exact sameTarget.trans sameCallback

/-! ## The independent conditional geometry domain

The domain is route-indexed by the actual certificates of the occurrence.  On an executable route
it quantifies universally over the successful topology, the two candidate pairs and the four
selected reference cursors, and demands the four-pair candidate readiness only in the case where
all those structural facts actually hold.  Consequently a malformed list or a refused reference
selection is *inside* the domain.  On the joint-failure route the domain is `True`, because the
fallback performs no read at all. -/

/-- **The conditional geometry domain of one occurrence.**  For the actually chosen odd or ordinary
route, every successful executable topology with two candidate pairs and four selected reference
cursors carries the four-pair candidate readiness.  Structural failures satisfy the implication
vacuously. -/
def LocalizedRule3ExtendedNodeConditionalGeometryDomain
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | some _ =>
      ∀ (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
        (leftFirst leftSecond rightFirst rightSecond : input.Atom)
        (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
          input.LocalizedRerootCursor carrierFuel),
        input.localizedRule3OddCumuleneEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence =
              some topology →
          input.localizedRule3ExplicitSubstituents
              topology.initial.left topology.initial.right = [leftFirst, leftSecond] →
          input.localizedRule3ExplicitSubstituents
              topology.right topology.rightPartner = [rightFirst, rightSecond] →
          input.localizedRule3ReferenceCursorExec?
              topology.initial.leftCursor leftFirst = some leftFirstCursor →
          input.localizedRule3ReferenceCursorExec?
              topology.initial.leftCursor leftSecond = some leftSecondCursor →
          input.localizedRule3ReferenceCursorExec?
              topology.rightCursor rightFirst = some rightFirstCursor →
          input.localizedRule3ReferenceCursorExec?
              topology.rightCursor rightSecond = some rightSecondCursor →
          input.LocalizedRule3AxisCandidateGeometryReadiness
            topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
  | none =>
      match input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some _ =>
          ∀ (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
            (leftFirst leftSecond rightFirst rightSecond : input.Atom)
            (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
              input.LocalizedRerootCursor carrierFuel),
            input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence =
                some topology →
              input.localizedRule3ExplicitSubstituents
                  topology.left topology.right = [leftFirst, leftSecond] →
              input.localizedRule3ExplicitSubstituents
                  topology.right topology.left = [rightFirst, rightSecond] →
              input.localizedRule3ReferenceCursorExec?
                  topology.leftCursor leftFirst = some leftFirstCursor →
              input.localizedRule3ReferenceCursorExec?
                  topology.leftCursor leftSecond = some leftSecondCursor →
              input.localizedRule3ReferenceCursorExec?
                  topology.rightCursor rightFirst = some rightFirstCursor →
              input.localizedRule3ReferenceCursorExec?
                  topology.rightCursor rightSecond = some rightSecondCursor →
              input.LocalizedRule3AxisCandidateGeometryReadiness
                topology.left topology.right leftFirst leftSecond rightFirst rightSecond
      | none => True

/-- **The independent all-occurrence domain.**  Every occurrence satisfies the conditional geometry
domain.  There is no reachability premise, no fuel relation and no predecessor frame: a recursive
node step can instantiate this directly from its own exact predecessor-frame hypothesis. -/
def LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) : Prop :=
  ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
    input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence

/-! ## Canonical spatial identity from structural success and the domain

The two lemmas below are the single-side positive branch of the spatial case analysis.  Given the
actual successful topology, the two candidate pairs, the four selected reference cursors, both
successful endpoint selectors and the conditional geometry domain at the actual route, the spatial
wrapper is the canonical unordered physical identity.  They are also the API a recursive successor
can use directly when its predecessor frame supplies the structural facts. -/

/-- The ordinary spatial wrapper's projected identity at a structurally successful endpoint pair
is the canonical physical identity, under the conditional geometry domain.  The physical double
bond is derived from the actual topology frame, not assumed. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
      input.LocalizedRerootCursor carrierFuel)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none)
    (routed : input.localizedRule3OrdinaryRouteCertificate? occurrence = some certificate)
    (leftCandidates : input.localizedRule3ExplicitSubstituents
      topology.left topology.right = [leftFirst, leftSecond])
    (rightCandidates : input.localizedRule3ExplicitSubstituents
      topology.right topology.left = [rightFirst, rightSecond])
    (leftFirstSelected : input.localizedRule3ReferenceCursorExec?
      topology.leftCursor leftFirst = some leftFirstCursor)
    (leftSecondSelected : input.localizedRule3ReferenceCursorExec?
      topology.leftCursor leftSecond = some leftSecondCursor)
    (rightFirstSelected : input.localizedRule3ReferenceCursorExec?
      topology.rightCursor rightFirst = some rightFirstCursor)
    (rightSecondSelected : input.localizedRule3ReferenceCursorExec?
      topology.rightCursor rightSecond = some rightSecondCursor)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.left topology.right topology.leftCursor =
        some leftEndpoint)
    (rightComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.left topology.rightCursor =
        some rightEndpoint)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf =
      some (input.localizedRule3PhysicalUnitId topology.left topology.right) := by
  have candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.left topology.right leftFirst leftSecond rightFirst rightSecond := by
    unfold LocalizedRule3ExtendedNodeConditionalGeometryDomain at geometry
    simp only [oddNone, routed] at geometry
    exact geometry topology leftFirst leftSecond rightFirst rightSecond leftFirstCursor
      leftSecondCursor rightFirstCursor rightSecondCursor found leftCandidates
      rightCandidates leftFirstSelected leftSecondSelected rightFirstSelected
      rightSecondSelected
  have ready : input.LocalizedRule3AxisGeometryReadiness
      topology.left topology.right leftEndpoint.priority rightEndpoint.priority :=
    input.localizedRule3AxisGeometryReadiness_of_candidates
      topology.left topology.right leftFirst leftSecond rightFirst rightSecond
      leftEndpoint.priority rightEndpoint.priority candidateReady
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
        target view read rule3FrameOf topology.left topology.right leftFirst leftSecond
        topology.leftCursor leftCandidates leftEndpoint leftComputed)
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
        target view read rule3FrameOf topology.right topology.left rightFirst rightSecond
        topology.rightCursor rightCandidates rightEndpoint rightComputed)
  have doubleBond : input.moleculeGraph.bond topology.left topology.right = 2 :=
    (input.localizedRule3PhysicalEndpointCursorFrameExec?_sound
      occurrence topology found).2.2.2.1
  exact input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_endpoints
    target occurrence view read rule3FrameOf topology found leftEndpoint rightEndpoint
    leftComputed rightComputed doubleBond ready

/-- The odd-cumulene spatial wrapper's projected identity at a structurally successful endpoint
pair is the canonical physical identity, under the conditional geometry domain. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
      input.LocalizedRerootCursor carrierFuel)
    (certificate : input.LocalizedRule3OddRouteCertificate occurrence)
    (routed : input.localizedRule3OddRouteCertificate? occurrence = some certificate)
    (leftCandidates : input.localizedRule3ExplicitSubstituents
      topology.initial.left topology.initial.right = [leftFirst, leftSecond])
    (rightCandidates : input.localizedRule3ExplicitSubstituents
      topology.right topology.rightPartner = [rightFirst, rightSecond])
    (leftFirstSelected : input.localizedRule3ReferenceCursorExec?
      topology.initial.leftCursor leftFirst = some leftFirstCursor)
    (leftSecondSelected : input.localizedRule3ReferenceCursorExec?
      topology.initial.leftCursor leftSecond = some leftSecondCursor)
    (rightFirstSelected : input.localizedRule3ReferenceCursorExec?
      topology.rightCursor rightFirst = some rightFirstCursor)
    (rightSecondSelected : input.localizedRule3ReferenceCursorExec?
      topology.rightCursor rightSecond = some rightSecondCursor)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.initial.left topology.initial.right
        topology.initial.leftCursor = some leftEndpoint)
    (rightComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.rightPartner
        topology.rightCursor = some rightEndpoint)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf =
      some (input.localizedRule3PhysicalUnitId topology.initial.left topology.right) := by
  have candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond := by
    unfold LocalizedRule3ExtendedNodeConditionalGeometryDomain at geometry
    simp only [routed] at geometry
    exact geometry topology leftFirst leftSecond rightFirst rightSecond leftFirstCursor
      leftSecondCursor rightFirstCursor rightSecondCursor found leftCandidates
      rightCandidates leftFirstSelected leftSecondSelected rightFirstSelected
      rightSecondSelected
  have ready : input.LocalizedRule3AxisGeometryReadiness
      topology.initial.left topology.right leftEndpoint.priority rightEndpoint.priority :=
    input.localizedRule3AxisGeometryReadiness_of_candidates
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
      leftEndpoint.priority rightEndpoint.priority candidateReady
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
        target view read rule3FrameOf topology.initial.left topology.initial.right
        leftFirst leftSecond topology.initial.leftCursor leftCandidates leftEndpoint
        leftComputed)
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
        target view read rule3FrameOf topology.right topology.rightPartner rightFirst
        rightSecond topology.rightCursor rightCandidates rightEndpoint rightComputed)
  exact input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_endpoints
    target occurrence view read rule3FrameOf topology found leftEndpoint rightEndpoint
    leftComputed rightComputed ready

/-! ## Failure-complete spatial equality on the ordinary route

The proof inspects the actual executable structure.  No successful topology, candidate pair,
reference selection or callback is assumed.  Every structural failure is a shared refusal supplied
by the predecessor's structural-refusal helpers, and the surviving structural-success branch is
decided by the two-target endpoint synchronization and the conditional geometry domain. -/

/-- **Failure-complete ordinary spatial equality.**  The two ordinary spatial wrappers have equal
projected physical identity under the conditional geometry domain and request-local callback facts
on the actual ordinary request list.  Both refusal and acceptance are covered. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none)
    (routed : input.localizedRule3OrdinaryRouteCertificate? occurrence = some certificate)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortSpatialCallbackRequests occurrence) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortSpatialCallbackRequests occurrence) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortSpatialCallbackRequests occurrence) after) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        targetOne occurrence viewOne readOne before =
      input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        targetTwo occurrence viewTwo readTwo after := by
  cases found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none =>
      have oneNone : input.localizedRule3ShortCircuitSpatialPhysicalUnit?
          targetOne occurrence viewOne readOne before = none := by
        simp [localizedRule3ShortCircuitSpatialPhysicalUnit?,
          localizedRule3ShortCircuitSpatialUnitWithRead?, found]
      have twoNone : input.localizedRule3ShortCircuitSpatialPhysicalUnit?
          targetTwo occurrence viewTwo readTwo after = none := by
        simp [localizedRule3ShortCircuitSpatialPhysicalUnit?,
          localizedRule3ShortCircuitSpatialUnitWithRead?, found]
      rw [oneNone, twoNone]
  | some topology =>
      have leftAgree : input.Rule3CallbackIsSomeAgreesOn
          (input.rule3ShortEndpointCallbackRequests topology.left topology.right
            topology.leftCursor) before after := by
        intro cursors member
        exact isSomeAgree cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member])
      have leftBeforeShape : input.Rule3CallbackFrameShapeOn
          (input.rule3ShortEndpointCallbackRequests topology.left topology.right
            topology.leftCursor) before := by
        intro cursors member frame succeeds
        exact beforeShape cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member]) frame succeeds
      have leftAfterShape : input.Rule3CallbackFrameShapeOn
          (input.rule3ShortEndpointCallbackRequests topology.left topology.right
            topology.leftCursor) after := by
        intro cursors member frame succeeds
        exact afterShape cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member]) frame succeeds
      have rightAgree : input.Rule3CallbackIsSomeAgreesOn
          (input.rule3ShortEndpointCallbackRequests topology.right topology.left
            topology.rightCursor) before after := by
        intro cursors member
        exact isSomeAgree cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member])
      have rightBeforeShape : input.Rule3CallbackFrameShapeOn
          (input.rule3ShortEndpointCallbackRequests topology.right topology.left
            topology.rightCursor) before := by
        intro cursors member frame succeeds
        exact beforeShape cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member]) frame succeeds
      have rightAfterShape : input.Rule3CallbackFrameShapeOn
          (input.rule3ShortEndpointCallbackRequests topology.right topology.left
            topology.rightCursor) after := by
        intro cursors member frame succeeds
        exact afterShape cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member]) frame succeeds
      have leftSync :=
        input.localizedRule3ConditionalEndpointSelector_isSome_eq_of_targets
          targetOne targetTwo viewOne viewTwo readOne readTwo before after
          topology.left topology.right topology.leftCursor leftAgree leftBeforeShape
          leftAfterShape
      have rightSync :=
        input.localizedRule3ConditionalEndpointSelector_isSome_eq_of_targets
          targetOne targetTwo viewOne viewTwo readOne readTwo before after
          topology.right topology.left topology.rightCursor rightAgree rightBeforeShape
          rightAfterShape
      cases leftCandidates :
          input.localizedRule3ExplicitSubstituents topology.left topology.right with
      | nil =>
          have oneLeft :=
            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
              targetOne viewOne readOne before topology.left topology.right
              topology.leftCursor leftCandidates
          have twoLeft :=
            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
              targetTwo viewTwo readTwo after topology.left topology.right
              topology.leftCursor leftCandidates
          have oneNone :=
            input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
              targetOne occurrence viewOne readOne before topology found oneLeft
          have twoNone :=
            input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
              targetTwo occurrence viewTwo readTwo after topology found twoLeft
          rw [oneNone, twoNone]
      | cons leftFirst leftRest =>
          cases leftRest with
          | nil =>
              have oneLeft :=
                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
                  targetOne viewOne readOne before topology.left topology.right leftFirst
                  topology.leftCursor leftCandidates
              have twoLeft :=
                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
                  targetTwo viewTwo readTwo after topology.left topology.right leftFirst
                  topology.leftCursor leftCandidates
              have oneNone :=
                input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                  targetOne occurrence viewOne readOne before topology found oneLeft
              have twoNone :=
                input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                  targetTwo occurrence viewTwo readTwo after topology found twoLeft
              rw [oneNone, twoNone]
          | cons leftSecond leftRest =>
              cases leftRest with
              | cons leftThird leftRestTail =>
                  have oneLeft :=
                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
                      targetOne viewOne readOne before topology.left topology.right
                      leftFirst leftSecond leftThird leftRestTail topology.leftCursor
                      leftCandidates
                  have twoLeft :=
                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
                      targetTwo viewTwo readTwo after topology.left topology.right
                      leftFirst leftSecond leftThird leftRestTail topology.leftCursor
                      leftCandidates
                  have oneNone :=
                    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                      targetOne occurrence viewOne readOne before topology found oneLeft
                  have twoNone :=
                    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                      targetTwo occurrence viewTwo readTwo after topology found twoLeft
                  rw [oneNone, twoNone]
              | nil =>
                  cases leftFirstSelected : input.localizedRule3ReferenceCursorExec?
                      topology.leftCursor leftFirst with
                  | none =>
                      have oneLeft :=
                        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
                          targetOne viewOne readOne before topology.left topology.right
                          leftFirst leftSecond topology.leftCursor leftCandidates
                          leftFirstSelected
                      have twoLeft :=
                        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
                          targetTwo viewTwo readTwo after topology.left topology.right
                          leftFirst leftSecond topology.leftCursor leftCandidates
                          leftFirstSelected
                      have oneNone :=
                        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                          targetOne occurrence viewOne readOne before topology found oneLeft
                      have twoNone :=
                        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                          targetTwo occurrence viewTwo readTwo after topology found twoLeft
                      rw [oneNone, twoNone]
                  | some leftFirstCursor =>
                      cases leftSecondSelected : input.localizedRule3ReferenceCursorExec?
                          topology.leftCursor leftSecond with
                      | none =>
                          have oneLeft :=
                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
                              targetOne viewOne readOne before topology.left
                              topology.right leftFirst leftSecond topology.leftCursor
                              leftFirstCursor leftCandidates leftFirstSelected
                              leftSecondSelected
                          have twoLeft :=
                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
                              targetTwo viewTwo readTwo after topology.left
                              topology.right leftFirst leftSecond topology.leftCursor
                              leftFirstCursor leftCandidates leftFirstSelected
                              leftSecondSelected
                          have oneNone :=
                            input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                              targetOne occurrence viewOne readOne before topology found
                              oneLeft
                          have twoNone :=
                            input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                              targetTwo occurrence viewTwo readTwo after topology found
                              twoLeft
                          rw [oneNone, twoNone]
                      | some leftSecondCursor =>
                          cases rightCandidates :
                              input.localizedRule3ExplicitSubstituents topology.right
                                topology.left with
                          | nil =>
                              have oneRight :=
                                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
                                  targetOne viewOne readOne before topology.right
                                  topology.left topology.rightCursor rightCandidates
                              have twoRight :=
                                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
                                  targetTwo viewTwo readTwo after topology.right
                                  topology.left topology.rightCursor rightCandidates
                              have oneNone :=
                                input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                  targetOne occurrence viewOne readOne before topology
                                  found oneRight
                              have twoNone :=
                                input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                  targetTwo occurrence viewTwo readTwo after topology
                                  found twoRight
                              rw [oneNone, twoNone]
                          | cons rightFirst rightRest =>
                              cases rightRest with
                              | nil =>
                                  have oneRight :=
                                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
                                      targetOne viewOne readOne before topology.right
                                      topology.left rightFirst topology.rightCursor
                                      rightCandidates
                                  have twoRight :=
                                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
                                      targetTwo viewTwo readTwo after topology.right
                                      topology.left rightFirst topology.rightCursor
                                      rightCandidates
                                  have oneNone :=
                                    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                      targetOne occurrence viewOne readOne before topology
                                      found oneRight
                                  have twoNone :=
                                    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                      targetTwo occurrence viewTwo readTwo after topology
                                      found twoRight
                                  rw [oneNone, twoNone]
                              | cons rightSecond rightRest =>
                                  cases rightRest with
                                  | cons rightThird rightRestTail =>
                                      have oneRight :=
                                        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
                                          targetOne viewOne readOne before topology.right
                                          topology.left rightFirst rightSecond rightThird
                                          rightRestTail topology.rightCursor
                                          rightCandidates
                                      have twoRight :=
                                        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
                                          targetTwo viewTwo readTwo after topology.right
                                          topology.left rightFirst rightSecond rightThird
                                          rightRestTail topology.rightCursor
                                          rightCandidates
                                      have oneNone :=
                                        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                          targetOne occurrence viewOne readOne before
                                          topology found oneRight
                                      have twoNone :=
                                        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                          targetTwo occurrence viewTwo readTwo after
                                          topology found twoRight
                                      rw [oneNone, twoNone]
                                  | nil =>
                                      cases rightFirstSelected :
                                          input.localizedRule3ReferenceCursorExec?
                                            topology.rightCursor rightFirst with
                                      | none =>
                                          have oneRight :=
                                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
                                              targetOne viewOne readOne before
                                              topology.right topology.left rightFirst
                                              rightSecond topology.rightCursor
                                              rightCandidates rightFirstSelected
                                          have twoRight :=
                                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
                                              targetTwo viewTwo readTwo after
                                              topology.right topology.left rightFirst
                                              rightSecond topology.rightCursor
                                              rightCandidates rightFirstSelected
                                          have oneNone :=
                                            input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                              targetOne occurrence viewOne readOne before
                                              topology found oneRight
                                          have twoNone :=
                                            input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                              targetTwo occurrence viewTwo readTwo after
                                              topology found twoRight
                                          rw [oneNone, twoNone]
                                      | some rightFirstCursor =>
                                          cases rightSecondSelected :
                                              input.localizedRule3ReferenceCursorExec?
                                                topology.rightCursor rightSecond with
                                          | none =>
                                              have oneRight :=
                                                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
                                                  targetOne viewOne readOne before
                                                  topology.right topology.left rightFirst
                                                  rightSecond topology.rightCursor
                                                  rightFirstCursor rightCandidates
                                                  rightFirstSelected rightSecondSelected
                                              have twoRight :=
                                                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
                                                  targetTwo viewTwo readTwo after
                                                  topology.right topology.left rightFirst
                                                  rightSecond topology.rightCursor
                                                  rightFirstCursor rightCandidates
                                                  rightFirstSelected rightSecondSelected
                                              have oneNone :=
                                                input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                                  targetOne occurrence viewOne readOne
                                                  before topology found oneRight
                                              have twoNone :=
                                                input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                                  targetTwo occurrence viewTwo readTwo after
                                                  topology found twoRight
                                              rw [oneNone, twoNone]
                                          | some rightSecondCursor =>
                                              cases leftOne :
                                                  input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                    targetOne viewOne readOne before
                                                    topology.left topology.right
                                                    topology.leftCursor with
                                              | none =>
                                                  have leftTwo : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                      targetTwo viewTwo readTwo after
                                                      topology.left topology.right
                                                      topology.leftCursor = none := by
                                                    cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                        targetTwo viewTwo readTwo after
                                                        topology.left topology.right
                                                        topology.leftCursor with
                                                    | none => rfl
                                                    | some value =>
                                                        rw [leftOne, h] at leftSync
                                                        simp only [Option.isSome_none,
                                                          Option.isSome_some] at leftSync
                                                        cases leftSync
                                                  have oneNone :=
                                                    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                                                      targetOne occurrence viewOne readOne
                                                      before topology found leftOne
                                                  have twoNone :=
                                                    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                                                      targetTwo occurrence viewTwo readTwo
                                                      after topology found leftTwo
                                                  rw [oneNone, twoNone]
                                              | some leftEndpointOne =>
                                                  have leftTwoExists : ∃ leftEndpointTwo,
                                                      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                        targetTwo viewTwo readTwo after
                                                        topology.left topology.right
                                                        topology.leftCursor =
                                                          some leftEndpointTwo := by
                                                    cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                        targetTwo viewTwo readTwo after
                                                        topology.left topology.right
                                                        topology.leftCursor with
                                                    | none =>
                                                        rw [leftOne, h] at leftSync
                                                        simp only [Option.isSome_none,
                                                          Option.isSome_some] at leftSync
                                                        cases leftSync
                                                    | some value => exact ⟨value, rfl⟩
                                                  obtain ⟨leftEndpointTwo, leftTwo⟩ :=
                                                    leftTwoExists
                                                  cases rightOne :
                                                      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                        targetOne viewOne readOne before
                                                        topology.right topology.left
                                                        topology.rightCursor with
                                                  | none =>
                                                      have rightTwo : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                          targetTwo viewTwo readTwo after
                                                          topology.right topology.left
                                                          topology.rightCursor = none := by
                                                        cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                            targetTwo viewTwo readTwo after
                                                            topology.right topology.left
                                                            topology.rightCursor with
                                                        | none => rfl
                                                        | some value =>
                                                            rw [rightOne, h] at rightSync
                                                            simp only [Option.isSome_none,
                                                              Option.isSome_some] at rightSync
                                                            cases rightSync
                                                      have oneNone :=
                                                        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                                          targetOne occurrence viewOne
                                                          readOne before topology found
                                                          rightOne
                                                      have twoNone :=
                                                        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                                          targetTwo occurrence viewTwo
                                                          readTwo after topology found
                                                          rightTwo
                                                      rw [oneNone, twoNone]
                                                  | some rightEndpointOne =>
                                                      have rightTwoExists : ∃ rightEndpointTwo,
                                                          input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                            targetTwo viewTwo readTwo after
                                                            topology.right topology.left
                                                            topology.rightCursor =
                                                              some rightEndpointTwo := by
                                                        cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                            targetTwo viewTwo readTwo after
                                                            topology.right topology.left
                                                            topology.rightCursor with
                                                        | none =>
                                                            rw [rightOne, h] at rightSync
                                                            simp only [Option.isSome_none,
                                                              Option.isSome_some] at rightSync
                                                            cases rightSync
                                                        | some value => exact ⟨value, rfl⟩
                                                      obtain ⟨rightEndpointTwo, rightTwo⟩ :=
                                                        rightTwoExists
                                                      have oneSome :=
                                                        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_conditionalGeometry
                                                          targetOne occurrence viewOne readOne
                                                          before topology found leftFirst
                                                          leftSecond rightFirst rightSecond
                                                          leftFirstCursor leftSecondCursor
                                                          rightFirstCursor rightSecondCursor
                                                          certificate oddNone routed
                                                          leftCandidates rightCandidates
                                                          leftFirstSelected leftSecondSelected
                                                          rightFirstSelected rightSecondSelected
                                                          leftEndpointOne rightEndpointOne
                                                          leftOne rightOne geometry
                                                      have twoSome :=
                                                        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_conditionalGeometry
                                                          targetTwo occurrence viewTwo readTwo
                                                          after topology found leftFirst
                                                          leftSecond rightFirst rightSecond
                                                          leftFirstCursor leftSecondCursor
                                                          rightFirstCursor rightSecondCursor
                                                          certificate oddNone routed
                                                          leftCandidates rightCandidates
                                                          leftFirstSelected leftSecondSelected
                                                          rightFirstSelected rightSecondSelected
                                                          leftEndpointTwo rightEndpointTwo
                                                          leftTwo rightTwo geometry
                                                      rw [oneSome, twoSome]

/-! ## Failure-complete spatial equality on the odd-cumulene route

The same structural inspection on the odd frame.  There is no adjacent double-bond premise on this
route; the canonical identity is the unordered pair of the cumulated initial terminal and the far
terminal, exactly as in the accepted odd projection law. -/

/-- **Failure-complete odd spatial equality.**  The two odd-cumulene spatial wrappers have equal
projected physical identity under the conditional geometry domain and request-local callback facts
on the actual odd request list.  Both refusal and acceptance are covered, and no topology,
candidate, reference selection or callback success is assumed. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedRule3OddRouteCertificate occurrence)
    (routed : input.localizedRule3OddRouteCertificate? occurrence = some certificate)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortOddCallbackRequests occurrence) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortOddCallbackRequests occurrence) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortOddCallbackRequests occurrence) after) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        targetOne occurrence viewOne readOne before =
      input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        targetTwo occurrence viewTwo readTwo after := by
  cases found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none =>
      have oneNone : input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
          targetOne occurrence viewOne readOne before = none := by
        simp [localizedRule3ShortCircuitOddSpatialPhysicalUnit?,
          localizedRule3ShortCircuitOddSpatialUnitWithRead?, found]
      have twoNone : input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
          targetTwo occurrence viewTwo readTwo after = none := by
        simp [localizedRule3ShortCircuitOddSpatialPhysicalUnit?,
          localizedRule3ShortCircuitOddSpatialUnitWithRead?, found]
      rw [oneNone, twoNone]
  | some topology =>
      have leftAgree : input.Rule3CallbackIsSomeAgreesOn
          (input.rule3ShortEndpointCallbackRequests topology.initial.left
            topology.initial.right topology.initial.leftCursor) before after := by
        intro cursors member
        exact isSomeAgree cursors
          (by simp [rule3ShortOddCallbackRequests, found, member])
      have leftBeforeShape : input.Rule3CallbackFrameShapeOn
          (input.rule3ShortEndpointCallbackRequests topology.initial.left
            topology.initial.right topology.initial.leftCursor) before := by
        intro cursors member frame succeeds
        exact beforeShape cursors
          (by simp [rule3ShortOddCallbackRequests, found, member]) frame succeeds
      have leftAfterShape : input.Rule3CallbackFrameShapeOn
          (input.rule3ShortEndpointCallbackRequests topology.initial.left
            topology.initial.right topology.initial.leftCursor) after := by
        intro cursors member frame succeeds
        exact afterShape cursors
          (by simp [rule3ShortOddCallbackRequests, found, member]) frame succeeds
      have rightAgree : input.Rule3CallbackIsSomeAgreesOn
          (input.rule3ShortEndpointCallbackRequests topology.right topology.rightPartner
            topology.rightCursor) before after := by
        intro cursors member
        exact isSomeAgree cursors
          (by simp [rule3ShortOddCallbackRequests, found, member])
      have rightBeforeShape : input.Rule3CallbackFrameShapeOn
          (input.rule3ShortEndpointCallbackRequests topology.right topology.rightPartner
            topology.rightCursor) before := by
        intro cursors member frame succeeds
        exact beforeShape cursors
          (by simp [rule3ShortOddCallbackRequests, found, member]) frame succeeds
      have rightAfterShape : input.Rule3CallbackFrameShapeOn
          (input.rule3ShortEndpointCallbackRequests topology.right topology.rightPartner
            topology.rightCursor) after := by
        intro cursors member frame succeeds
        exact afterShape cursors
          (by simp [rule3ShortOddCallbackRequests, found, member]) frame succeeds
      have leftSync :=
        input.localizedRule3ConditionalEndpointSelector_isSome_eq_of_targets
          targetOne targetTwo viewOne viewTwo readOne readTwo before after
          topology.initial.left topology.initial.right topology.initial.leftCursor
          leftAgree leftBeforeShape leftAfterShape
      have rightSync :=
        input.localizedRule3ConditionalEndpointSelector_isSome_eq_of_targets
          targetOne targetTwo viewOne viewTwo readOne readTwo before after
          topology.right topology.rightPartner topology.rightCursor rightAgree
          rightBeforeShape rightAfterShape
      cases leftCandidates : input.localizedRule3ExplicitSubstituents
          topology.initial.left topology.initial.right with
      | nil =>
          have oneLeft :=
            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
              targetOne viewOne readOne before topology.initial.left
              topology.initial.right topology.initial.leftCursor leftCandidates
          have twoLeft :=
            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
              targetTwo viewTwo readTwo after topology.initial.left
              topology.initial.right topology.initial.leftCursor leftCandidates
          have oneNone :=
            input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
              targetOne occurrence viewOne readOne before topology found oneLeft
          have twoNone :=
            input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
              targetTwo occurrence viewTwo readTwo after topology found twoLeft
          rw [oneNone, twoNone]
      | cons leftFirst leftRest =>
          cases leftRest with
          | nil =>
              have oneLeft :=
                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
                  targetOne viewOne readOne before topology.initial.left
                  topology.initial.right leftFirst topology.initial.leftCursor
                  leftCandidates
              have twoLeft :=
                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
                  targetTwo viewTwo readTwo after topology.initial.left
                  topology.initial.right leftFirst topology.initial.leftCursor
                  leftCandidates
              have oneNone :=
                input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                  targetOne occurrence viewOne readOne before topology found oneLeft
              have twoNone :=
                input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                  targetTwo occurrence viewTwo readTwo after topology found twoLeft
              rw [oneNone, twoNone]
          | cons leftSecond leftRest =>
              cases leftRest with
              | cons leftThird leftRestTail =>
                  have oneLeft :=
                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
                      targetOne viewOne readOne before topology.initial.left
                      topology.initial.right leftFirst leftSecond leftThird
                      leftRestTail topology.initial.leftCursor leftCandidates
                  have twoLeft :=
                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
                      targetTwo viewTwo readTwo after topology.initial.left
                      topology.initial.right leftFirst leftSecond leftThird
                      leftRestTail topology.initial.leftCursor leftCandidates
                  have oneNone :=
                    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                      targetOne occurrence viewOne readOne before topology found oneLeft
                  have twoNone :=
                    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                      targetTwo occurrence viewTwo readTwo after topology found twoLeft
                  rw [oneNone, twoNone]
              | nil =>
                  cases leftFirstSelected : input.localizedRule3ReferenceCursorExec?
                      topology.initial.leftCursor leftFirst with
                  | none =>
                      have oneLeft :=
                        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
                          targetOne viewOne readOne before topology.initial.left
                          topology.initial.right leftFirst leftSecond
                          topology.initial.leftCursor leftCandidates leftFirstSelected
                      have twoLeft :=
                        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
                          targetTwo viewTwo readTwo after topology.initial.left
                          topology.initial.right leftFirst leftSecond
                          topology.initial.leftCursor leftCandidates leftFirstSelected
                      have oneNone :=
                        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                          targetOne occurrence viewOne readOne before topology found oneLeft
                      have twoNone :=
                        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                          targetTwo occurrence viewTwo readTwo after topology found twoLeft
                      rw [oneNone, twoNone]
                  | some leftFirstCursor =>
                      cases leftSecondSelected : input.localizedRule3ReferenceCursorExec?
                          topology.initial.leftCursor leftSecond with
                      | none =>
                          have oneLeft :=
                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
                              targetOne viewOne readOne before topology.initial.left
                              topology.initial.right leftFirst leftSecond
                              topology.initial.leftCursor leftFirstCursor leftCandidates
                              leftFirstSelected leftSecondSelected
                          have twoLeft :=
                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
                              targetTwo viewTwo readTwo after topology.initial.left
                              topology.initial.right leftFirst leftSecond
                              topology.initial.leftCursor leftFirstCursor leftCandidates
                              leftFirstSelected leftSecondSelected
                          have oneNone :=
                            input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                              targetOne occurrence viewOne readOne before topology found
                              oneLeft
                          have twoNone :=
                            input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                              targetTwo occurrence viewTwo readTwo after topology found
                              twoLeft
                          rw [oneNone, twoNone]
                      | some leftSecondCursor =>
                          cases rightCandidates :
                              input.localizedRule3ExplicitSubstituents topology.right
                                topology.rightPartner with
                          | nil =>
                              have oneRight :=
                                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
                                  targetOne viewOne readOne before topology.right
                                  topology.rightPartner topology.rightCursor rightCandidates
                              have twoRight :=
                                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
                                  targetTwo viewTwo readTwo after topology.right
                                  topology.rightPartner topology.rightCursor rightCandidates
                              have oneNone :=
                                input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                  targetOne occurrence viewOne readOne before topology
                                  found oneRight
                              have twoNone :=
                                input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                  targetTwo occurrence viewTwo readTwo after topology
                                  found twoRight
                              rw [oneNone, twoNone]
                          | cons rightFirst rightRest =>
                              cases rightRest with
                              | nil =>
                                  have oneRight :=
                                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
                                      targetOne viewOne readOne before topology.right
                                      topology.rightPartner rightFirst topology.rightCursor
                                      rightCandidates
                                  have twoRight :=
                                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
                                      targetTwo viewTwo readTwo after topology.right
                                      topology.rightPartner rightFirst topology.rightCursor
                                      rightCandidates
                                  have oneNone :=
                                    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                      targetOne occurrence viewOne readOne before topology
                                      found oneRight
                                  have twoNone :=
                                    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                      targetTwo occurrence viewTwo readTwo after topology
                                      found twoRight
                                  rw [oneNone, twoNone]
                              | cons rightSecond rightRest =>
                                  cases rightRest with
                                  | cons rightThird rightRestTail =>
                                      have oneRight :=
                                        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
                                          targetOne viewOne readOne before topology.right
                                          topology.rightPartner rightFirst rightSecond
                                          rightThird rightRestTail topology.rightCursor
                                          rightCandidates
                                      have twoRight :=
                                        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
                                          targetTwo viewTwo readTwo after topology.right
                                          topology.rightPartner rightFirst rightSecond
                                          rightThird rightRestTail topology.rightCursor
                                          rightCandidates
                                      have oneNone :=
                                        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                          targetOne occurrence viewOne readOne before
                                          topology found oneRight
                                      have twoNone :=
                                        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                          targetTwo occurrence viewTwo readTwo after
                                          topology found twoRight
                                      rw [oneNone, twoNone]
                                  | nil =>
                                      cases rightFirstSelected :
                                          input.localizedRule3ReferenceCursorExec?
                                            topology.rightCursor rightFirst with
                                      | none =>
                                          have oneRight :=
                                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
                                              targetOne viewOne readOne before
                                              topology.right topology.rightPartner
                                              rightFirst rightSecond topology.rightCursor
                                              rightCandidates rightFirstSelected
                                          have twoRight :=
                                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
                                              targetTwo viewTwo readTwo after
                                              topology.right topology.rightPartner
                                              rightFirst rightSecond topology.rightCursor
                                              rightCandidates rightFirstSelected
                                          have oneNone :=
                                            input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                              targetOne occurrence viewOne readOne before
                                              topology found oneRight
                                          have twoNone :=
                                            input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                              targetTwo occurrence viewTwo readTwo after
                                              topology found twoRight
                                          rw [oneNone, twoNone]
                                      | some rightFirstCursor =>
                                          cases rightSecondSelected :
                                              input.localizedRule3ReferenceCursorExec?
                                                topology.rightCursor rightSecond with
                                          | none =>
                                              have oneRight :=
                                                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
                                                  targetOne viewOne readOne before
                                                  topology.right topology.rightPartner
                                                  rightFirst rightSecond topology.rightCursor
                                                  rightFirstCursor rightCandidates
                                                  rightFirstSelected rightSecondSelected
                                              have twoRight :=
                                                input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
                                                  targetTwo viewTwo readTwo after
                                                  topology.right topology.rightPartner
                                                  rightFirst rightSecond topology.rightCursor
                                                  rightFirstCursor rightCandidates
                                                  rightFirstSelected rightSecondSelected
                                              have oneNone :=
                                                input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                                  targetOne occurrence viewOne readOne
                                                  before topology found oneRight
                                              have twoNone :=
                                                input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                                  targetTwo occurrence viewTwo readTwo after
                                                  topology found twoRight
                                              rw [oneNone, twoNone]
                                          | some rightSecondCursor =>
                                              cases leftOne :
                                                  input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                    targetOne viewOne readOne before
                                                    topology.initial.left
                                                    topology.initial.right
                                                    topology.initial.leftCursor with
                                              | none =>
                                                  have leftTwo : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                      targetTwo viewTwo readTwo after
                                                      topology.initial.left
                                                      topology.initial.right
                                                      topology.initial.leftCursor = none := by
                                                    cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                        targetTwo viewTwo readTwo after
                                                        topology.initial.left
                                                        topology.initial.right
                                                        topology.initial.leftCursor with
                                                    | none => rfl
                                                    | some value =>
                                                        rw [leftOne, h] at leftSync
                                                        simp only [Option.isSome_none,
                                                          Option.isSome_some] at leftSync
                                                        cases leftSync
                                                  have oneNone :=
                                                    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                                                      targetOne occurrence viewOne readOne
                                                      before topology found leftOne
                                                  have twoNone :=
                                                    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
                                                      targetTwo occurrence viewTwo readTwo
                                                      after topology found leftTwo
                                                  rw [oneNone, twoNone]
                                              | some leftEndpointOne =>
                                                  have leftTwoExists : ∃ leftEndpointTwo,
                                                      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                        targetTwo viewTwo readTwo after
                                                        topology.initial.left
                                                        topology.initial.right
                                                        topology.initial.leftCursor =
                                                          some leftEndpointTwo := by
                                                    cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                        targetTwo viewTwo readTwo after
                                                        topology.initial.left
                                                        topology.initial.right
                                                        topology.initial.leftCursor with
                                                    | none =>
                                                        rw [leftOne, h] at leftSync
                                                        simp only [Option.isSome_none,
                                                          Option.isSome_some] at leftSync
                                                        cases leftSync
                                                    | some value => exact ⟨value, rfl⟩
                                                  obtain ⟨leftEndpointTwo, leftTwo⟩ :=
                                                    leftTwoExists
                                                  cases rightOne :
                                                      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                        targetOne viewOne readOne before
                                                        topology.right topology.rightPartner
                                                        topology.rightCursor with
                                                  | none =>
                                                      have rightTwo : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                          targetTwo viewTwo readTwo after
                                                          topology.right topology.rightPartner
                                                          topology.rightCursor = none := by
                                                        cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                            targetTwo viewTwo readTwo after
                                                            topology.right topology.rightPartner
                                                            topology.rightCursor with
                                                        | none => rfl
                                                        | some value =>
                                                            rw [rightOne, h] at rightSync
                                                            simp only [Option.isSome_none,
                                                              Option.isSome_some] at rightSync
                                                            cases rightSync
                                                      have oneNone :=
                                                        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                                          targetOne occurrence viewOne
                                                          readOne before topology found
                                                          rightOne
                                                      have twoNone :=
                                                        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
                                                          targetTwo occurrence viewTwo
                                                          readTwo after topology found
                                                          rightTwo
                                                      rw [oneNone, twoNone]
                                                  | some rightEndpointOne =>
                                                      have rightTwoExists : ∃ rightEndpointTwo,
                                                          input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                            targetTwo viewTwo readTwo after
                                                            topology.right topology.rightPartner
                                                            topology.rightCursor =
                                                              some rightEndpointTwo := by
                                                        cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                                                            targetTwo viewTwo readTwo after
                                                            topology.right topology.rightPartner
                                                            topology.rightCursor with
                                                        | none =>
                                                            rw [rightOne, h] at rightSync
                                                            simp only [Option.isSome_none,
                                                              Option.isSome_some] at rightSync
                                                            cases rightSync
                                                        | some value => exact ⟨value, rfl⟩
                                                      obtain ⟨rightEndpointTwo, rightTwo⟩ :=
                                                        rightTwoExists
                                                      have oneSome :=
                                                        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_conditionalGeometry
                                                          targetOne occurrence viewOne readOne
                                                          before topology found leftFirst
                                                          leftSecond rightFirst rightSecond
                                                          leftFirstCursor leftSecondCursor
                                                          rightFirstCursor rightSecondCursor
                                                          certificate routed leftCandidates
                                                          rightCandidates leftFirstSelected
                                                          leftSecondSelected rightFirstSelected
                                                          rightSecondSelected leftEndpointOne
                                                          rightEndpointOne leftOne rightOne
                                                          geometry
                                                      have twoSome :=
                                                        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_conditionalGeometry
                                                          targetTwo occurrence viewTwo readTwo
                                                          after topology found leftFirst
                                                          leftSecond rightFirst rightSecond
                                                          leftFirstCursor leftSecondCursor
                                                          rightFirstCursor rightSecondCursor
                                                          certificate routed leftCandidates
                                                          rightCandidates leftFirstSelected
                                                          leftSecondSelected rightFirstSelected
                                                          rightSecondSelected leftEndpointTwo
                                                          rightEndpointTwo leftTwo rightTwo
                                                          geometry
                                                      rw [oneSome, twoSome]







/-- Membership-equivalent exclusion lists preserve the projected physical identity after any
spatial wrapper with equal projected identity, including the `some none` cancellation branch. -/
theorem localizedRule3ConditionalNodePhysicalUnit_exclusion_policy
    (input : CertifiedLocalizedCIPInput) {α : Type}
    (observation : α → input.LocalizedRule3SpatialNodeResult)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (containsEq : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      excludedOne.contains unit = excludedTwo.contains unit)
    (left right : Option α)
    (unitEq : Option.map (fun result => (observation result).physicalUnitId) left =
      Option.map (fun result => (observation result).physicalUnitId) right) :
    Option.map (Option.map LocalizedRule3SpatialNodeResult.physicalUnitId)
        (left >>= fun result =>
          some (if excludedOne.contains (observation result).physicalUnitId
            then none else some (observation result))) =
      Option.map (Option.map LocalizedRule3SpatialNodeResult.physicalUnitId)
        (right >>= fun result =>
          some (if excludedTwo.contains (observation result).physicalUnitId
            then none else some (observation result))) := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some rightResult =>
          simp only [Option.map_none, Option.map_some] at unitEq
          cases unitEq
  | some leftResult =>
      cases right with
      | none =>
          simp only [Option.map_none, Option.map_some] at unitEq
          cases unitEq
      | some rightResult =>
          have idEq : (observation leftResult).physicalUnitId =
              (observation rightResult).physicalUnitId := by
            simpa only [Option.map_some, Option.some.injEq] using unitEq
          have contains : excludedOne.contains (observation rightResult).physicalUnitId =
              excludedTwo.contains (observation rightResult).physicalUnitId :=
            containsEq _
          by_cases blocked :
            excludedTwo.contains (observation rightResult).physicalUnitId = true
          · have blockedOne :
                excludedOne.contains (observation rightResult).physicalUnitId = true := by
              rw [contains]
              exact blocked
            simp only [option_some_bind_apply, Option.map_some, idEq, if_pos blockedOne,
              if_pos blocked, Option.map_none]
          · have blockedOne : ¬
                excludedOne.contains (observation rightResult).physicalUnitId = true := by
              intro present
              exact blocked (by rw [← contains]; exact present)
            simp only [option_some_bind_apply, Option.map_some, if_neg blockedOne,
              if_neg blocked, idEq]

/-! ## Route-indexed node laws under the conditional geometry domain -/

/-- **The odd-route node law under conditional geometry.**  When the actual dispatch takes the odd
route, the projected physical identity of the extended node is synchronized under the conditional
geometry domain and request-local callback facts on the actual extended request list.  No topology,
candidate, reference selection or callback success is assumed. -/
theorem localizedRule3ExtendedNodePhysicalUnit?_eq_of_oddRouteConditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedRule3OddRouteCertificate occurrence)
    (routed : input.localizedRule3OddRouteCertificate? occurrence = some certificate)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) after)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (excludedEquivalent : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ excludedOne ↔ unit ∈ excludedTwo) :
    input.localizedRule3ExtendedNodePhysicalUnit?
        targetOne occurrence viewOne readOne before excludedOne =
      input.localizedRule3ExtendedNodePhysicalUnit?
        targetTwo occurrence viewTwo readTwo after excludedTwo := by
  have oddAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortOddCallbackRequests occurrence) before after := by
    intro cursors member
    exact isSomeAgree cursors
      (by simpa only [rule3ExtendedNodeCallbackRequests, routed] using member)
  have oddBeforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortOddCallbackRequests occurrence) before := by
    intro cursors member frame succeeds
    exact beforeShape cursors
      (by simpa only [rule3ExtendedNodeCallbackRequests, routed] using member) frame
      succeeds
  have oddAfterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortOddCallbackRequests occurrence) after := by
    intro cursors member frame succeeds
    exact afterShape cursors
      (by simpa only [rule3ExtendedNodeCallbackRequests, routed] using member) frame
      succeeds
  have spatial :=
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_conditionalGeometry
      targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
      certificate routed geometry oddAgree oddBeforeShape oddAfterShape
  have containsEq : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      excludedOne.contains unit = excludedTwo.contains unit :=
    fun unit =>
      input.localizedRule3PhysicalUnitContains_eq_of_mem_iff excludedOne excludedTwo
        excludedEquivalent unit
  unfold localizedRule3ExtendedNodePhysicalUnit?
    localizedRule3ExtendedShortCircuitNodeWithRead?
  simp only [routed, Option.pure_apply]
  exact input.localizedRule3ConditionalNodePhysicalUnit_exclusion_policy
    (fun result => input.localizedRule3ShortCircuitOddSpatialObservation result)
    excludedOne excludedTwo containsEq _ _ spatial

/-- **The ordinary-route node law under conditional geometry.**  When the odd route is absent and
the ordinary route certificate is present, the same projected physical identity is synchronized
under the conditional geometry domain and request-local callback facts on the actual extended
request list.  The physical double bond used by the positive branch is derived from the actual
topology frame inside the spatial theorem, never assumed by the caller. -/
theorem localizedRule3ExtendedNodePhysicalUnit?_eq_of_ordinaryRouteConditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none)
    (routed : input.localizedRule3OrdinaryRouteCertificate? occurrence = some certificate)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) after)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (excludedEquivalent : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ excludedOne ↔ unit ∈ excludedTwo) :
    input.localizedRule3ExtendedNodePhysicalUnit?
        targetOne occurrence viewOne readOne before excludedOne =
      input.localizedRule3ExtendedNodePhysicalUnit?
        targetTwo occurrence viewTwo readTwo after excludedTwo := by
  have spatialAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortSpatialCallbackRequests occurrence) before after := by
    intro cursors member
    exact isSomeAgree cursors
      (by simpa only [rule3ExtendedNodeCallbackRequests, oddNone,
        rule3NodeCallbackRequests, routed] using member)
  have spatialBeforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortSpatialCallbackRequests occurrence) before := by
    intro cursors member frame succeeds
    exact beforeShape cursors
      (by simpa only [rule3ExtendedNodeCallbackRequests, oddNone,
        rule3NodeCallbackRequests, routed] using member) frame succeeds
  have spatialAfterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortSpatialCallbackRequests occurrence) after := by
    intro cursors member frame succeeds
    exact afterShape cursors
      (by simpa only [rule3ExtendedNodeCallbackRequests, oddNone,
        rule3NodeCallbackRequests, routed] using member) frame succeeds
  have spatial :=
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_conditionalGeometry
      targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
      certificate oddNone routed geometry spatialAgree spatialBeforeShape
      spatialAfterShape
  have containsEq : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      excludedOne.contains unit = excludedTwo.contains unit :=
    fun unit =>
      input.localizedRule3PhysicalUnitContains_eq_of_mem_iff excludedOne excludedTwo
        excludedEquivalent unit
  unfold localizedRule3ExtendedNodePhysicalUnit?
    localizedRule3ExtendedShortCircuitNodeWithRead?
    localizedRule3ShortCircuitNodeWithRead?
  simp only [oddNone, routed, Option.pure_apply]
  exact input.localizedRule3ConditionalNodePhysicalUnit_exclusion_policy
    (fun result => input.localizedRule3ShortCircuitSpatialObservation result)
    excludedOne excludedTwo containsEq _ _ spatial

/-! ## The main failure-complete node law -/









theorem localizedRule3ExtendedNodePhysicalUnit?_eq_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) after)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (excludedEquivalent : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ excludedOne ↔ unit ∈ excludedTwo) :
    input.localizedRule3ExtendedNodePhysicalUnit?
        targetOne occurrence viewOne readOne before excludedOne =
      input.localizedRule3ExtendedNodePhysicalUnit?
        targetTwo occurrence viewTwo readTwo after excludedTwo := by
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      exact
        input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_oddRouteConditionalGeometry
          targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
          certificate routed geometry isSomeAgree beforeShape afterShape excludedOne
          excludedTwo excludedEquivalent
  | none =>
      cases ordinary : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some certificate =>
          exact
            input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_ordinaryRouteConditionalGeometry
              targetOne targetTwo viewOne viewTwo readOne readTwo before after
              occurrence certificate routed ordinary geometry isSomeAgree beforeShape
              afterShape excludedOne excludedTwo excludedEquivalent
      | none =>
          exact
            input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_jointNone
              targetOne targetTwo viewOne viewTwo readOne readTwo before after
              occurrence routed ordinary excludedOne excludedTwo

/-- **The all-occurrence form.**  Supplying the conditional geometry domain for every occurrence
yields the node law at every occurrence, with no reachability or fuel premise.  This is the intended
entry point for a recursive successor: the exact predecessor frame hypothesis supplies the
request-local callback premises at the current occurrence, while the independent conditional
geometry domain is supplied separately by the successor's own geometry construction. -/
theorem localizedRule3ExtendedNodePhysicalUnit?_eq_of_conditionalGeometryAll
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) after)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (excludedEquivalent : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ excludedOne ↔ unit ∈ excludedTwo) :
    input.localizedRule3ExtendedNodePhysicalUnit?
        targetOne occurrence viewOne readOne before excludedOne =
      input.localizedRule3ExtendedNodePhysicalUnit?
        targetTwo occurrence viewTwo readTwo after excludedTwo :=
  input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_conditionalGeometry
    targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
    (geometry occurrence) isSomeAgree beforeShape afterShape excludedOne excludedTwo
    excludedEquivalent

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ConditionalEndpointSelector_isSome_eq_of_targets
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedNodeConditionalGeometryDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ConditionalNodePhysicalUnit_exclusion_policy
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?_eq_of_oddRouteConditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?_eq_of_ordinaryRouteConditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?_eq_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?_eq_of_conditionalGeometryAll
