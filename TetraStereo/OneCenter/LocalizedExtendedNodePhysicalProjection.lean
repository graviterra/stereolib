import TetraStereo.OneCenter.LocalizedRule3GeometryDefinedness
import TetraStereo.OneCenter.LocalizedRule3PhysicalIncidence
import TetraStereo.OneCenter.LocalizedExtendedFallbackNoRead
import TetraStereo.OneCenter.LocalizedRule3GeometryRefusalSync
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



























































namespace TetraStereo.OneCenter

universe u

/-- The bind of a `some` value in the `Option` monad is definitionally the applied continuation. -/
private theorem option_some_bind_apply
    {α β : Type u} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-- A bind whose continuation is a `some` of a function value has the same `isSome` as its input.
In particular a compiler's success flag is exactly the selector's success flag on the tied
branch. -/
private theorem option_bind_some_isSome
    {α β : Type u} (value : Option α) (f : α → β) :
    ((value >>= fun a => some (f a)) : Option β).isSome = value.isSome := by
  cases value <;> rfl

namespace CertifiedLocalizedCIPInput

/-! ## Synchronized callback success with the exact two-key frame shape -/

/-- Two Rule-3 frame callbacks are synchronized at one actual selected reference-cursor pair when
they agree on whether they succeed and, whenever they succeed, both returned frames have exactly
two Rule-3 keys.  Two keys is exactly the shape the endpoint compiler accepts; a synchronized
successful pair therefore compiles on both sides, while a synchronized failing pair refuses on both
sides before any label reader is consulted. -/
def LocalizedRule3SynchronizedPairFrameSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  (before [firstCursor, secondCursor]).isSome =
      (after [firstCursor, secondCursor]).isSome ∧
    (∀ frame, before [firstCursor, secondCursor] = some frame → frame.keys.length = 2) ∧
    (∀ frame, after [firstCursor, secondCursor] = some frame → frame.keys.length = 2)

/-- The synchronization relation is symmetric. -/
theorem LocalizedRule3SynchronizedPairFrameSupport.symm
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    (synchronized :
      input.LocalizedRule3SynchronizedPairFrameSupport before after firstCursor secondCursor) :
    input.LocalizedRule3SynchronizedPairFrameSupport after before firstCursor secondCursor :=
  ⟨synchronized.1.symm, synchronized.2.2, synchronized.2.1⟩

/-! ## Membership transport for the exclusion policy -/

/-- Two exclusion lists with the same membership induce the same `contains` test at every physical
unit identity.  This is the only property of the exclusion lists used by the node-level policy. -/
theorem localizedRule3PhysicalUnitContains_eq_of_mem_iff
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRule3PhysicalUnitId)
    (sameMembership : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ left ↔ unit ∈ right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    left.contains unit = right.contains unit := by
  by_cases present : unit ∈ left
  · have presentRight : unit ∈ right := (sameMembership unit).mp present
    simp [List.contains_eq_mem, present, presentRight]
  · have absentRight : unit ∉ right := fun inRight => present ((sameMembership unit).mpr inRight)
    simp [List.contains_eq_mem, present, absentRight]

/-! ## Endpoint compilation under synchronized callbacks -/

/-- A refused synchronized callback refuses the endpoint compiler: the compiler is callback-first,
so `none` at the actual selected reference pair is terminal and no label read occurs. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_none_of_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (callbackNone : rule3FrameOf [firstCursor, secondCursor] = none) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = none := by
  rw [input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
    target view read rule3FrameOf endpoint partner first second endpointCursor
    firstCursor secondCursor candidates firstSelected secondSelected]
  simp [callbackNone]

/-- **Endpoint compilation success is synchronized.**  Under synchronized pair-frame support at the
actual selected reference pair, the two endpoint compilers either both refuse (synchronized `none`)
or both succeed (synchronized frames with exactly two keys, whose two compound Rules-4/5 keys are
constructed for every reader at the occurrence budget). -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_synchronized
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (synchronized :
      input.LocalizedRule3SynchronizedPairFrameSupport before after firstCursor secondCursor) :
    (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        targetOne viewOne readOne before endpoint partner endpointCursor).isSome =
      (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        targetTwo viewTwo readTwo after endpoint partner endpointCursor).isSome := by
  rw [input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
        targetOne viewOne readOne before endpoint partner first second endpointCursor
        firstCursor secondCursor candidates firstSelected secondSelected,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
        targetTwo viewTwo readTwo after endpoint partner first second endpointCursor
        firstCursor secondCursor candidates firstSelected secondSelected]
  have firstValid : input.LocalizedRerootCursorValid firstCursor :=
    input.localizedRule3ReferenceCursorExec?_valid endpointCursor firstCursor first firstSelected
  have secondValid : input.LocalizedRerootCursorValid secondCursor :=
    input.localizedRule3ReferenceCursorExec?_valid endpointCursor secondCursor second secondSelected
  cases beforeEq : before [firstCursor, secondCursor] with
  | none =>
      have synchronizedSome := synchronized.1
      rw [beforeEq] at synchronizedSome
      cases afterEq : after [firstCursor, secondCursor] with
      | none => simp [beforeEq, afterEq]
      | some frame => simp [afterEq] at synchronizedSome
  | some frameBefore =>
      have lengthBefore := synchronized.2.1 frameBefore beforeEq
      have synchronizedSome := synchronized.1
      rw [beforeEq] at synchronizedSome
      cases afterEq : after [firstCursor, secondCursor] with
      | none => simp [afterEq] at synchronizedSome
      | some frameAfter =>
          have lengthAfter := synchronized.2.2 frameAfter afterEq
          cases keysBefore : frameBefore.keys with
          | nil => simp [keysBefore] at lengthBefore
          | cons firstRule3Before restBefore =>
              cases restBefore with
              | nil => simp [keysBefore] at lengthBefore
              | cons secondRule3Before restBefore =>
                  cases restBefore with
                  | nil =>
                      cases keysAfter : frameAfter.keys with
                      | nil => simp [keysAfter] at lengthAfter
                      | cons firstRule3After restAfter =>
                          cases restAfter with
                          | nil => simp [keysAfter] at lengthAfter
                          | cons secondRule3After restAfter =>
                              cases restAfter with
                              | nil =>
                                  obtain ⟨firstKeyOne, firstKeyOneComputed⟩ :=
                                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                                      readOne firstCursor firstValid
                                  obtain ⟨secondKeyOne, secondKeyOneComputed⟩ :=
                                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                                      readOne secondCursor secondValid
                                  obtain ⟨firstKeyTwo, firstKeyTwoComputed⟩ :=
                                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                                      readTwo firstCursor firstValid
                                  obtain ⟨secondKeyTwo, secondKeyTwoComputed⟩ :=
                                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                                      readTwo secondCursor secondValid
                                  simp only [
                                    show localizedOccurrenceRerootEvaluationFuel carrierFuel =
                                      2 * (carrierFuel + 1) from rfl,
                                    keysBefore, keysAfter,
                                    firstKeyOneComputed, option_some_bind_apply,
                                    secondKeyOneComputed, option_some_bind_apply,
                                    firstKeyTwoComputed, option_some_bind_apply,
                                    secondKeyTwoComputed, option_some_bind_apply,
                                    Option.isSome_some]
                              | cons thirdRule3After restAfter =>
                                  simp [keysAfter] at lengthAfter
                  | cons thirdRule3Before restBefore =>
                      simp [keysBefore] at lengthBefore

/-! ## Selector synchronization -/

/-- **Short-circuit selector success is synchronized.**  Under synchronized pair-frame support at
the actual selected reference pair, the two parametric short-circuit selectors either both refuse
or both succeed.  The four structural comparison branches are reader- and callback-independent and
decide identically on both sides; the completely tied branch is the endpoint compiler above. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_synchronized
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (synchronized :
      input.LocalizedRule3SynchronizedPairFrameSupport before after firstCursor secondCursor) :
    (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        targetOne viewOne readOne before endpoint partner endpointCursor).isSome =
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        targetTwo viewTwo readTwo after endpoint partner endpointCursor).isSome := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  simp only [firstSelected, option_some_bind_apply, secondSelected, option_some_bind_apply]
  generalize rootComparison :
    input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = rootOrdering
  cases rootOrdering with
  | gt => rfl
  | lt => rfl
  | eq =>
      generalize constitutionalComparison :
        input.compareLocalizedConstitutionalCursors? firstCursor secondCursor =
          constitutionalOrdering
      cases constitutionalOrdering with
      | none =>
          rw [option_bind_some_isSome, option_bind_some_isSome]
          exact
            input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_synchronized
              targetOne targetTwo viewOne viewTwo readOne readTwo before after
              endpoint partner first second endpointCursor firstCursor secondCursor
              candidates firstSelected secondSelected synchronized
      | some ordering =>
          cases ordering with
          | gt => rfl
          | lt => rfl
          | eq =>
              rw [option_bind_some_isSome, option_bind_some_isSome]
              exact
                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_synchronized
                  targetOne targetTwo viewOne viewTwo readOne readTwo before after
                  endpoint partner first second endpointCursor firstCursor secondCursor
                  candidates firstSelected secondSelected synchronized

/-! ## Route failure propagates through the spatial wrappers -/

/-- A refusing left endpoint selector makes the ordinary spatial wrapper refuse, whatever the
callback or reader does at the right endpoint. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_leftEndpoint_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (leftNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.left topology.right topology.leftCursor = none) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
      target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitSpatialUnitWithRead?
  rw [found, option_some_bind_apply, leftNone]
  rfl

/-- A refusing right endpoint selector makes the ordinary spatial wrapper refuse once the left
endpoint has succeeded. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_rightEndpoint_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (leftEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.left topology.right topology.leftCursor =
        some leftEndpoint)
    (rightNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.left topology.rightCursor = none) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
      target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitSpatialUnitWithRead?
  rw [found, option_some_bind_apply, leftComputed, option_some_bind_apply, rightNone]
  rfl

/-- A refusing left endpoint selector makes the odd spatial wrapper refuse. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_leftEndpoint_none
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
    (leftNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.initial.left topology.initial.right
        topology.initial.leftCursor = none) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithRead?
      target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithRead?
  rw [found, option_some_bind_apply, leftNone]
  rfl

/-- A refusing right endpoint selector makes the odd spatial wrapper refuse once the left endpoint
has succeeded. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_rightEndpoint_none
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
    (leftEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.initial.left topology.initial.right
        topology.initial.leftCursor = some leftEndpoint)
    (rightNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.rightPartner
        topology.rightCursor = none) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithRead?
      target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithRead?
  rw [found, option_some_bind_apply, leftComputed, option_some_bind_apply, rightNone]
  rfl

/-! ## Membership-equivalent exclusion lists preserve the node projection -/

/-- The actual physical-unit exclusion policy applied after any successful spatial wrapper is
invariant under membership-equivalent exclusion lists, including the `some none` cancellation case.
The two wrappers must project to the same physical identity at every successful result; the E/Z
geometry and all other fields of the spatial result are unconstrained. -/
private theorem option_map_nodePhysicalUnit_exclusion_policy
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

/-! ## Synchronized spatial identity on the ordinary route -/

/-- **The ordinary spatial wrapper's projected identity is synchronized.**  The two arbitrary
readers and the two arbitrary callbacks may differ; the targets and dependency views may differ.
Under synchronized pair-frame support on both actual candidate pairs and independent readiness of
the four candidate pairings, the two projected physical identities are equal.  No successful spatial
result is assumed: if either wrapper refuses, so does the other, and the common value is `none`. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_synchronized
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
      input.LocalizedRerootCursor carrierFuel)
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
    (leftSynchronized : input.LocalizedRule3SynchronizedPairFrameSupport
      before after leftFirstCursor leftSecondCursor)
    (rightSynchronized : input.LocalizedRule3SynchronizedPairFrameSupport
      before after rightFirstCursor rightSecondCursor)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.left topology.right leftFirst leftSecond rightFirst rightSecond) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        targetOne occurrence viewOne readOne before =
      input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        targetTwo occurrence viewTwo readTwo after := by
  have leftSync :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_synchronized
      targetOne targetTwo viewOne viewTwo readOne readTwo before after
      topology.left topology.right leftFirst leftSecond topology.leftCursor
      leftFirstCursor leftSecondCursor leftCandidates leftFirstSelected leftSecondSelected
      leftSynchronized
  have rightSync :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_synchronized
      targetOne targetTwo viewOne viewTwo readOne readTwo before after
      topology.right topology.left rightFirst rightSecond topology.rightCursor
      rightFirstCursor rightSecondCursor rightCandidates rightFirstSelected rightSecondSelected
      rightSynchronized
  cases leftOne : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      targetOne viewOne readOne before topology.left topology.right topology.leftCursor with
  | none =>
      have leftTwo : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          targetTwo viewTwo readTwo after topology.left topology.right
            topology.leftCursor = none := by
        cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            targetTwo viewTwo readTwo after topology.left topology.right
              topology.leftCursor with
        | none => rfl
        | some result =>
            rw [leftOne, h] at leftSync
            simp only [Option.isSome_none, Option.isSome_some] at leftSync
            cases leftSync
      have unitOne :=
        input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_leftEndpoint_none
          targetOne occurrence viewOne readOne before topology found leftOne
      have unitTwo :=
        input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_leftEndpoint_none
          targetTwo occurrence viewTwo readTwo after topology found leftTwo
      simp [localizedRule3ShortCircuitSpatialPhysicalUnit?, unitOne, unitTwo]
  | some leftEndpointOne =>
      cases rightOne : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          targetOne viewOne readOne before topology.right topology.left
            topology.rightCursor with
      | none =>
          have leftTwoExists : ∃ leftEndpointTwo,
              input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.left topology.right
                  topology.leftCursor = some leftEndpointTwo := by
            cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.left topology.right
                  topology.leftCursor with
            | none =>
                rw [leftOne, h] at leftSync
                simp only [Option.isSome_none, Option.isSome_some] at leftSync
                cases leftSync
            | some result => exact ⟨result, rfl⟩
          obtain ⟨leftEndpointTwo, leftTwo⟩ := leftTwoExists
          have rightTwo : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
              targetTwo viewTwo readTwo after topology.right topology.left
                topology.rightCursor = none := by
            cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.right topology.left
                  topology.rightCursor with
            | none => rfl
            | some result =>
                rw [rightOne, h] at rightSync
                simp only [Option.isSome_none, Option.isSome_some] at rightSync
                cases rightSync
          have unitOne :=
            input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_rightEndpoint_none
              targetOne occurrence viewOne readOne before topology found leftEndpointOne
              leftOne rightOne
          have unitTwo :=
            input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_rightEndpoint_none
              targetTwo occurrence viewTwo readTwo after topology found leftEndpointTwo
              leftTwo rightTwo
          simp [localizedRule3ShortCircuitSpatialPhysicalUnit?, unitOne, unitTwo]
      | some rightEndpointOne =>
          have leftTwoExists : ∃ leftEndpointTwo,
              input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.left topology.right
                  topology.leftCursor = some leftEndpointTwo := by
            cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.left topology.right
                  topology.leftCursor with
            | none =>
                rw [leftOne, h] at leftSync
                simp only [Option.isSome_none, Option.isSome_some] at leftSync
                cases leftSync
            | some result => exact ⟨result, rfl⟩
          obtain ⟨leftEndpointTwo, leftTwo⟩ := leftTwoExists
          have rightTwoExists : ∃ rightEndpointTwo,
              input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.right topology.left
                  topology.rightCursor = some rightEndpointTwo := by
            cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.right topology.left
                  topology.rightCursor with
            | none =>
                rw [rightOne, h] at rightSync
                simp only [Option.isSome_none, Option.isSome_some] at rightSync
                cases rightSync
            | some result => exact ⟨result, rfl⟩
          obtain ⟨rightEndpointTwo, rightTwo⟩ := rightTwoExists
          have doubleBond : input.moleculeGraph.bond topology.left topology.right = 2 :=
            (input.localizedRule3PhysicalEndpointCursorFrameExec?_sound
              occurrence topology found).2.2.2.1
          have readyOne : input.LocalizedRule3AxisGeometryReadiness
              topology.left topology.right leftEndpointOne.priority
                rightEndpointOne.priority :=
            input.localizedRule3AxisGeometryReadiness_of_candidates
              topology.left topology.right leftFirst leftSecond rightFirst rightSecond
              leftEndpointOne.priority rightEndpointOne.priority candidateReady
              (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
                targetOne viewOne readOne before topology.left topology.right leftFirst
                leftSecond topology.leftCursor leftCandidates leftEndpointOne leftOne)
              (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
                targetOne viewOne readOne before topology.right topology.left rightFirst
                rightSecond topology.rightCursor rightCandidates rightEndpointOne rightOne)
          have readyTwo : input.LocalizedRule3AxisGeometryReadiness
              topology.left topology.right leftEndpointTwo.priority
                rightEndpointTwo.priority :=
            input.localizedRule3AxisGeometryReadiness_of_candidates
              topology.left topology.right leftFirst leftSecond rightFirst rightSecond
              leftEndpointTwo.priority rightEndpointTwo.priority candidateReady
              (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
                targetTwo viewTwo readTwo after topology.left topology.right leftFirst
                leftSecond topology.leftCursor leftCandidates leftEndpointTwo leftTwo)
              (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
                targetTwo viewTwo readTwo after topology.right topology.left rightFirst
                rightSecond topology.rightCursor rightCandidates rightEndpointTwo rightTwo)
          rw [
            input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_endpoints
              targetOne occurrence viewOne readOne before topology found leftEndpointOne
              rightEndpointOne leftOne rightOne doubleBond readyOne,
            input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_endpoints
              targetTwo occurrence viewTwo readTwo after topology found leftEndpointTwo
              rightEndpointTwo leftTwo rightTwo doubleBond readyTwo]

/-! ## Synchronized spatial identity on the odd-cumulene route -/

/-- **The odd spatial wrapper's projected identity is synchronized.**  The same independent
candidate-pair readiness and synchronized pair-frame support give the same projected physical
identity on the odd-cumulene route.  There is no adjacent double-bond premise on this route. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_synchronized
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
      input.LocalizedRerootCursor carrierFuel)
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
    (leftSynchronized : input.LocalizedRule3SynchronizedPairFrameSupport
      before after leftFirstCursor leftSecondCursor)
    (rightSynchronized : input.LocalizedRule3SynchronizedPairFrameSupport
      before after rightFirstCursor rightSecondCursor)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        targetOne occurrence viewOne readOne before =
      input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        targetTwo occurrence viewTwo readTwo after := by
  have leftSync :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_synchronized
      targetOne targetTwo viewOne viewTwo readOne readTwo before after
      topology.initial.left topology.initial.right leftFirst leftSecond
      topology.initial.leftCursor leftFirstCursor leftSecondCursor leftCandidates
      leftFirstSelected leftSecondSelected leftSynchronized
  have rightSync :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_synchronized
      targetOne targetTwo viewOne viewTwo readOne readTwo before after
      topology.right topology.rightPartner rightFirst rightSecond topology.rightCursor
      rightFirstCursor rightSecondCursor rightCandidates rightFirstSelected
      rightSecondSelected rightSynchronized
  cases leftOne : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      targetOne viewOne readOne before topology.initial.left topology.initial.right
        topology.initial.leftCursor with
  | none =>
      have leftTwo : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          targetTwo viewTwo readTwo after topology.initial.left topology.initial.right
            topology.initial.leftCursor = none := by
        cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            targetTwo viewTwo readTwo after topology.initial.left topology.initial.right
              topology.initial.leftCursor with
        | none => rfl
        | some result =>
            rw [leftOne, h] at leftSync
            simp only [Option.isSome_none, Option.isSome_some] at leftSync
            cases leftSync
      have unitOne :=
        input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_leftEndpoint_none
          targetOne occurrence viewOne readOne before topology found leftOne
      have unitTwo :=
        input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_leftEndpoint_none
          targetTwo occurrence viewTwo readTwo after topology found leftTwo
      simp [localizedRule3ShortCircuitOddSpatialPhysicalUnit?, unitOne, unitTwo]
  | some leftEndpointOne =>
      cases rightOne : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          targetOne viewOne readOne before topology.right topology.rightPartner
            topology.rightCursor with
      | none =>
          have leftTwoExists : ∃ leftEndpointTwo,
              input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.initial.left topology.initial.right
                  topology.initial.leftCursor = some leftEndpointTwo := by
            cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.initial.left topology.initial.right
                  topology.initial.leftCursor with
            | none =>
                rw [leftOne, h] at leftSync
                simp only [Option.isSome_none, Option.isSome_some] at leftSync
                cases leftSync
            | some result => exact ⟨result, rfl⟩
          obtain ⟨leftEndpointTwo, leftTwo⟩ := leftTwoExists
          have rightTwo : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
              targetTwo viewTwo readTwo after topology.right topology.rightPartner
                topology.rightCursor = none := by
            cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.right topology.rightPartner
                  topology.rightCursor with
            | none => rfl
            | some result =>
                rw [rightOne, h] at rightSync
                simp only [Option.isSome_none, Option.isSome_some] at rightSync
                cases rightSync
          have unitOne :=
            input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_rightEndpoint_none
              targetOne occurrence viewOne readOne before topology found leftEndpointOne
              leftOne rightOne
          have unitTwo :=
            input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_rightEndpoint_none
              targetTwo occurrence viewTwo readTwo after topology found leftEndpointTwo
              leftTwo rightTwo
          simp [localizedRule3ShortCircuitOddSpatialPhysicalUnit?, unitOne, unitTwo]
      | some rightEndpointOne =>
          have leftTwoExists : ∃ leftEndpointTwo,
              input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.initial.left topology.initial.right
                  topology.initial.leftCursor = some leftEndpointTwo := by
            cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.initial.left topology.initial.right
                  topology.initial.leftCursor with
            | none =>
                rw [leftOne, h] at leftSync
                simp only [Option.isSome_none, Option.isSome_some] at leftSync
                cases leftSync
            | some result => exact ⟨result, rfl⟩
          obtain ⟨leftEndpointTwo, leftTwo⟩ := leftTwoExists
          have rightTwoExists : ∃ rightEndpointTwo,
              input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.right topology.rightPartner
                  topology.rightCursor = some rightEndpointTwo := by
            cases h : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
                targetTwo viewTwo readTwo after topology.right topology.rightPartner
                  topology.rightCursor with
            | none =>
                rw [rightOne, h] at rightSync
                simp only [Option.isSome_none, Option.isSome_some] at rightSync
                cases rightSync
            | some result => exact ⟨result, rfl⟩
          obtain ⟨rightEndpointTwo, rightTwo⟩ := rightTwoExists
          have readyOne : input.LocalizedRule3AxisGeometryReadiness
              topology.initial.left topology.right leftEndpointOne.priority
                rightEndpointOne.priority :=
            input.localizedRule3AxisGeometryReadiness_of_candidates
              topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
              leftEndpointOne.priority rightEndpointOne.priority candidateReady
              (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
                targetOne viewOne readOne before topology.initial.left topology.initial.right
                leftFirst leftSecond topology.initial.leftCursor leftCandidates
                leftEndpointOne leftOne)
              (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
                targetOne viewOne readOne before topology.right topology.rightPartner
                rightFirst rightSecond topology.rightCursor rightCandidates
                rightEndpointOne rightOne)
          have readyTwo : input.LocalizedRule3AxisGeometryReadiness
              topology.initial.left topology.right leftEndpointTwo.priority
                rightEndpointTwo.priority :=
            input.localizedRule3AxisGeometryReadiness_of_candidates
              topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
              leftEndpointTwo.priority rightEndpointTwo.priority candidateReady
              (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
                targetTwo viewTwo readTwo after topology.initial.left topology.initial.right
                leftFirst leftSecond topology.initial.leftCursor leftCandidates
                leftEndpointTwo leftTwo)
              (input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
                targetTwo viewTwo readTwo after topology.right topology.rightPartner
                rightFirst rightSecond topology.rightCursor rightCandidates
                rightEndpointTwo rightTwo)
          rw [
            input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_endpoints
              targetOne occurrence viewOne readOne before topology found leftEndpointOne
              rightEndpointOne leftOne rightOne readyOne,
            input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_endpoints
              targetTwo occurrence viewTwo readTwo after topology found leftEndpointTwo
              rightEndpointTwo leftTwo rightTwo readyTwo]

/-! ## The projected physical identity of the actual extended node -/





noncomputable def localizedRule3ExtendedNodePhysicalUnit?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option input.LocalizedRule3PhysicalUnitId) :=
  Option.map (Option.map LocalizedRule3SpatialNodeResult.physicalUnitId)
    (input.localizedRule3ExtendedShortCircuitNodeWithRead?
      target occurrence view read callback excluded)

/-- **The odd-route node law.**  When the actual dispatch takes the checked odd route, the
projected physical identity of the extended node is synchronized across two arbitrary readers,
two arbitrary callbacks, two targets and dependency views, and two membership-equivalent exclusion
lists, under synchronized pair-frame support and independent candidate-pair readiness.  The law is
conditional only on the actual route being taken; it does not assume that either spatial wrapper
succeeds, that either callback succeeds, or that the endpoint priorities agree. -/
theorem localizedRule3ExtendedNodePhysicalUnit?_eq_of_oddRoute
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
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
      input.LocalizedRerootCursor carrierFuel)
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
    (leftSynchronized : input.LocalizedRule3SynchronizedPairFrameSupport
      before after leftFirstCursor leftSecondCursor)
    (rightSynchronized : input.LocalizedRule3SynchronizedPairFrameSupport
      before after rightFirstCursor rightSecondCursor)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (excludedEquivalent : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ excludedOne ↔ unit ∈ excludedTwo) :
    input.localizedRule3ExtendedNodePhysicalUnit?
        targetOne occurrence viewOne readOne before excludedOne =
      input.localizedRule3ExtendedNodePhysicalUnit?
        targetTwo occurrence viewTwo readTwo after excludedTwo := by
  have spatial :=
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_synchronized
      targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
      topology found leftFirst leftSecond rightFirst rightSecond leftFirstCursor
      leftSecondCursor rightFirstCursor rightSecondCursor leftCandidates rightCandidates
      leftFirstSelected leftSecondSelected rightFirstSelected rightSecondSelected
      leftSynchronized rightSynchronized candidateReady
  have containsEq : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      excludedOne.contains unit = excludedTwo.contains unit :=
    fun unit =>
      input.localizedRule3PhysicalUnitContains_eq_of_mem_iff excludedOne excludedTwo
        excludedEquivalent unit
  unfold localizedRule3ExtendedNodePhysicalUnit?
    localizedRule3ExtendedShortCircuitNodeWithRead?
  simp only [routed, Option.pure_apply]
  exact option_map_nodePhysicalUnit_exclusion_policy input
    (fun result => input.localizedRule3ShortCircuitOddSpatialObservation result)
    excludedOne excludedTwo containsEq _ _ spatial

/-- **The ordinary-route node law.**  When the odd route is not taken and the ordinary route
certificate is present, the same projected physical identity is synchronized under the same
reader-, callback- and priority-independent conditions.  The physical double bond required by the
ordinary geometry is derived from the actual executable topology frame, not assumed. -/
theorem localizedRule3ExtendedNodePhysicalUnit?_eq_of_ordinaryRoute
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
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
      input.LocalizedRerootCursor carrierFuel)
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
    (leftSynchronized : input.LocalizedRule3SynchronizedPairFrameSupport
      before after leftFirstCursor leftSecondCursor)
    (rightSynchronized : input.LocalizedRule3SynchronizedPairFrameSupport
      before after rightFirstCursor rightSecondCursor)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.left topology.right leftFirst leftSecond rightFirst rightSecond)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (excludedEquivalent : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ excludedOne ↔ unit ∈ excludedTwo) :
    input.localizedRule3ExtendedNodePhysicalUnit?
        targetOne occurrence viewOne readOne before excludedOne =
      input.localizedRule3ExtendedNodePhysicalUnit?
        targetTwo occurrence viewTwo readTwo after excludedTwo := by
  have spatial :=
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_synchronized
      targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
      topology found leftFirst leftSecond rightFirst rightSecond leftFirstCursor
      leftSecondCursor rightFirstCursor rightSecondCursor leftCandidates rightCandidates
      leftFirstSelected leftSecondSelected rightFirstSelected rightSecondSelected
      leftSynchronized rightSynchronized candidateReady
  have containsEq : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      excludedOne.contains unit = excludedTwo.contains unit :=
    fun unit =>
      input.localizedRule3PhysicalUnitContains_eq_of_mem_iff excludedOne excludedTwo
        excludedEquivalent unit
  unfold localizedRule3ExtendedNodePhysicalUnit?
    localizedRule3ExtendedShortCircuitNodeWithRead?
    localizedRule3ShortCircuitNodeWithRead?
  simp only [oddNone, routed, Option.pure_apply]
  exact option_map_nodePhysicalUnit_exclusion_policy input
    (fun result => input.localizedRule3ShortCircuitSpatialObservation result)
    excludedOne excludedTwo containsEq _ _ spatial






theorem localizedRule3ExtendedNodePhysicalUnit?_eq_of_jointNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (oddNone : input.localizedRule3OddRouteCertificate? occurrence = none)
    (ordinaryNone : input.localizedRule3OrdinaryRouteCertificate? occurrence = none)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedNodePhysicalUnit?
        targetOne occurrence viewOne readOne before excludedOne =
      input.localizedRule3ExtendedNodePhysicalUnit?
        targetTwo occurrence viewTwo readTwo after excludedTwo := by
  unfold localizedRule3ExtendedNodePhysicalUnit?
    localizedRule3ExtendedShortCircuitNodeWithRead?
    localizedRule3ShortCircuitNodeWithRead?
  simp only [oddNone, ordinaryNone]
  rw [input.localizedDescriptorBearingRule3NodeWithExec?_eq_of_jointRouteCertificateNone
    targetOne targetTwo occurrence viewOne viewTwo before after excludedOne excludedTwo
    ordinaryNone oddNone]

/-! ## Structural refusals and reader-independence of the endpoint seam

The route-indexed support predicate below packages a *successful* topology, the two exact candidate
pairs and four successful reference selections.  The actual executable also has structural failure
branches: no topology recovery, a candidate list that is not exactly two elements, or a failed
reference-cursor lookup.  These branches are callback-, reader-, target- and view-independent, so
two arbitrary readers/callbacks refuse together.  The lemmas in this section expose that behaviour
and show that the endpoint compiler's success flag does not depend on the target, the dependency
view or the label reader once the callback is fixed. -/

/-- **The endpoint compiler's `isSome` is reader-, target- and view-independent for a fixed
callback.**  The callback is the only branch source: a refused callback gives `none`; a successful
frame whose key list is not exactly two gives `none`; a successful two-key frame always completes
because both compound through-Rule-5 keys exist at the proved budget for every reader. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_sameCallback
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor) :
    (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        targetOne viewOne readOne rule3FrameOf endpoint partner endpointCursor).isSome =
      (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        targetTwo viewTwo readTwo rule3FrameOf endpoint partner endpointCursor).isSome := by
  rw [input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
        targetOne viewOne readOne rule3FrameOf endpoint partner first second endpointCursor
        firstCursor secondCursor candidates firstSelected secondSelected,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
        targetTwo viewTwo readTwo rule3FrameOf endpoint partner first second endpointCursor
        firstCursor secondCursor candidates firstSelected secondSelected]
  have firstValid : input.LocalizedRerootCursorValid firstCursor :=
    input.localizedRule3ReferenceCursorExec?_valid endpointCursor firstCursor first firstSelected
  have secondValid : input.LocalizedRerootCursorValid secondCursor :=
    input.localizedRule3ReferenceCursorExec?_valid endpointCursor secondCursor second secondSelected
  cases callback : rule3FrameOf [firstCursor, secondCursor] with
  | none => simp [callback]
  | some frame =>
      cases keys : frame.keys with
      | nil => simp [callback, keys]
      | cons firstRule3 rest =>
          cases rest with
          | nil => simp [callback, keys]
          | cons secondRule3 rest =>
              cases rest with
              | cons thirdRule3 rest => simp [callback, keys]
              | nil =>
                  obtain ⟨firstKeyOne, firstKeyOneComputed⟩ :=
                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                      readOne firstCursor firstValid
                  obtain ⟨secondKeyOne, secondKeyOneComputed⟩ :=
                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                      readOne secondCursor secondValid
                  obtain ⟨firstKeyTwo, firstKeyTwoComputed⟩ :=
                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                      readTwo firstCursor firstValid
                  obtain ⟨secondKeyTwo, secondKeyTwoComputed⟩ :=
                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                      readTwo secondCursor secondValid
                  simp only [
                    show localizedOccurrenceRerootEvaluationFuel carrierFuel =
                      2 * (carrierFuel + 1) from rfl,
                    callback, keys,
                    firstKeyOneComputed, option_some_bind_apply,
                    secondKeyOneComputed, option_some_bind_apply,
                    firstKeyTwoComputed, option_some_bind_apply,
                    secondKeyTwoComputed, option_some_bind_apply,
                    Option.isSome_some]

/-- **The short-circuit selector's `isSome` is reader-, target- and view-independent for a fixed
callback.**  The candidate-shape and reference-selection failures are structural; the strict
root/constitutional branches never consult the callback; only the completely tied branch reaches
the endpoint compiler, whose success flag was shown above to be reader/target/view-independent. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_sameCallback
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        targetOne viewOne readOne rule3FrameOf endpoint partner endpointCursor).isSome =
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        targetTwo viewTwo readTwo rule3FrameOf endpoint partner endpointCursor).isSome := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  cases candidates : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil => simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]
      | cons second rest =>
          cases rest with
          | cons third rest =>
              simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]
          | nil =>
              cases firstSelected : input.localizedRule3ReferenceCursorExec?
                  endpointCursor first with
              | none =>
                  simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates,
                    firstSelected]
              | some firstCursor =>
                  cases secondSelected : input.localizedRule3ReferenceCursorExec?
                      endpointCursor second with
                  | none =>
                      simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates,
                        firstSelected, secondSelected]
                  | some secondCursor =>
                      dsimp only
                      simp only [firstSelected, option_some_bind_apply, secondSelected,
                        option_some_bind_apply]
                      generalize rootComparison :
                        input.compareLocalizedRerootCursorConstitutionalRoot
                          firstCursor secondCursor = rootOrdering
                      cases rootOrdering with
                      | gt => rfl
                      | lt => rfl
                      | eq =>
                          generalize constitutionalComparison :
                            input.compareLocalizedConstitutionalCursors?
                              firstCursor secondCursor = constitutionalOrdering
                          cases constitutionalOrdering with
                          | none =>
                              rw [option_bind_some_isSome, option_bind_some_isSome]
                              exact
                                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_sameCallback
                                  targetOne targetTwo viewOne viewTwo readOne readTwo
                                  rule3FrameOf endpoint partner first second endpointCursor
                                  firstCursor secondCursor candidates firstSelected secondSelected
                          | some ordering =>
                              cases ordering with
                              | gt => rfl
                              | lt => rfl
                              | eq =>
                                  rw [option_bind_some_isSome, option_bind_some_isSome]
                                  exact
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_sameCallback
                                      targetOne targetTwo viewOne viewTwo readOne readTwo
                                      rule3FrameOf endpoint partner first second endpointCursor
                                      firstCursor secondCursor candidates firstSelected
                                      secondSelected

/-! ## Structural refusals of the endpoint selector -/

/-- An empty candidate list is a shared structural refusal of the endpoint selector. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = []) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = none := by
  simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]

/-- A one-element candidate list is a shared structural refusal of the endpoint selector. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first]) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = none := by
  simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]

/-- A candidate list with three or more elements is a shared structural refusal of the endpoint
selector. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second third : input.Atom)
    (rest : List input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner =
      first :: second :: third :: rest) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = none := by
  simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]

/-- A failed first reference-cursor lookup is a shared structural refusal of the endpoint
selector. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstNone : input.localizedRule3ReferenceCursorExec? endpointCursor first = none) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = none := by
  simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates, firstNone]

/-- A failed second reference-cursor lookup is a shared structural refusal of the endpoint
selector. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondNone : input.localizedRule3ReferenceCursorExec? endpointCursor second = none) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = none := by
  simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates, firstSelected,
    secondNone]

/-! ## Refusal propagation from a right endpoint without inspecting the left endpoint -/

/-- A refusing right endpoint selector makes the ordinary spatial wrapper refuse whatever the left
selector does: the do-block can only continue through the right bind, which is `none`. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_rightEndpoint_none_free
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (rightNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.left topology.rightCursor = none) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
      target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitSpatialUnitWithRead?
  rw [found, option_some_bind_apply]
  cases leftSelector : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.left topology.right topology.leftCursor with
  | none => rfl
  | some leftEndpoint =>
      rw [option_some_bind_apply, rightNone]
      rfl

/-- The projected physical identity of the ordinary wrapper from a refusing right endpoint. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (rightNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.left topology.rightCursor = none) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
      target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitSpatialPhysicalUnit?
  rw [input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_rightEndpoint_none_free
    target occurrence view read rule3FrameOf topology found rightNone]
  rfl

/-- A refusing right endpoint selector makes the odd spatial wrapper refuse whatever the left
selector does. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_rightEndpoint_none_free
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
    (rightNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.rightPartner
        topology.rightCursor = none) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithRead?
      target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithRead?
  rw [found, option_some_bind_apply]
  cases leftSelector : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.initial.left topology.initial.right
        topology.initial.leftCursor with
  | none => rfl
  | some leftEndpoint =>
      rw [option_some_bind_apply, rightNone]
      rfl

/-- The projected physical identity of the odd wrapper from a refusing right endpoint. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
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
    (rightNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.rightPartner
        topology.rightCursor = none) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
      target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitOddSpatialPhysicalUnit?
  rw [input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_rightEndpoint_none_free
    target occurrence view read rule3FrameOf topology found rightNone]
  rfl

/-! ## The route-indexed support predicate -/

/-- The semantic support required by the actual extended-node dispatch, selected by the actual route
certificates of the occurrence.  On the odd route it packages the actual odd topology, its two
candidate pairs, the four actual reference-cursor selections, synchronized pair-frame support at
both pairs, and the four-pair independent geometry readiness.  On the ordinary route it packages the
same data for the actual physical double-bond frame.  On the joint-failure route no support is
required, because the original eager evaluator is literally callback-, reader- and exclusion-
independent there. -/
def LocalizedRule3ExtendedNodeRoutePhysicalSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | some _ =>
      ∃ (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
        (leftFirst leftSecond rightFirst rightSecond : input.Atom)
        (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
          input.LocalizedRerootCursor carrierFuel),
        input.localizedRule3OddCumuleneEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence =
              some topology ∧
          input.localizedRule3ExplicitSubstituents
              topology.initial.left topology.initial.right = [leftFirst, leftSecond] ∧
          input.localizedRule3ExplicitSubstituents
              topology.right topology.rightPartner = [rightFirst, rightSecond] ∧
          input.localizedRule3ReferenceCursorExec?
              topology.initial.leftCursor leftFirst = some leftFirstCursor ∧
          input.localizedRule3ReferenceCursorExec?
              topology.initial.leftCursor leftSecond = some leftSecondCursor ∧
          input.localizedRule3ReferenceCursorExec?
              topology.rightCursor rightFirst = some rightFirstCursor ∧
          input.localizedRule3ReferenceCursorExec?
              topology.rightCursor rightSecond = some rightSecondCursor ∧
          input.LocalizedRule3SynchronizedPairFrameSupport
              before after leftFirstCursor leftSecondCursor ∧
          input.LocalizedRule3SynchronizedPairFrameSupport
              before after rightFirstCursor rightSecondCursor ∧
          input.LocalizedRule3AxisCandidateGeometryReadiness
              topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
  | none =>
      match input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some _ =>
          ∃ (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
            (leftFirst leftSecond rightFirst rightSecond : input.Atom)
            (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
              input.LocalizedRerootCursor carrierFuel),
            input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence =
                some topology ∧
              input.localizedRule3ExplicitSubstituents
                  topology.left topology.right = [leftFirst, leftSecond] ∧
              input.localizedRule3ExplicitSubstituents
                  topology.right topology.left = [rightFirst, rightSecond] ∧
              input.localizedRule3ReferenceCursorExec?
                  topology.leftCursor leftFirst = some leftFirstCursor ∧
              input.localizedRule3ReferenceCursorExec?
                  topology.leftCursor leftSecond = some leftSecondCursor ∧
              input.localizedRule3ReferenceCursorExec?
                  topology.rightCursor rightFirst = some rightFirstCursor ∧
              input.localizedRule3ReferenceCursorExec?
                  topology.rightCursor rightSecond = some rightSecondCursor ∧
              input.LocalizedRule3SynchronizedPairFrameSupport
                  before after leftFirstCursor leftSecondCursor ∧
              input.LocalizedRule3SynchronizedPairFrameSupport
                  before after rightFirstCursor rightSecondCursor ∧
              input.LocalizedRule3AxisCandidateGeometryReadiness
                  topology.left topology.right leftFirst leftSecond rightFirst rightSecond
      | none => True

/-- **The actual extended node's projected physical identity is route-wise invariant.**  For the
same actual occurrence, with the route-indexed semantic support above and membership-equivalent
exclusion lists, two arbitrary readers, two arbitrary callbacks, two targets and two dependency
views give the same `Option.map (Option.map physicalUnitId)` value.  All three actual dispatch
routes are covered: odd, ordinary, and joint-failure fallback.  The theorem does not assume that the
spatial computation succeeds or that the callbacks succeed; synchronized failure yields the common
value `none`, while readiness makes synchronized success retain the canonical physical endpoint
identity. -/
theorem localizedRule3ExtendedNodePhysicalUnit?_eq_of_routeSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (excludedEquivalent : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ excludedOne ↔ unit ∈ excludedTwo)
    (support : input.LocalizedRule3ExtendedNodeRoutePhysicalSupport
      targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence) :
    input.localizedRule3ExtendedNodePhysicalUnit?
        targetOne occurrence viewOne readOne before excludedOne =
      input.localizedRule3ExtendedNodePhysicalUnit?
        targetTwo occurrence viewTwo readTwo after excludedTwo := by
  revert support
  unfold LocalizedRule3ExtendedNodeRoutePhysicalSupport
  cases oddRoute : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      intro support
      obtain ⟨topology, leftFirst, leftSecond, rightFirst, rightSecond,
        leftFirstCursor, leftSecondCursor, rightFirstCursor, rightSecondCursor,
        found, leftCandidates, rightCandidates, leftFirstSelected, leftSecondSelected,
        rightFirstSelected, rightSecondSelected, leftSynchronized, rightSynchronized,
        candidateReady⟩ := support
      exact input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_oddRoute
        targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
        certificate oddRoute topology found leftFirst leftSecond rightFirst rightSecond
        leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor leftCandidates
        rightCandidates leftFirstSelected leftSecondSelected rightFirstSelected
        rightSecondSelected leftSynchronized rightSynchronized candidateReady
        excludedOne excludedTwo excludedEquivalent
  | none =>
      cases ordinaryRoute : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some certificate =>
          intro support
          obtain ⟨topology, leftFirst, leftSecond, rightFirst, rightSecond,
            leftFirstCursor, leftSecondCursor, rightFirstCursor, rightSecondCursor,
            found, leftCandidates, rightCandidates, leftFirstSelected, leftSecondSelected,
            rightFirstSelected, rightSecondSelected, leftSynchronized, rightSynchronized,
            candidateReady⟩ := support
          exact input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_ordinaryRoute
            targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
            certificate oddRoute ordinaryRoute topology found leftFirst leftSecond
            rightFirst rightSecond
            leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor leftCandidates
            rightCandidates leftFirstSelected leftSecondSelected rightFirstSelected
            rightSecondSelected leftSynchronized rightSynchronized candidateReady
            excludedOne excludedTwo excludedEquivalent
      | none =>
          intro _support
          exact input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_jointNone
            targetOne targetTwo viewOne viewTwo readOne readTwo before after occurrence
            oddRoute ordinaryRoute excludedOne excludedTwo

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3SynchronizedPairFrameSupport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3SynchronizedPairFrameSupport.symm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3PhysicalUnitContains_eq_of_mem_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_none_of_callback_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_synchronized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_synchronized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_leftEndpoint_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_rightEndpoint_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_leftEndpoint_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_rightEndpoint_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_synchronized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_synchronized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?_eq_of_oddRoute
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?_eq_of_ordinaryRoute
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?_eq_of_jointNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedNodeRoutePhysicalSupport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodePhysicalUnit?_eq_of_routeSupport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_sameCallback
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_sameCallback
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_candidates_three
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_firstReference_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_none_of_secondReference_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_none_of_rightEndpoint_none_free
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_none_of_rightEndpoint_none_free
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none_free
