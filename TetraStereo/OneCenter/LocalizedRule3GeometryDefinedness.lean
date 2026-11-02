import TetraStereo.OneCenter.LocalizedRule3DemandRestrictedEndpoint
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddSpatial
import TetraStereo.OneCenter.LocalizedParametricExtendedRule3Key
import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.OneCenter.LocalizedRule3EndpointDemandApplicability
import TetraStereo.OneCenter.LocalizedRule3ActualReferenceDemand
import TetraStereo.OneCenter.LocalizedRerootRule3PhysicalUnit
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

universe u

/-! ## The `Option` bind used by executable `do` blocks is definitional

`>>=` produced by a `do` block is `Bind.bind` with the `Option` instance, definitionally equal to
the primitive `Option.bind` as in the imported executable modules. -/
private theorem option_some_bind_apply
    {α β : Type u} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-!
# Independent Rule-3 geometry readiness and physical identity under arbitrary readers

The occurrence-local Rule-3 endpoint compiler demands a shared Rule-3 frame callback on the two
*actual* reference cursors selected by the executable reference selector, and then demands two
compound through-Rule-5 keys built by an arbitrary label reader.  Earlier layers compare two such
readers by assuming agreement of the callback frames themselves.  Across a restricted and a
whole-state reader the callback may instead return *different* frames, or fail on one side while
succeeding on the other, in exactly the branch where the endpoint priorities tie or become
nonstereogenic.  The geometry layer investigated here is independent of that disagreement:

* `LocalizedRule3ReferenceGeometryReady` is a purely semantic, reader-independent condition on an
  actual reference pair: the four coordinates obtained from `spatialPointAt?` satisfy exact
  coplanarity and a nonvanishing side product.  It says nothing about any key, comparison, frame
  or solver outcome.
* `LocalizedRule3AxisGeometryReadiness` lifts readiness through the two complete endpoint
  priorities read by the executable short-circuit selector.  Nonstereogenic priorities need no
  coordinates at all; two senior priorities need the two actual selected references to be ready.
* A successful priority-keyed spatial unit is *derived* from readiness and the physical double
  bond, for the ordinary and for the odd-cumulene skeleton, by the existing exact classifier
  equivalence.  Missing or degenerate coordinates are not claimed to be total: readiness is an
  explicit domain.
* `localizedRule3ShortCircuitEndpointPriorityWithRead?_exists_of_support` derives endpoint
  selector success from the two-key shape of the callback at the actual reference pair, using the
  universal compound-key availability `exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice`
  and the actual validity of the two selected reference cursors.  The desired compound keys are
  never assumed.
* The physical identity projection
  `localizedRule3ShortCircuitSpatialPhysicalUnit?` maps the spatial wrapper through
  `physicalUnitId ∘ spatialObservation`.  That identity depends only on the physical endpoints,
  not on the E/Z geometry, the priorities, the callback frames or the label reader, so two
  readers with request-local `isSome` agreement and successful two-key callbacks at the two actual
  reference pairs produce exactly the same projected physical identity.

## What is deliberately not claimed

Nothing below asserts equality of the full endpoint keys, equality of the spatial node result, or
that missing coordinates are impossible.  The comparison is only of the projected physical unit
identity, which is exactly the `Option.map (physicalUnitId ∘ spatialObservation)` interface
requested for neutralizing a parent refusal.  Request-local callback `isSome` agreement is retained
as the intermediate induction interface; it is stated explicitly and is weaker than frame equality.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Independent geometry readiness -/

/-- Readiness of one actual reference pair for exact Rule-3 geometry.  The four atoms are read at
their actual semantic coordinates; the pair is ready when the exact scalar triple product vanishes
and the exact side product is nonzero.  No key, comparison, callback frame or solver answer occurs
in this definition. -/
def LocalizedRule3ReferenceGeometryReady
    (input : CertifiedLocalizedCIPInput)
    (left right leftReference rightReference : input.Atom) : Prop :=
  ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint : CartesianPoint3,
    input.spatialPointAt? left = some leftPoint ∧
      input.spatialPointAt? right = some rightPoint ∧
      input.spatialPointAt? leftReference = some leftReferencePoint ∧
      input.spatialPointAt? rightReference = some rightReferencePoint ∧
      CartesianPoint3.rule3Coplanarity leftPoint rightPoint
        leftReferencePoint rightReferencePoint = 0 ∧
      CartesianPoint3.rule3SideProduct leftPoint rightPoint
        leftReferencePoint rightReferencePoint ≠ 0

/-- Readiness produces the actual semantic coordinates together with an exact `seqcis` or
`seqtrans` classifier result.  The sign of the nonvanishing side product selects the branch, so no
classifier success is assumed. -/
theorem localizedRule3ReferenceGeometryReady_exists_geometry
    (input : CertifiedLocalizedCIPInput)
    {left right leftReference rightReference : input.Atom}
    (ready : input.LocalizedRule3ReferenceGeometryReady
      left right leftReference rightReference) :
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint : CartesianPoint3,
      ∃ geometry : OfficialRule3Geometry,
        input.spatialPointAt? left = some leftPoint ∧
          input.spatialPointAt? right = some rightPoint ∧
          input.spatialPointAt? leftReference = some leftReferencePoint ∧
          input.spatialPointAt? rightReference = some rightReferencePoint ∧
          rule3GeometryOfSpatialReferences? leftPoint rightPoint
            leftReferencePoint rightReferencePoint = some geometry ∧
          RationalRule3SpatialGeometry leftPoint rightPoint
            leftReferencePoint rightReferencePoint geometry := by
  obtain ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
    leftComputed, rightComputed, leftReferenceComputed, rightReferenceComputed,
    coplanar, sideNonzero⟩ := ready
  rcases lt_or_gt_of_ne sideNonzero with sideNegative | sidePositive
  · refine ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
      .seqtrans, leftComputed, rightComputed, leftReferenceComputed,
      rightReferenceComputed, ?_, ?_⟩
    · exact (rule3GeometryOfSpatialReferences?_eq_some_iff leftPoint rightPoint
        leftReferencePoint rightReferencePoint .seqtrans).mpr ⟨coplanar, sideNegative⟩
    · exact ⟨coplanar, sideNegative⟩
  · refine ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
      .seqcis, leftComputed, rightComputed, leftReferenceComputed,
      rightReferenceComputed, ?_, ?_⟩
    · exact (rule3GeometryOfSpatialReferences?_eq_some_iff leftPoint rightPoint
        leftReferencePoint rightReferencePoint .seqcis).mpr ⟨coplanar, sidePositive⟩
    · exact ⟨coplanar, sidePositive⟩

/-- Axis readiness: the two complete endpoint priorities of one physical double bond.  A
nonstereogenic priority on either end needs no geometry; two senior priorities require the two
actual selected references to be independently ready. -/
def LocalizedRule3AxisGeometryReadiness
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority) : Prop :=
  match leftPriority, rightPriority with
  | .nonstereogenic, _ => True
  | _, .nonstereogenic => True
  | .senior leftReference, .senior rightReference =>
      input.LocalizedRule3ReferenceGeometryReady left right leftReference rightReference

/-- Candidate-pair readiness: all four pairings of the two actual candidate references at the left
endpoint with the two actual candidate references at the right endpoint are ready.  This is the
reader-independent domain statement; which pairing is actually selected may depend on the reader,
but every possible selection is covered. -/
def LocalizedRule3AxisCandidateGeometryReadiness
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom) : Prop :=
  input.LocalizedRule3ReferenceGeometryReady left right leftFirst rightFirst ∧
    input.LocalizedRule3ReferenceGeometryReady left right leftFirst rightSecond ∧
    input.LocalizedRule3ReferenceGeometryReady left right leftSecond rightFirst ∧
    input.LocalizedRule3ReferenceGeometryReady left right leftSecond rightSecond

/-- Candidate readiness covers every actual senior selection whose references are drawn from the
two candidate pairs.  This is where a reader-dependent strict-or-tied endpoint outcome is related
back to the reader-independent four-pair domain. -/
theorem localizedRule3AxisGeometryReadiness_of_candidates
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      left right leftFirst leftSecond rightFirst rightSecond)
    (leftMember : ∀ reference, leftPriority = .senior reference →
      reference = leftFirst ∨ reference = leftSecond)
    (rightMember : ∀ reference, rightPriority = .senior reference →
      reference = rightFirst ∨ reference = rightSecond) :
    input.LocalizedRule3AxisGeometryReadiness left right leftPriority rightPriority := by
  cases leftPriority with
  | nonstereogenic =>
      cases rightPriority with
      | nonstereogenic => exact trivial
      | senior rightReference => exact trivial
  | senior leftReference =>
      cases rightPriority with
      | nonstereogenic => exact trivial
      | senior rightReference =>
          rcases leftMember leftReference rfl with leftFirstEq | leftSecondEq
          · rcases rightMember rightReference rfl with rightFirstEq | rightSecondEq
            · rw [leftFirstEq, rightFirstEq]
              exact candidateReady.1
            · rw [leftFirstEq, rightSecondEq]
              exact candidateReady.2.1
          · rcases rightMember rightReference rfl with rightFirstEq | rightSecondEq
            · rw [leftSecondEq, rightFirstEq]
              exact candidateReady.2.2.1
            · rw [leftSecondEq, rightSecondEq]
              exact candidateReady.2.2.2

/-! ## Geometry success from readiness -/

/-- Under readiness and the physical double bond, the ordinary priority-keyed spatial skeleton
succeeds.  Nonstereogenic branches return immediately; two senior references use the independently
ready coordinates.  No endpoint key or callback frame is demanded. -/
theorem localizedRule3DescriptorBearingSpatialUnitOfPriorities?_exists_of_readiness
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (doubleBond : input.moleculeGraph.bond left right = 2)
    (ready : input.LocalizedRule3AxisGeometryReadiness left right leftPriority rightPriority) :
    ∃ unit, input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
      left right leftPriority rightPriority = some unit := by
  unfold localizedRule3DescriptorBearingSpatialUnitOfPriorities?
  rw [if_pos doubleBond]
  cases leftPriority with
  | nonstereogenic =>
      cases rightPriority with
      | nonstereogenic => exact ⟨_, rfl⟩
      | senior rightReference => exact ⟨_, rfl⟩
  | senior leftReference =>
      cases rightPriority with
      | nonstereogenic => exact ⟨_, rfl⟩
      | senior rightReference =>
          have readyReferences : input.LocalizedRule3ReferenceGeometryReady
              left right leftReference rightReference := by
            simpa only [LocalizedRule3AxisGeometryReadiness] using ready
          obtain ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
            geometry, leftComputed, rightComputed, leftReferenceComputed,
            rightReferenceComputed, geometryComputed, _meaning⟩ :=
            input.localizedRule3ReferenceGeometryReady_exists_geometry readyReferences
          dsimp only
          rw [leftComputed, rightComputed, leftReferenceComputed, rightReferenceComputed]
          simp only [option_some_bind_apply]
          rw [geometryComputed, option_some_bind_apply]
          exact ⟨_, rfl⟩

/-- Under readiness the odd-cumulene priority-keyed skeleton succeeds.  There is no adjacent
double-bond test at the ends of a cumulated chain, so readiness alone is the geometry domain. -/
theorem localizedRule3ExtendedSpatialUnitOfPriorities?_exists_of_readiness
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (ready : input.LocalizedRule3AxisGeometryReadiness left right leftPriority rightPriority) :
    ∃ unit, input.localizedRule3ExtendedSpatialUnitOfPriorities?
      left right leftPriority rightPriority = some unit := by
  unfold localizedRule3ExtendedSpatialUnitOfPriorities?
  cases leftPriority with
  | nonstereogenic =>
      cases rightPriority with
      | nonstereogenic => exact ⟨_, rfl⟩
      | senior rightReference => exact ⟨_, rfl⟩
  | senior leftReference =>
      cases rightPriority with
      | nonstereogenic => exact ⟨_, rfl⟩
      | senior rightReference =>
          have readyReferences : input.LocalizedRule3ReferenceGeometryReady
              left right leftReference rightReference := by
            simpa only [LocalizedRule3AxisGeometryReadiness] using ready
          obtain ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
            geometry, leftComputed, rightComputed, leftReferenceComputed,
            rightReferenceComputed, geometryComputed, _meaning⟩ :=
            input.localizedRule3ReferenceGeometryReady_exists_geometry readyReferences
          dsimp only
          rw [leftComputed, rightComputed, leftReferenceComputed, rightReferenceComputed]
          simp only [option_some_bind_apply]
          rw [geometryComputed, option_some_bind_apply]
          exact ⟨_, rfl⟩

/-! ## Actual selected cursors and endpoint success -/

/-- A reference cursor selected by the actual executable selector is path-valid.  The child
membership is supplied by `rule3ActualReferenceCursor_child`, and the declarative reading of the
executable child list is unconditional. -/
theorem localizedRule3ReferenceCursorExec?_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : input.Atom)
    (selected : input.localizedRule3ReferenceCursorExec?
      endpointCursor reference = some cursor) :
    input.LocalizedRerootCursorValid cursor := by
  obtain ⟨member, _previous, _current⟩ :=
    input.rule3ActualReferenceCursor_child endpointCursor cursor reference selected
  exact input.localizedRerootChild_valid endpointCursor cursor
    (input.executableLocalizedRerootChildren endpointCursor)
    (input.executableLocalizedRerootChildren_declarative endpointCursor) member

/-- A successful parametric endpoint compilation records the actual candidate pair in its
endpoint frame.  This is the pinned-computation form of the compiler, destructed through the
callback-first program. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_endpointFrame_candidates
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
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = some frame) :
    frame.endpointFrame.first = first ∧ frame.endpointFrame.second = second := by
  rw [input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
    target view read rule3FrameOf endpoint partner first second endpointCursor
    firstCursor secondCursor candidates firstSelected secondSelected] at computed
  generalize callbackResult : rule3FrameOf [firstCursor, secondCursor] = result at computed
  cases result with
  | none => simp [callbackResult] at computed
  | some rule3Frame =>
      simp only [option_some_bind_apply] at computed
      generalize keysResult : rule3Frame.keys = keys at computed
      cases keys with
      | nil => simp [keysResult] at computed
      | cons firstRule3 rest =>
          cases rest with
          | nil => simp [keysResult] at computed
          | cons secondRule3 rest =>
              cases rest with
              | cons thirdRule3 rest => simp [keysResult] at computed
              | nil =>
                  generalize firstBuilt :
                    input.buildLocalizedRerootCompoundRule45KeyWithRead?
                      read (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                      firstCursor = firstResult at computed
                  cases firstResult with
                  | none => simp [firstBuilt] at computed
                  | some firstRule45 =>
                      simp only [option_some_bind_apply] at computed
                      generalize secondBuilt :
                        input.buildLocalizedRerootCompoundRule45KeyWithRead?
                          read (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                          secondCursor = secondResult at computed
                      cases secondResult with
                      | none => simp [secondBuilt] at computed
                      | some secondRule45 =>
                          simp only [option_some_bind_apply] at computed
                          simp only [Option.some.injEq] at computed
                          subst frame
                          exact ⟨rfl, rfl⟩

/-- The parametric endpoint compiler succeeds whenever the callback returns a two-key frame on the
two actual selected reference cursors.  The two compound through-Rule-5 keys are obtained from
their universal availability theorem at the occurrence reroot budget, using the validity of the
two selected cursors; no key is assumed. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_exists_of_support
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
    (support : input.LocalizedRule3ExactPairFrameSupport
      rule3FrameOf firstCursor secondCursor)
    (firstValid : input.LocalizedRerootCursorValid firstCursor)
    (secondValid : input.LocalizedRerootCursorValid secondCursor) :
    ∃ frame, input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = some frame := by
  obtain ⟨supportFrame, callbackComputed, keysLength⟩ := support
  rw [input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
    target view read rule3FrameOf endpoint partner first second endpointCursor
    firstCursor secondCursor candidates firstSelected secondSelected]
  rw [callbackComputed, option_some_bind_apply]
  generalize keysResult : supportFrame.keys = keys
  cases keys with
  | nil => simp [keysResult] at keysLength
  | cons firstRule3 rest =>
      cases rest with
      | nil => simp [keysResult] at keysLength
      | cons secondRule3 rest =>
          cases rest with
          | cons thirdRule3 rest => simp [keysResult] at keysLength
          | nil =>
              obtain ⟨firstRule45, firstComputed⟩ :=
                input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                  read firstCursor firstValid
              obtain ⟨secondRule45, secondComputed⟩ :=
                input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                  read secondCursor secondValid
              simp only [show localizedOccurrenceRerootEvaluationFuel carrierFuel =
                2 * (carrierFuel + 1) from rfl,
                firstComputed, option_some_bind_apply, secondComputed,
                option_some_bind_apply]
              exact ⟨_, rfl⟩

/-- The parametric short-circuit selector succeeds whenever the callback returns a two-key frame
on the two actual selected reference cursors.  Every strict branch returns immediately; the fully
tied branch reduces to the endpoint compiler lemma above. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_exists_of_support
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
    (support : input.LocalizedRule3ExactPairFrameSupport
      rule3FrameOf firstCursor secondCursor) :
    ∃ result, input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = some result := by
  have firstValid : input.LocalizedRerootCursorValid firstCursor :=
    input.localizedRule3ReferenceCursorExec?_valid endpointCursor firstCursor first firstSelected
  have secondValid : input.LocalizedRerootCursorValid secondCursor :=
    input.localizedRule3ReferenceCursorExec?_valid endpointCursor secondCursor second secondSelected
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  rw [firstSelected, option_some_bind_apply, secondSelected, option_some_bind_apply]
  cases root : input.compareLocalizedRerootCursorConstitutionalRoot
    firstCursor secondCursor with
  | gt => exact ⟨_, rfl⟩
  | lt => exact ⟨_, rfl⟩
  | eq =>
      cases constitutional : input.compareLocalizedConstitutionalCursors?
        firstCursor secondCursor with
      | none =>
          obtain ⟨frame, frameComputed⟩ :=
            input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_exists_of_support
              target view read rule3FrameOf endpoint partner first second endpointCursor
              firstCursor secondCursor candidates firstSelected secondSelected support
              firstValid secondValid
          rw [frameComputed, option_some_bind_apply]
          exact ⟨_, rfl⟩
      | some ordering =>
          cases ordering with
          | gt => exact ⟨_, rfl⟩
          | lt => exact ⟨_, rfl⟩
          | eq =>
              obtain ⟨frame, frameComputed⟩ :=
                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_exists_of_support
                  target view read rule3FrameOf endpoint partner first second endpointCursor
                  firstCursor secondCursor candidates firstSelected secondSelected support
                  firstValid secondValid
              rw [frameComputed, option_some_bind_apply]
              exact ⟨_, rfl⟩

/-- Every senior reference of a successful parametric short-circuit selector is one of the two
actual candidates.  The strict branches select a candidate directly; the fully tied branch reads
the priority of the compiled endpoint frame, whose stored candidate pair is exactly the actual
one. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
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
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf endpoint partner endpointCursor = some result) :
    ∀ reference, result.priority = .senior reference →
      reference = first ∨ reference = second := by
  intro reference senior
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead? at computed
  rw [candidates] at computed
  dsimp only at computed
  cases firstSelected : input.localizedRule3ReferenceCursorExec?
    endpointCursor first with
  | none =>
      rw [firstSelected] at computed
      simp at computed
  | some firstCursor =>
      cases secondSelected : input.localizedRule3ReferenceCursorExec?
        endpointCursor second with
      | none =>
          rw [firstSelected, option_some_bind_apply, secondSelected] at computed
          simp at computed
      | some secondCursor =>
          rw [firstSelected, option_some_bind_apply, secondSelected,
            option_some_bind_apply] at computed
          cases root : input.compareLocalizedRerootCursorConstitutionalRoot
            firstCursor secondCursor with
          | gt =>
              rw [root] at computed
              simp only [Option.some.injEq] at computed
              subst result
              have equality : reference = first := by
                injection senior with senior
                exact senior.symm
              exact Or.inl equality
          | lt =>
              rw [root] at computed
              simp only [Option.some.injEq] at computed
              subst result
              have equality : reference = second := by
                injection senior with senior
                exact senior.symm
              exact Or.inr equality
          | eq =>
              cases constitutional : input.compareLocalizedConstitutionalCursors?
                firstCursor secondCursor with
              | some ordering =>
                  cases ordering with
                  | gt =>
                      rw [root, constitutional] at computed
                      simp only [Option.some.injEq] at computed
                      subst result
                      have equality : reference = first := by
                        injection senior with senior
                        exact senior.symm
                      exact Or.inl equality
                  | lt =>
                      rw [root, constitutional] at computed
                      simp only [Option.some.injEq] at computed
                      subst result
                      have equality : reference = second := by
                        injection senior with senior
                        exact senior.symm
                      exact Or.inr equality
                  | eq =>
                      cases built : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                          target view read rule3FrameOf endpoint partner endpointCursor with
                      | none =>
                          rw [root, constitutional, built] at computed
                          simp at computed
                      | some frame =>
                          rw [root, constitutional, built, option_some_bind_apply] at computed
                          simp only [Option.some.injEq] at computed
                          subst result
                          have candidatePair :=
                            input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_endpointFrame_candidates
                              target view read rule3FrameOf endpoint partner first second
                              endpointCursor firstCursor secondCursor candidates firstSelected
                              secondSelected frame built
                          unfold localizedRule3EndpointPriority at senior
                          split at senior
                          · injection senior with senior
                            exact Or.inl (senior.symm.trans candidatePair.1)
                          · injection senior with senior
                            exact Or.inr (senior.symm.trans candidatePair.2)
                          · simp at senior
              | none =>
                  cases built : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                      target view read rule3FrameOf endpoint partner endpointCursor with
                  | none =>
                      rw [root, constitutional, built] at computed
                      simp at computed
                  | some frame =>
                      rw [root, constitutional, built, option_some_bind_apply] at computed
                      simp only [Option.some.injEq] at computed
                      subst result
                      have candidatePair :=
                        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_endpointFrame_candidates
                          target view read rule3FrameOf endpoint partner first second
                          endpointCursor firstCursor secondCursor candidates firstSelected
                          secondSelected frame built
                      unfold localizedRule3EndpointPriority at senior
                      split at senior
                      · injection senior with senior
                        exact Or.inl (senior.symm.trans candidatePair.1)
                      · injection senior with senior
                        exact Or.inr (senior.symm.trans candidatePair.2)
                      · simp at senior

/-! ## The projected physical identity -/

/-- The spatial node observation retains the physical unordered endpoint pair, independently of the
E/Z geometry and of the two endpoint priorities. -/
@[simp] theorem localizedRule3ShortCircuitSpatialObservation_physicalUnitId
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) :
    (input.localizedRule3ShortCircuitSpatialObservation result).physicalUnitId =
      input.localizedRule3PhysicalUnitId result.topology.left result.topology.right :=
  rfl

/-- The projected physical identity of the ordinary parametric spatial wrapper.  This is the exact
`Option.map (physicalUnitId ∘ spatialObservation)` interface used to neutralize a parent refusal:
only the physical endpoint pair is retained, not the E/Z geometry, the priorities or any key. -/
noncomputable def localizedRule3ShortCircuitSpatialPhysicalUnit?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option input.LocalizedRule3PhysicalUnitId :=
  Option.map
    (fun result => (input.localizedRule3ShortCircuitSpatialObservation result).physicalUnitId)
    (input.localizedRule3ShortCircuitSpatialUnitWithRead?
      target occurrence view read rule3FrameOf)

/-- A successful topology, two successful endpoint selectors, the physical double bond and axis
readiness determine the projected physical identity of the ordinary wrapper.  The geometry unit
itself is derived by the priority skeleton. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_endpoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.left topology.right topology.leftCursor =
        some leftEndpoint)
    (rightComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.left topology.rightCursor =
        some rightEndpoint)
    (doubleBond : input.moleculeGraph.bond topology.left topology.right = 2)
    (ready : input.LocalizedRule3AxisGeometryReadiness topology.left topology.right
      leftEndpoint.priority rightEndpoint.priority) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf =
      some (input.localizedRule3PhysicalUnitId topology.left topology.right) := by
  unfold localizedRule3ShortCircuitSpatialPhysicalUnit?
    localizedRule3ShortCircuitSpatialUnitWithRead?
  rw [found, option_some_bind_apply, leftComputed, option_some_bind_apply,
    rightComputed, option_some_bind_apply]
  obtain ⟨unit, unitComputed⟩ :=
    input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_exists_of_readiness
      topology.left topology.right leftEndpoint.priority rightEndpoint.priority doubleBond ready
  rw [input.localizedRule3ShortCircuitSpatialUnit?_eq_some_of_priorities
    topology.left topology.right leftEndpoint rightEndpoint unit unitComputed,
    option_some_bind_apply]
  simp only [Option.map_some, localizedRule3ShortCircuitSpatialObservation_physicalUnitId,
    Option.some.injEq]

/-! ## Reader-independent projected identity -/

/-- One side of the reader comparison: if the callback supplies a two-key frame on the two actual
selected reference cursors of both endpoints, then the projected physical identity is the canonical
unordered identity of the physical endpoints.  The actual senior references are covered by the
candidate-pair readiness domain. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_support
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
    (leftSupport : input.LocalizedRule3ExactPairFrameSupport
      rule3FrameOf leftFirstCursor leftSecondCursor)
    (rightSupport : input.LocalizedRule3ExactPairFrameSupport
      rule3FrameOf rightFirstCursor rightSecondCursor)
    (doubleBond : input.moleculeGraph.bond topology.left topology.right = 2)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.left topology.right leftFirst leftSecond rightFirst rightSecond) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf =
      some (input.localizedRule3PhysicalUnitId topology.left topology.right) := by
  obtain ⟨leftEndpoint, leftComputed⟩ :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_exists_of_support
      target view read rule3FrameOf topology.left topology.right leftFirst leftSecond
      topology.leftCursor leftFirstCursor leftSecondCursor leftCandidates leftFirstSelected
      leftSecondSelected leftSupport
  obtain ⟨rightEndpoint, rightComputed⟩ :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_exists_of_support
      target view read rule3FrameOf topology.right topology.left rightFirst rightSecond
      topology.rightCursor rightFirstCursor rightSecondCursor rightCandidates rightFirstSelected
      rightSecondSelected rightSupport
  have leftMember : ∀ reference, leftEndpoint.priority = .senior reference →
      reference = leftFirst ∨ reference = leftSecond :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
      target view read rule3FrameOf topology.left topology.right leftFirst leftSecond
      topology.leftCursor leftCandidates leftEndpoint leftComputed
  have rightMember : ∀ reference, rightEndpoint.priority = .senior reference →
      reference = rightFirst ∨ reference = rightSecond :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
      target view read rule3FrameOf topology.right topology.left rightFirst rightSecond
      topology.rightCursor rightCandidates rightEndpoint rightComputed
  have ready : input.LocalizedRule3AxisGeometryReadiness
      topology.left topology.right leftEndpoint.priority rightEndpoint.priority :=
    input.localizedRule3AxisGeometryReadiness_of_candidates topology.left topology.right
      leftFirst leftSecond rightFirst rightSecond leftEndpoint.priority rightEndpoint.priority
      candidateReady leftMember rightMember
  exact input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_endpoints
    target occurrence view read rule3FrameOf topology found leftEndpoint rightEndpoint
    leftComputed rightComputed doubleBond ready

/-- **Request-local reader comparison of the projected physical identity.**  Two arbitrary label
readers and two arbitrary Rule-3 frame callbacks give exactly the same physical unit identity as
long as each callback returns a two-key frame on the two actual selected reference-cursor pairs
and the callbacks agree on `isSome` at those request lists.  The E/Z geometry and the two endpoint
priorities may differ between the readers; only the candidates, the actual cursor selections and
the physical endpoints are shared. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_callbackSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
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
    (leftSupportBefore : input.LocalizedRule3ExactPairFrameSupport
      before leftFirstCursor leftSecondCursor)
    (leftSupportAfter : input.LocalizedRule3ExactPairFrameSupport
      after leftFirstCursor leftSecondCursor)
    (rightSupportBefore : input.LocalizedRule3ExactPairFrameSupport
      before rightFirstCursor rightSecondCursor)
    (rightSupportAfter : input.LocalizedRule3ExactPairFrameSupport
      after rightFirstCursor rightSecondCursor)
    (leftCallbackIsSome :
      (before [leftFirstCursor, leftSecondCursor]).isSome =
        (after [leftFirstCursor, leftSecondCursor]).isSome)
    (rightCallbackIsSome :
      (before [rightFirstCursor, rightSecondCursor]).isSome =
        (after [rightFirstCursor, rightSecondCursor]).isSome)
    (doubleBond : input.moleculeGraph.bond topology.left topology.right = 2)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.left topology.right leftFirst leftSecond rightFirst rightSecond) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view readOne before =
      input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view readTwo after := by
  have beforeIdentity :=
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_support
      target occurrence view readOne before topology found leftFirst leftSecond rightFirst
      rightSecond leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor
      leftCandidates rightCandidates leftFirstSelected leftSecondSelected rightFirstSelected
      rightSecondSelected leftSupportBefore rightSupportBefore doubleBond candidateReady
  have afterIdentity :=
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_support
      target occurrence view readTwo after topology found leftFirst leftSecond rightFirst
      rightSecond leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor
      leftCandidates rightCandidates leftFirstSelected leftSecondSelected rightFirstSelected
      rightSecondSelected leftSupportAfter rightSupportAfter doubleBond candidateReady
  rw [beforeIdentity, afterIdentity]









/-- The odd-cumulene spatial node observation retains the physical unordered endpoint pair,
independently of the E/Z geometry and of the two endpoint priorities. -/
@[simp] theorem localizedRule3ShortCircuitOddSpatialObservation_physicalUnitId
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel) :
    (input.localizedRule3ShortCircuitOddSpatialObservation result).physicalUnitId =
      input.localizedRule3PhysicalUnitId
        result.topology.initial.left result.topology.right :=
  rfl

/-- The projected physical identity of the odd parametric spatial wrapper. -/
noncomputable def localizedRule3ShortCircuitOddSpatialPhysicalUnit?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option input.LocalizedRule3PhysicalUnitId :=
  Option.map
    (fun result => (input.localizedRule3ShortCircuitOddSpatialObservation result).physicalUnitId)
    (input.localizedRule3ShortCircuitOddSpatialUnitWithRead?
      target occurrence view read rule3FrameOf)

/-- A successful odd topology, two successful endpoint selectors and axis readiness determine the
projected physical identity of the odd wrapper.  No adjacent double-bond test is used; the
extended skeleton itself is derived from readiness. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_endpoints
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
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.initial.left topology.initial.right
        topology.initial.leftCursor = some leftEndpoint)
    (rightComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.rightPartner topology.rightCursor =
        some rightEndpoint)
    (ready : input.LocalizedRule3AxisGeometryReadiness
      topology.initial.left topology.right leftEndpoint.priority rightEndpoint.priority) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf =
      some (input.localizedRule3PhysicalUnitId topology.initial.left topology.right) := by
  unfold localizedRule3ShortCircuitOddSpatialPhysicalUnit?
    localizedRule3ShortCircuitOddSpatialUnitWithRead?
  rw [found, option_some_bind_apply, leftComputed, option_some_bind_apply,
    rightComputed, option_some_bind_apply]
  obtain ⟨unit, unitComputed⟩ :=
    input.localizedRule3ExtendedSpatialUnitOfPriorities?_exists_of_readiness
      topology.initial.left topology.right leftEndpoint.priority rightEndpoint.priority ready
  rw [unitComputed, option_some_bind_apply]
  simp only [Option.map_some, localizedRule3ShortCircuitOddSpatialObservation_physicalUnitId,
    Option.some.injEq]

/-- One side of the odd-cumulene reader comparison. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_support
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
    (leftSupport : input.LocalizedRule3ExactPairFrameSupport
      rule3FrameOf leftFirstCursor leftSecondCursor)
    (rightSupport : input.LocalizedRule3ExactPairFrameSupport
      rule3FrameOf rightFirstCursor rightSecondCursor)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf =
      some (input.localizedRule3PhysicalUnitId topology.initial.left topology.right) := by
  obtain ⟨leftEndpoint, leftComputed⟩ :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_exists_of_support
      target view read rule3FrameOf topology.initial.left topology.initial.right
      leftFirst leftSecond topology.initial.leftCursor leftFirstCursor leftSecondCursor
      leftCandidates leftFirstSelected leftSecondSelected leftSupport
  obtain ⟨rightEndpoint, rightComputed⟩ :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_exists_of_support
      target view read rule3FrameOf topology.right topology.rightPartner rightFirst rightSecond
      topology.rightCursor rightFirstCursor rightSecondCursor rightCandidates rightFirstSelected
      rightSecondSelected rightSupport
  have leftMember : ∀ reference, leftEndpoint.priority = .senior reference →
      reference = leftFirst ∨ reference = leftSecond :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
      target view read rule3FrameOf topology.initial.left topology.initial.right
      leftFirst leftSecond topology.initial.leftCursor leftCandidates leftEndpoint leftComputed
  have rightMember : ∀ reference, rightEndpoint.priority = .senior reference →
      reference = rightFirst ∨ reference = rightSecond :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
      target view read rule3FrameOf topology.right topology.rightPartner rightFirst rightSecond
      topology.rightCursor rightCandidates rightEndpoint rightComputed
  have ready : input.LocalizedRule3AxisGeometryReadiness
      topology.initial.left topology.right leftEndpoint.priority rightEndpoint.priority :=
    input.localizedRule3AxisGeometryReadiness_of_candidates
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
      leftEndpoint.priority rightEndpoint.priority candidateReady leftMember rightMember
  exact input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_endpoints
    target occurrence view read rule3FrameOf topology found leftEndpoint rightEndpoint
    leftComputed rightComputed ready

/-- **Request-local odd-cumulene reader comparison of the projected physical identity.**  The E/Z
geometry and the endpoint priorities may differ between the readers; the callback is required only
to return a two-key frame on the two actual selected reference pairs and to agree on `isSome` at
those request lists. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_callbackSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
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
    (leftSupportBefore : input.LocalizedRule3ExactPairFrameSupport
      before leftFirstCursor leftSecondCursor)
    (leftSupportAfter : input.LocalizedRule3ExactPairFrameSupport
      after leftFirstCursor leftSecondCursor)
    (rightSupportBefore : input.LocalizedRule3ExactPairFrameSupport
      before rightFirstCursor rightSecondCursor)
    (rightSupportAfter : input.LocalizedRule3ExactPairFrameSupport
      after rightFirstCursor rightSecondCursor)
    (leftCallbackIsSome :
      (before [leftFirstCursor, leftSecondCursor]).isSome =
        (after [leftFirstCursor, leftSecondCursor]).isSome)
    (rightCallbackIsSome :
      (before [rightFirstCursor, rightSecondCursor]).isSome =
        (after [rightFirstCursor, rightSecondCursor]).isSome)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view readOne before =
      input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view readTwo after := by
  have beforeIdentity :=
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_support
      target occurrence view readOne before topology found leftFirst leftSecond rightFirst
      rightSecond leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor
      leftCandidates rightCandidates leftFirstSelected leftSecondSelected rightFirstSelected
      rightSecondSelected leftSupportBefore rightSupportBefore candidateReady
  have afterIdentity :=
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_support
      target occurrence view readTwo after topology found leftFirst leftSecond rightFirst
      rightSecond leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor
      leftCandidates rightCandidates leftFirstSelected leftSecondSelected rightFirstSelected
      rightSecondSelected leftSupportAfter rightSupportAfter candidateReady
  rw [beforeIdentity, afterIdentity]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ReferenceGeometryReady
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ReferenceGeometryReady_exists_geometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3AxisGeometryReadiness
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3AxisCandidateGeometryReadiness
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3AxisGeometryReadiness_of_candidates
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_exists_of_readiness
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedSpatialUnitOfPriorities?_exists_of_readiness
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ReferenceCursorExec?_valid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_endpointFrame_candidates
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_exists_of_support
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_exists_of_support
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialObservation_physicalUnitId
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_endpoints
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_support
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_callbackSupport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialObservation_physicalUnitId
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_endpoints
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_support
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_callbackSupport
