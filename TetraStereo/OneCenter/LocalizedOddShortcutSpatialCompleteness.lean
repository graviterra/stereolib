import TetraStereo.OneCenter.LocalizedRule3CumulatedDescriptor
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddSpatial

set_option autoImplicit false

namespace TetraStereo.OneCenter




































namespace CertifiedLocalizedCIPInput

/-! ## Factorization and priority coherence of the descriptor-bearing terminal unit -/

/-- The descriptor-bearing extended terminal unit is exactly the priority-only skeleton applied to
the two complete endpoint priorities.  This is the odd-cumulene analogue of the ordinary
double-bond factorization and lets every later statement be written once, on priorities. -/
theorem localizedRule3ExtendedDescriptorBearingSpatialUnit?_factorization
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame) :
    input.localizedRule3ExtendedDescriptorBearingSpatialUnit? left right leftFrame rightFrame =
      input.localizedRule3ExtendedSpatialUnitOfPriorities? left right
        (input.localizedRule3EndpointPriority leftFrame)
        (input.localizedRule3EndpointPriority rightFrame) := by
  unfold localizedRule3ExtendedDescriptorBearingSpatialUnit?
    localizedRule3ExtendedSpatialUnitOfPriorities?
  rfl

/-- A successful priority-only unit records exactly the two priorities it was given. -/
theorem localizedRule3ExtendedSpatialUnitOfPriorities?_priorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3ExtendedSpatialUnitOfPriorities?
      left right leftPriority rightPriority = some unit) :
    unit.leftPriority = leftPriority ∧ unit.rightPriority = rightPriority := by
  have derived := input.localizedRule3ExtendedSpatialUnitOfPriorities?_sound
    left right leftPriority rightPriority unit computed
  exact ⟨derived.1, derived.2.1⟩

/-- A successful descriptor-bearing unit records exactly the two complete endpoint priorities it
was given.  This is the bridge that identifies the unit projected from a legacy eager compilation
with the unit computed by the priority-only shortcut. -/
theorem localizedRule3ExtendedDescriptorBearingSpatialUnit?_priorities
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
      left right leftFrame rightFrame = some unit) :
    unit.leftPriority = input.localizedRule3EndpointPriority leftFrame ∧
      unit.rightPriority = input.localizedRule3EndpointPriority rightFrame := by
  rw [input.localizedRule3ExtendedDescriptorBearingSpatialUnit?_factorization
    left right leftFrame rightFrame] at computed
  exact input.localizedRule3ExtendedSpatialUnitOfPriorities?_priorities
    left right (input.localizedRule3EndpointPriority leftFrame)
    (input.localizedRule3EndpointPriority rightFrame) unit computed

/-! ## Complete two-sided semantics of the priority-only terminal unit -/

/-- Executable success of the priority-only terminal unit is exactly its independent declarative
meaning: the two priorities are the requested ones and the exact rational terminal geometry relates
the actual semantic coordinates of the two terminal atoms and of the two senior references. -/
theorem localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult) :
    input.localizedRule3ExtendedSpatialUnitOfPriorities?
        left right leftPriority rightPriority = some unit ↔
      input.DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
        left right leftPriority rightPriority unit := by
  constructor
  · intro computed
    exact input.localizedRule3ExtendedSpatialUnitOfPriorities?_sound
      left right leftPriority rightPriority unit computed
  · rintro ⟨leftEq, rightEq, geometryMeaning⟩
    have unitEq : unit = ⟨leftPriority, rightPriority, unit.geometry⟩ := by
      cases unit with
      | mk unitLeft unitRight unitGeometry =>
          dsimp only at leftEq rightEq ⊢
          rw [leftEq, rightEq]
    rw [unitEq]
    cases leftPriority with
    | nonstereogenic =>
        cases rightPriority with
        | nonstereogenic =>
            rw [geometryMeaning]
            simp [localizedRule3ExtendedSpatialUnitOfPriorities?]
        | senior rightReference =>
            rw [geometryMeaning]
            simp [localizedRule3ExtendedSpatialUnitOfPriorities?]
    | senior leftReference =>
        cases rightPriority with
        | nonstereogenic =>
            rw [geometryMeaning]
            simp [localizedRule3ExtendedSpatialUnitOfPriorities?]
        | senior rightReference =>
            obtain ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
              leftSemantic, rightSemantic, leftReferenceSemantic,
              rightReferenceSemantic, spatial⟩ := geometryMeaning
            simp [localizedRule3ExtendedSpatialUnitOfPriorities?,
              (input.spatialPointAt?_eq_some_iff left leftPoint).mpr leftSemantic,
              (input.spatialPointAt?_eq_some_iff right rightPoint).mpr rightSemantic,
              (input.spatialPointAt?_eq_some_iff
                leftReference leftReferencePoint).mpr leftReferenceSemantic,
              (input.spatialPointAt?_eq_some_iff
                rightReference rightReferencePoint).mpr rightReferenceSemantic,
              (rule3GeometryOfSpatialReferences?_eq_some_iff
                leftPoint rightPoint leftReferencePoint rightReferencePoint
                unit.geometry).mpr spatial]

/-- Refusal of the priority-only terminal unit is exact: it happens precisely when no result
satisfies the independent declarative terminal meaning. -/
theorem localizedRule3ExtendedSpatialUnitOfPriorities?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority) :
    input.localizedRule3ExtendedSpatialUnitOfPriorities?
        left right leftPriority rightPriority = none ↔
      ¬ ∃ unit, input.DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
        left right leftPriority rightPriority unit := by
  constructor
  · intro computed ⟨unit, semantic⟩
    have successful :=
      (input.localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_iff
        left right leftPriority rightPriority unit).mpr semantic
    rw [computed] at successful
    contradiction
  · intro noSemantic
    cases computed : input.localizedRule3ExtendedSpatialUnitOfPriorities?
        left right leftPriority rightPriority with
    | none => rfl
    | some unit =>
        exfalso
        exact noSemantic ⟨unit,
          (input.localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_iff
            left right leftPriority rightPriority unit).mp computed⟩

/-! ## Explicit strict endpoint decision certificates -/

/-- An explicit strict decision certificate for one odd-cumulene terminal endpoint.  Every
constructor records only actual input facts: the exact explicit substituent pair, the two
executable reference-cursor selections, and the atomic-root or complete-constitutional comparison
outcome.  No constructor records the resulting observation, an executable success, a complete
endpoint key frame, the recursive Rule-3 frame callback, or any Rules-4a--5 key.  Consequently a
certificate is usable with the production callback and with `fun _ => none` alike.

The four constructors are exactly the strict branches of
`localizedRule3ShortCircuitEndpointPriorityExec?`: two decided by a strict first-sphere root
comparison and two decided by a strict complete constitutional comparison after a root tie.  The
deferred Rule-5 branch is deliberately absent because it would have to assume the eager endpoint
compilation, which is precisely what this layer must not assume. -/
inductive LocalizedRule3ConstitutionalEndpointCertificate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.LocalizedRule3ShortCircuitEndpointResult → Prop where
  | rootSeniorFirst (first second : input.Atom)
      (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
      (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
      (firstComputed : input.localizedRule3ReferenceCursorExec?
        endpointCursor first = some firstCursor)
      (secondComputed : input.localizedRule3ReferenceCursorExec?
        endpointCursor second = some secondCursor)
      (strict : input.compareLocalizedRerootCursorConstitutionalRoot
        firstCursor secondCursor = Ordering.gt) :
      input.LocalizedRule3ConstitutionalEndpointCertificate
        target view callback endpoint partner endpointCursor
        { priority := .senior first, firstCandidate := first }
  | rootSeniorSecond (first second : input.Atom)
      (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
      (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
      (firstComputed : input.localizedRule3ReferenceCursorExec?
        endpointCursor first = some firstCursor)
      (secondComputed : input.localizedRule3ReferenceCursorExec?
        endpointCursor second = some secondCursor)
      (strict : input.compareLocalizedRerootCursorConstitutionalRoot
        firstCursor secondCursor = Ordering.lt) :
      input.LocalizedRule3ConstitutionalEndpointCertificate
        target view callback endpoint partner endpointCursor
        { priority := .senior second, firstCandidate := first }
  | constitutionalSeniorFirst (first second : input.Atom)
      (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
      (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
      (firstComputed : input.localizedRule3ReferenceCursorExec?
        endpointCursor first = some firstCursor)
      (secondComputed : input.localizedRule3ReferenceCursorExec?
        endpointCursor second = some secondCursor)
      (tied : input.compareLocalizedRerootCursorConstitutionalRoot
        firstCursor secondCursor = Ordering.eq)
      (strict : input.compareLocalizedConstitutionalCursors?
        firstCursor secondCursor = some Ordering.gt) :
      input.LocalizedRule3ConstitutionalEndpointCertificate
        target view callback endpoint partner endpointCursor
        { priority := .senior first, firstCandidate := first }
  | constitutionalSeniorSecond (first second : input.Atom)
      (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
      (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
      (firstComputed : input.localizedRule3ReferenceCursorExec?
        endpointCursor first = some firstCursor)
      (secondComputed : input.localizedRule3ReferenceCursorExec?
        endpointCursor second = some secondCursor)
      (tied : input.compareLocalizedRerootCursorConstitutionalRoot
        firstCursor secondCursor = Ordering.eq)
      (strict : input.compareLocalizedConstitutionalCursors?
        firstCursor secondCursor = some Ordering.lt) :
      input.LocalizedRule3ConstitutionalEndpointCertificate
        target view callback endpoint partner endpointCursor
        { priority := .senior second, firstCandidate := first }

/-- Every strict certificate evaluates: the executable short-circuit endpoint selector returns
exactly the certified result, for every target, dependency view, and Rule-3 frame callback.  The
proof is the four strict non-eagerness theorems; the deferred compiler is never reached, so no
callback success and no eager frame are involved. -/
theorem LocalizedRule3ConstitutionalEndpointCertificate.evaluate
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    {result : input.LocalizedRule3ShortCircuitEndpointResult}
    (certificate : input.LocalizedRule3ConstitutionalEndpointCertificate
      target view callback endpoint partner endpointCursor result) :
    input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view callback endpoint partner endpointCursor = some result := by
  cases certificate with
  | rootSeniorFirst first second firstCursor secondCursor candidates
      firstComputed secondComputed strict =>
      exact input.localizedRule3ShortCircuitEndpointPriorityExec?_strict_gt
        target view callback endpoint partner first second endpointCursor candidates
        firstCursor secondCursor firstComputed secondComputed strict
  | rootSeniorSecond first second firstCursor secondCursor candidates
      firstComputed secondComputed strict =>
      exact input.localizedRule3ShortCircuitEndpointPriorityExec?_strict_lt
        target view callback endpoint partner first second endpointCursor candidates
        firstCursor secondCursor firstComputed secondComputed strict
  | constitutionalSeniorFirst first second firstCursor secondCursor candidates
      firstComputed secondComputed tied strict =>
      exact input.localizedRule3ShortCircuitEndpointPriorityExec?_constitutional_gt
        target view callback endpoint partner first second endpointCursor candidates
        firstCursor secondCursor firstComputed secondComputed tied strict
  | constitutionalSeniorSecond first second firstCursor secondCursor candidates
      firstComputed secondComputed tied strict =>
      exact input.localizedRule3ShortCircuitEndpointPriorityExec?_constitutional_lt
        target view callback endpoint partner first second endpointCursor candidates
        firstCursor secondCursor firstComputed secondComputed tied strict

/-- Every strict certificate certifies a senior endpoint priority.  In particular no strict
certificate can produce `.nonstereogenic`, so its terminal geometry is always decided by the exact
rational senior-reference relation. -/
theorem LocalizedRule3ConstitutionalEndpointCertificate.exists_priority_senior
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    {result : input.LocalizedRule3ShortCircuitEndpointResult}
    (certificate : input.LocalizedRule3ConstitutionalEndpointCertificate
      target view callback endpoint partner endpointCursor result) :
    ∃ reference, result.priority = .senior reference := by
  cases certificate with
  | rootSeniorFirst first second _ _ _ _ _ _ => exact ⟨first, rfl⟩
  | rootSeniorSecond first second _ _ _ _ _ _ => exact ⟨second, rfl⟩
  | constitutionalSeniorFirst first second _ _ _ _ _ _ _ => exact ⟨first, rfl⟩
  | constitutionalSeniorSecond first second _ _ _ _ _ _ _ => exact ⟨second, rfl⟩

/-! ## Assembling the odd short-circuit spatial result -/

/-- Construction theorem for the odd-cumulene spatial shortcut.  Given the executable odd terminal
topology, two explicit strict endpoint certificates (one per terminal endpoint), and the
independently stated declarative terminal geometry at the certified priorities, the executable odd
spatial shortcut returns exactly the packaged result.  The Rule-3 frame callback stays fully
unconstrained: the strict certificates evaluate without it. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_some_of_certificates
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftResult rightResult : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftCertificate : input.LocalizedRule3ConstitutionalEndpointCertificate
      target view callback topology.initial.left topology.initial.right
      topology.initial.leftCursor leftResult)
    (rightCertificate : input.LocalizedRule3ConstitutionalEndpointCertificate
      target view callback topology.right topology.rightPartner
      topology.rightCursor rightResult)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (geometry : input.DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
      topology.initial.left topology.right
      leftResult.priority rightResult.priority unit) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view callback =
      some ⟨topology, leftResult, rightResult, unit⟩ := by
  have leftComputed := leftCertificate.evaluate
  have rightComputed := rightCertificate.evaluate
  have unitComputed :=
    (input.localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_iff
      topology.initial.left topology.right
      leftResult.priority rightResult.priority unit).mpr geometry
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec?
  simp [topologyComputed, leftComputed, rightComputed, unitComputed]

/-- Existential corollary of the construction theorem: the odd spatial shortcut succeeds and its
topology, both decided endpoints, and the exact rational unit are exactly the supplied ones. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithExec?_exists_of_certificates
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftResult rightResult : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftCertificate : input.LocalizedRule3ConstitutionalEndpointCertificate
      target view callback topology.initial.left topology.initial.right
      topology.initial.leftCursor leftResult)
    (rightCertificate : input.LocalizedRule3ConstitutionalEndpointCertificate
      target view callback topology.right topology.rightPartner
      topology.rightCursor rightResult)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (geometry : input.DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
      topology.initial.left topology.right
      leftResult.priority rightResult.priority unit) :
    ∃ spatial : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel,
      input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
          target occurrence view callback = some spatial ∧
        spatial.topology = topology ∧
        spatial.leftEndpoint = leftResult ∧
        spatial.rightEndpoint = rightResult ∧
        spatial.unit = unit := by
  exact ⟨⟨topology, leftResult, rightResult, unit⟩,
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_some_of_certificates
      target occurrence view callback topology topologyComputed leftResult rightResult
      leftCertificate rightCertificate unit geometry,
    rfl, rfl, rfl, rfl⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
