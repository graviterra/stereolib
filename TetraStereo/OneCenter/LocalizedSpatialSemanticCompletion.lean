import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddSpatial
import TetraStereo.OneCenter.LocalizedOddShortcutSpatialCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput












































































/-! ## Exact two-sided semantics of the ordinary priority skeleton -/

/-- Executable success of the ordinary physical-double-bond priority skeleton is *exactly* its
independent declarative meaning.  In particular the exact rational geometry is determined by the
vanishing coplanarity determinant and the sign of the side-product determinant, and the two
completed endpoint priorities are those requested. -/
theorem localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult) :
    input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
        left right leftPriority rightPriority = some unit ↔
      input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnitOfPriorities
        left right leftPriority rightPriority unit := by
  constructor
  · intro computed
    exact input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_sound
      left right leftPriority rightPriority unit computed
  · rintro ⟨leftEq, rightEq, doubleBond, geometryMeaning⟩
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
            simp [localizedRule3DescriptorBearingSpatialUnitOfPriorities?, doubleBond]
        | senior rightReference =>
            rw [geometryMeaning]
            simp [localizedRule3DescriptorBearingSpatialUnitOfPriorities?, doubleBond]
    | senior leftReference =>
        cases rightPriority with
        | nonstereogenic =>
            rw [geometryMeaning]
            simp [localizedRule3DescriptorBearingSpatialUnitOfPriorities?, doubleBond]
        | senior rightReference =>
            obtain ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
              leftSemantic, rightSemantic, leftReferenceSemantic,
              rightReferenceSemantic, spatial⟩ := geometryMeaning
            simp [localizedRule3DescriptorBearingSpatialUnitOfPriorities?, doubleBond,
              (input.spatialPointAt?_eq_some_iff left leftPoint).mpr leftSemantic,
              (input.spatialPointAt?_eq_some_iff right rightPoint).mpr rightSemantic,
              (input.spatialPointAt?_eq_some_iff
                leftReference leftReferencePoint).mpr leftReferenceSemantic,
              (input.spatialPointAt?_eq_some_iff
                rightReference rightReferencePoint).mpr rightReferenceSemantic,
              (rule3GeometryOfSpatialReferences?_eq_some_iff
                leftPoint rightPoint leftReferencePoint rightReferencePoint
                unit.geometry).mpr spatial]

/-- The named reverse direction of
`localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_some_iff`: an independently described
physical double bond with two complete endpoint priorities and exact rational senior-reference
geometry is reproduced by the executable skeleton with the very same result record. -/
theorem localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (declarative : input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnitOfPriorities
      left right leftPriority rightPriority unit) :
    input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
      left right leftPriority rightPriority = some unit :=
  (input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_some_iff
    left right leftPriority rightPriority unit).mpr declarative

/-- Exact refusal of the ordinary priority skeleton: it answers `none` precisely when no result
satisfies the independent declarative relation. -/
theorem localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority) :
    input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
        left right leftPriority rightPriority = none ↔
      ¬ ∃ unit, input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnitOfPriorities
        left right leftPriority rightPriority unit := by
  constructor
  · intro computed ⟨unit, semantic⟩
    have successful :=
      (input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_some_iff
        left right leftPriority rightPriority unit).mpr semantic
    rw [computed] at successful
    contradiction
  · intro noSemantic
    cases computed : input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
        left right leftPriority rightPriority with
    | none => rfl
    | some unit =>
        exact absurd ⟨unit,
          (input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_some_iff
            left right leftPriority rightPriority unit).mp computed⟩ noSemantic

/-! ## Exact reverse of the odd-cumulene terminal skeleton -/

/-- The odd-cumulene terminal skeleton has the same exact two-sided semantics.  The odd spatial
module proves only soundness; the reverse direction is the existing complete characterization
`localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_iff` of
`LocalizedOddShortcutSpatialCompleteness`, re-exported here so that both skeletons expose the
converse at the same interface.  The terminal skeleton deliberately imposes no adjacent-endpoint
bond test, matching `DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities`. -/
theorem localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (declarative : input.DeclarativeLocalizedRule3ExtendedSpatialUnitOfPriorities
      left right leftPriority rightPriority unit) :
    input.localizedRule3ExtendedSpatialUnitOfPriorities?
      left right leftPriority rightPriority = some unit :=
  (input.localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_iff
    left right leftPriority rightPriority unit).mpr declarative

/-! ## Minimal short-circuit unit from the two endpoint results -/

/-- The minimal short-circuit unit computation is exactly the priority skeleton applied to the two
endpoint results.  Given endpoint coherence (`unit.left`/`unit.right` are the two supplied endpoint
results) and the declarative priority/geometry meaning of the projected core, the executable
returns the very same unit record, so both endpoint `firstCandidate` witnesses and both selected
senior reference atoms are preserved. -/
theorem localizedRule3ShortCircuitSpatialUnit?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (unit : input.LocalizedRule3ShortCircuitSpatialUnitResult)
    (leftCoherent : unit.left = leftEndpoint)
    (rightCoherent : unit.right = rightEndpoint)
    (coreDeclarative : input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnitOfPriorities
      left right leftEndpoint.priority rightEndpoint.priority
      (shortCircuitUnitToDescriptorBearing input unit)) :
    input.localizedRule3ShortCircuitSpatialUnit? left right leftEndpoint rightEndpoint =
      some unit := by
  have coreComputed :=
    (input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_some_iff
      left right leftEndpoint.priority rightEndpoint.priority
      (shortCircuitUnitToDescriptorBearing input unit)).mpr coreDeclarative
  unfold localizedRule3ShortCircuitSpatialUnit?
  rw [coreComputed]
  cases unit with
  | mk unitLeft unitRight unitCore =>
      dsimp only [shortCircuitUnitToDescriptorBearing] at leftCoherent rightCoherent ⊢
      rw [← leftCoherent, ← rightCoherent]
      rfl

/-- Packaged form of the minimal-unit converse: the full independently stated short-circuit spatial
unit (both recovered endpoint results and the priority-keyed rational geometry) is reproduced by the
executable minimal unit computation, with the exact same result record. -/
theorem localizedRule3ShortCircuitSpatialUnit?_eq_some_of_declarativeUnit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (left right : input.Atom)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (unit : input.LocalizedRule3ShortCircuitSpatialUnitResult)
    (declarative : input.DeclarativeLocalizedRule3ShortCircuitSpatialUnit target view
      Rule3FrameMeaning left right leftCursor rightCursor leftEndpoint rightEndpoint unit) :
    input.localizedRule3ShortCircuitSpatialUnit? left right leftEndpoint rightEndpoint =
      some unit := by
  obtain ⟨leftCoherent, rightCoherent, -, -, coreDeclarative⟩ := declarative
  exact input.localizedRule3ShortCircuitSpatialUnit?_eq_some_of_declarative
    left right leftEndpoint rightEndpoint unit leftCoherent rightCoherent coreDeclarative







/-- **Intermediate composition** (ordinary double bond).  A declarative short-circuit spatial
result is reproduced by the executable occurrence wrapper — the same topology, the same two
endpoint results (including their senior reference atoms and `firstCandidate` witnesses), and the
same priority-keyed rational geometry — provided the physical topology and the two endpoint
decisions are recognized.

Residual work, owned elsewhere: `topologyRecognized` is the ordinary
`localizedRule3PhysicalEndpointCursorFrame?` completeness statement of
`LocalizedRule3RouteCompleteness`; `leftEndpointRecognized`/`rightEndpointRecognized` are the
independent endpoint converses of `LocalizedEndpointSemanticCompletion`, whose own explicit
component obligations are frame-callback observable completeness, constitutional coherence,
canonical reference selection, and exact Rule-4/5 builder agreement.  When those land they can be
passed directly here.  These are the only remaining component premises; the geometry and minimal
unit are discharged unconditionally. -/
theorem localizedRule3ShortCircuitSpatialUnitWithExec?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (declarative : input.DeclarativeLocalizedRule3ShortCircuitSpatialResult
      target occurrence view Rule3FrameMeaning result)
    (topologyRecognized :
      input.localizedRule3PhysicalEndpointCursorFrame? occurrence = some result.topology)
    (leftEndpointRecognized :
      input.localizedRule3ShortCircuitEndpointPriority? target view rule3FrameOf
          result.topology.left result.topology.right result.topology.leftCursor =
        some result.leftEndpoint)
    (rightEndpointRecognized :
      input.localizedRule3ShortCircuitEndpointPriority? target view rule3FrameOf
          result.topology.right result.topology.left result.topology.rightCursor =
        some result.rightEndpoint) :
    input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence view rule3FrameOf = some result := by
  obtain ⟨-, unitDeclarative⟩ := declarative
  have unitComputed := input.localizedRule3ShortCircuitSpatialUnit?_eq_some_of_declarativeUnit
    target view Rule3FrameMeaning result.topology.left result.topology.right
    result.topology.leftCursor result.topology.rightCursor result.leftEndpoint
    result.rightEndpoint result.unit unitDeclarative
  unfold localizedRule3ShortCircuitSpatialUnitWithExec?
  simp [localizedRule3PhysicalEndpointCursorFrameExec?_eq_original,
    ← localizedRule3ShortCircuitEndpointPriority?_eq_localizedRule3ShortCircuitEndpointPriorityExec?,
    topologyRecognized, leftEndpointRecognized, rightEndpointRecognized, unitComputed]

/-- The non-executable occurrence wrapper computes the same result as its executable twin, so the
ordinary composition holds for `localizedRule3ShortCircuitSpatialUnitWith?` as well. -/
theorem localizedRule3ShortCircuitSpatialUnitWith?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (declarative : input.DeclarativeLocalizedRule3ShortCircuitSpatialResult
      target occurrence view Rule3FrameMeaning result)
    (topologyRecognized :
      input.localizedRule3PhysicalEndpointCursorFrame? occurrence = some result.topology)
    (leftEndpointRecognized :
      input.localizedRule3ShortCircuitEndpointPriority? target view rule3FrameOf
          result.topology.left result.topology.right result.topology.leftCursor =
        some result.leftEndpoint)
    (rightEndpointRecognized :
      input.localizedRule3ShortCircuitEndpointPriority? target view rule3FrameOf
          result.topology.right result.topology.left result.topology.rightCursor =
        some result.rightEndpoint) :
    input.localizedRule3ShortCircuitSpatialUnitWith?
        target occurrence view rule3FrameOf = some result := by
  rw [← localizedRule3ShortCircuitSpatialUnitWithExec?_eq_localizedRule3ShortCircuitSpatialUnitWith?
    input target occurrence view rule3FrameOf]
  exact input.localizedRule3ShortCircuitSpatialUnitWithExec?_eq_some_of_declarative
    target occurrence view rule3FrameOf Rule3FrameMeaning result declarative
    topologyRecognized leftEndpointRecognized rightEndpointRecognized

/-! ## Occurrence-level odd-cumulene converse (intermediate composition) -/

/-- **Intermediate composition** (odd cumulene).  A declarative odd short-circuit spatial result is
reproduced by the executable odd occurrence wrapper, with the exact same topology, endpoint
results, and terminal geometry.

Residual work, owned elsewhere: `topologyRecognized` is the odd-cumulene
`localizedRule3OddCumuleneEndpointCursorFrame?` completeness statement of
`LocalizedRule3RouteCompleteness`; `leftEndpointRecognized`/`rightEndpointRecognized` are the
independent endpoint converses of `LocalizedEndpointSemanticCompletion`, whose own explicit
component obligations are frame-callback observable completeness, constitutional coherence,
canonical reference selection, and exact Rule-4/5 builder agreement.  The terminal geometry
converse itself is unconditional
(`localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_of_declarative`). -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Meaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel)
    (declarative : input.DeclarativeLocalizedRule3ShortCircuitOddSpatialResult
      target occurrence view Meaning result)
    (topologyRecognized :
      input.localizedRule3OddCumuleneEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence =
        some result.topology)
    (leftEndpointRecognized :
      input.localizedRule3ShortCircuitEndpointPriority? target view callback
          result.topology.initial.left result.topology.initial.right
          result.topology.initial.leftCursor =
        some result.leftEndpoint)
    (rightEndpointRecognized :
      input.localizedRule3ShortCircuitEndpointPriority? target view callback
          result.topology.right result.topology.rightPartner result.topology.rightCursor =
        some result.rightEndpoint) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view callback = some result := by
  obtain ⟨-, -, -, geometryDeclarative⟩ := declarative
  have unitComputed := input.localizedRule3ExtendedSpatialUnitOfPriorities?_eq_some_of_declarative
    result.topology.initial.left result.topology.right
    result.leftEndpoint.priority result.rightEndpoint.priority result.unit geometryDeclarative
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec?
  simp [localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original,
    ← localizedRule3ShortCircuitEndpointPriority?_eq_localizedRule3ShortCircuitEndpointPriorityExec?,
    topologyRecognized, leftEndpointRecognized, rightEndpointRecognized, unitComputed]

/-! ## Exact retention of the reference atoms used by the observations

The spatial observations project a senior reference atom out of a senior priority and fall back to
the inert `firstCandidate` witness only for a proved nonstereogenic (complete-key tie) priority.
The lemmas below record that projection exactly, so the compositions above preserve both. -/

@[simp] theorem localizedRule3ShortCircuitSpatialObservation_leftReference_match
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) :
    (input.localizedRule3ShortCircuitSpatialObservation result).unit.leftReference =
      match result.leftEndpoint.priority with
      | .senior reference => reference
      | .nonstereogenic => result.leftEndpoint.firstCandidate := rfl

@[simp] theorem localizedRule3ShortCircuitSpatialObservation_rightReference_match
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) :
    (input.localizedRule3ShortCircuitSpatialObservation result).unit.rightReference =
      match result.rightEndpoint.priority with
      | .senior reference => reference
      | .nonstereogenic => result.rightEndpoint.firstCandidate := rfl

/-- A senior left endpoint contributes its exact senior reference atom to the observation. -/
theorem localizedRule3ShortCircuitSpatialObservation_leftReference_senior
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (reference : input.Atom)
    (senior : result.leftEndpoint.priority = .senior reference) :
    (input.localizedRule3ShortCircuitSpatialObservation result).unit.leftReference =
      reference := by
  rw [localizedRule3ShortCircuitSpatialObservation_leftReference_match, senior]

/-- A senior right endpoint contributes its exact senior reference atom to the observation. -/
theorem localizedRule3ShortCircuitSpatialObservation_rightReference_senior
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (reference : input.Atom)
    (senior : result.rightEndpoint.priority = .senior reference) :
    (input.localizedRule3ShortCircuitSpatialObservation result).unit.rightReference =
      reference := by
  rw [localizedRule3ShortCircuitSpatialObservation_rightReference_match, senior]

/-- A proved nonstereogenic left priority keeps exactly the inert first candidate. -/
theorem localizedRule3ShortCircuitSpatialObservation_leftReference_nonstereogenic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (tied : result.leftEndpoint.priority = .nonstereogenic) :
    (input.localizedRule3ShortCircuitSpatialObservation result).unit.leftReference =
      result.leftEndpoint.firstCandidate := by
  rw [localizedRule3ShortCircuitSpatialObservation_leftReference_match, tied]

/-- A proved nonstereogenic right priority keeps exactly the inert first candidate. -/
theorem localizedRule3ShortCircuitSpatialObservation_rightReference_nonstereogenic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (tied : result.rightEndpoint.priority = .nonstereogenic) :
    (input.localizedRule3ShortCircuitSpatialObservation result).unit.rightReference =
      result.rightEndpoint.firstCandidate := by
  rw [localizedRule3ShortCircuitSpatialObservation_rightReference_match, tied]

/-- Exact odd-cumulene projection of the left observation reference atom: a senior terminal
priority contributes its selected senior reference, a proved nonstereogenic priority contributes
the inert first candidate. -/
@[simp] theorem localizedRule3ShortCircuitOddSpatialObservation_leftReference_match
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel) :
    (input.localizedRule3ShortCircuitOddSpatialObservation result).unit.leftReference =
      match result.unit.leftPriority with
      | .senior reference => reference
      | .nonstereogenic => result.leftEndpoint.firstCandidate := rfl

/-- Exact odd-cumulene projection of the right observation reference atom: a senior terminal
priority contributes its selected senior reference, a proved nonstereogenic priority contributes
the inert first candidate. -/
@[simp] theorem localizedRule3ShortCircuitOddSpatialObservation_rightReference_match
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel) :
    (input.localizedRule3ShortCircuitOddSpatialObservation result).unit.rightReference =
      match result.unit.rightPriority with
      | .senior reference => reference
      | .nonstereogenic => result.rightEndpoint.firstCandidate := rfl

/-- A senior left terminal priority contributes its exact senior reference atom to the odd
observation. -/
theorem localizedRule3ShortCircuitOddSpatialObservation_leftReference_senior
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel)
    (reference : input.Atom)
    (senior : result.unit.leftPriority = .senior reference) :
    (input.localizedRule3ShortCircuitOddSpatialObservation result).unit.leftReference =
      reference := by
  rw [localizedRule3ShortCircuitOddSpatialObservation_leftReference_match, senior]

/-- A senior right terminal priority contributes its exact senior reference atom to the odd
observation. -/
theorem localizedRule3ShortCircuitOddSpatialObservation_rightReference_senior
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel)
    (reference : input.Atom)
    (senior : result.unit.rightPriority = .senior reference) :
    (input.localizedRule3ShortCircuitOddSpatialObservation result).unit.rightReference =
      reference := by
  rw [localizedRule3ShortCircuitOddSpatialObservation_rightReference_match, senior]

/-- A proved nonstereogenic left terminal priority keeps exactly the inert first candidate. -/
theorem localizedRule3ShortCircuitOddSpatialObservation_leftReference_nonstereogenic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel)
    (tied : result.unit.leftPriority = .nonstereogenic) :
    (input.localizedRule3ShortCircuitOddSpatialObservation result).unit.leftReference =
      result.leftEndpoint.firstCandidate := by
  rw [localizedRule3ShortCircuitOddSpatialObservation_leftReference_match, tied]

/-- A proved nonstereogenic right terminal priority keeps exactly the inert first candidate. -/
theorem localizedRule3ShortCircuitOddSpatialObservation_rightReference_nonstereogenic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel)
    (tied : result.unit.rightPriority = .nonstereogenic) :
    (input.localizedRule3ShortCircuitOddSpatialObservation result).unit.rightReference =
      result.rightEndpoint.firstCandidate := by
  rw [localizedRule3ShortCircuitOddSpatialObservation_rightReference_match, tied]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
