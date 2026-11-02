import TetraStereo.OneCenter.LocalizedOpenCumuleneChemicalCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Atomic spatial construction for perceived even cumulenes

The existing per-cumulene readiness package
`LocalizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount` concludes, for every canonical endpoint
topology and every pair of successful endpoint compilations, the existence of an assignment
satisfying `DeclarativeLocalizedAxialAssignmentOfEndpointFrames`.  That conclusion is the object
the pipeline is meant to construct, so it is not independent evidence.

This module replaces it with strictly atomic, independently checkable data:

* for each of the two endpoint key frames, the complete Rules-1a--5 high reference selected by a
  **non-tie** comparison of its two keys (`localizedAxialHighOfEndpointFrame?`);
* `SemanticSpatialPointAt` coordinates for the two axis atoms and the two selected high
  references;
* a nonzero exact rational `CartesianPoint3.axialChiralityMeasure` of those four points.

`LocalizedAxialAtomicSpatialEvidence` bundles exactly these four ingredients.  The pure layer is
proved to be *exactly* equivalent to executable success
(`localizedAxialAssignmentOfEndpointFrames?_isSome_iff_atomic`), the executable assignment and its
independent meaning are constructed from the atomic data, and the atom-count quantification is
lifted back to the old readiness predicate without weakening
(`localizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount_iff_atomic`).

Every topology, endpoint-compilation and traversal-fuel obligation remains an explicit hypothesis.
No claim is made that arbitrary graphs carry coordinates: `SpatialIndicesWellFormed` admits
`spatial? = none`, and in that case the executable correctly refuses.  The point-totality lemmas
here apply only when a spatial configuration is actually supplied and indexed.
-/

/-! ## Atomic endpoint selection -/

/-- The senior reference at one endpoint: the atom whose complete Rules-1a--5 key is greater.
`none` exactly at a tied endpoint comparison. -/
def localizedAxialHighOfEndpointFrame?
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) : Option input.Atom :=
  match input.compareLocalizedOccurrenceRule3Through5Keys frame.firstKey frame.secondKey with
  | .gt => some frame.first
  | .lt => some frame.second
  | .eq => none

/-- Senior selection is the first projection of the already proved strict endpoint pair. -/
theorem localizedAxialHighOfEndpointFrame?_eq_pair_fst
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    input.localizedAxialHighOfEndpointFrame? frame =
      (input.localizedAxialEndpointPair? frame).map Prod.fst := by
  unfold localizedAxialHighOfEndpointFrame? localizedAxialEndpointPair?
  cases compared : input.compareLocalizedOccurrenceRule3Through5Keys
    frame.firstKey frame.secondKey <;> rfl

/-- Senior selection commutes with pair selection: a selected high reference always comes with a
selected low reference, and conversely. -/
theorem localizedAxialHighOfEndpointFrame?_eq_some_iff_exists_pair
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (high : input.Atom) :
    input.localizedAxialHighOfEndpointFrame? frame = some high ↔
      ∃ low, input.localizedAxialEndpointPair? frame = some (high, low) := by
  rw [input.localizedAxialHighOfEndpointFrame?_eq_pair_fst]
  constructor
  · intro mapped
    obtain ⟨pair, pairComputed, firstEq⟩ := Option.map_eq_some_iff.mp mapped
    rcases pair with ⟨pairHigh, pairLow⟩
    subst firstEq
    exact ⟨pairLow, pairComputed⟩
  · rintro ⟨low, pairComputed⟩
    rw [pairComputed]
    rfl

/-- Senior selection succeeds exactly when the complete endpoint keys are not tied. -/
theorem localizedAxialHighOfEndpointFrame?_isSome_iff
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    (input.localizedAxialHighOfEndpointFrame? frame).isSome = true ↔
      input.compareLocalizedOccurrenceRule3Through5Keys
        frame.firstKey frame.secondKey ≠ Ordering.eq := by
  unfold localizedAxialHighOfEndpointFrame?
  cases compared : input.compareLocalizedOccurrenceRule3Through5Keys
    frame.firstKey frame.secondKey <;> simp

/-! ## Exact rational nonzero descriptor criterion -/

/-- A nonzero exact axial measure always produces a descriptor. -/
theorem axialDescriptorOfSpatialReferences?_isSome_of_ne_zero
    (axisStart axisEnd startHigh endHigh : CartesianPoint3)
    (nonzero : CartesianPoint3.axialChiralityMeasure
      axisStart axisEnd startHigh endHigh ≠ 0) :
    (axialDescriptorOfSpatialReferences?
      axisStart axisEnd startHigh endHigh).isSome = true := by
  rcases lt_trichotomy (CartesianPoint3.axialChiralityMeasure
    axisStart axisEnd startHigh endHigh) 0 with negative | zero | positive
  · simp [axialDescriptorOfSpatialReferences?, negative]
  · exact absurd zero nonzero
  · have notNegative : ¬ CartesianPoint3.axialChiralityMeasure
        axisStart axisEnd startHigh endHigh < 0 := not_lt_of_ge positive.le
    simp [axialDescriptorOfSpatialReferences?, notNegative, positive]

/-- The executable descriptor succeeds exactly when the exact rational measure is nonzero. -/
theorem axialDescriptorOfSpatialReferences?_isSome_iff_ne_zero
    (axisStart axisEnd startHigh endHigh : CartesianPoint3) :
    (axialDescriptorOfSpatialReferences?
        axisStart axisEnd startHigh endHigh).isSome = true ↔
      CartesianPoint3.axialChiralityMeasure
        axisStart axisEnd startHigh endHigh ≠ 0 := by
  constructor
  · intro successful zero
    simp [axialDescriptorOfSpatialReferences?, zero] at successful
  · exact axialDescriptorOfSpatialReferences?_isSome_of_ne_zero
      axisStart axisEnd startHigh endHigh

/-- A zero exact measure is the executable refusal condition. -/
theorem axialDescriptorOfSpatialReferences?_eq_none_of_measure_zero
    (axisStart axisEnd startHigh endHigh : CartesianPoint3)
    (zero : CartesianPoint3.axialChiralityMeasure
      axisStart axisEnd startHigh endHigh = 0) :
    axialDescriptorOfSpatialReferences? axisStart axisEnd startHigh endHigh = none := by
  simp [axialDescriptorOfSpatialReferences?, zero]

/-! ## Point totality from a supplied spatial configuration -/

/-- With a present spatial configuration indexed by the atom count, every semantic atom reads the
corresponding exact rational position. -/
theorem spatialPointAt?_eq_some_get_of_spatial
    (input : CertifiedLocalizedCIPInput)
    (spatial : SpatialConfiguration)
    (observed : input.certified.input.spatial? = some spatial)
    (wellFormed :
      spatial.positions.length = input.certified.input.molecule.atomCount)
    (atom : input.Atom) :
    input.spatialPointAt? atom =
      some (spatial.positions[atom.val]'(by simp [wellFormed])) := by
  have hlt : atom.val < spatial.positions.length := by
    simp [wellFormed]
  simp [spatialPointAt?, observed, List.getElem?_eq_getElem hlt]

/-- Point totality: every atom of a spaced, count-indexed input has an exact coordinate. -/
theorem exists_spatialPointAt_of_spatial
    (input : CertifiedLocalizedCIPInput)
    (spatial : SpatialConfiguration)
    (observed : input.certified.input.spatial? = some spatial)
    (wellFormed :
      spatial.positions.length = input.certified.input.molecule.atomCount)
    (atom : input.Atom) :
    ∃ point, input.spatialPointAt? atom = some point := by
  exact ⟨_, input.spatialPointAt?_eq_some_get_of_spatial
    spatial observed wellFormed atom⟩

/-- Point totality in semantic form. -/
theorem exists_semanticSpatialPointAt_of_spatial
    (input : CertifiedLocalizedCIPInput)
    (spatial : SpatialConfiguration)
    (observed : input.certified.input.spatial? = some spatial)
    (wellFormed :
      spatial.positions.length = input.certified.input.molecule.atomCount)
    (atom : input.Atom) :
    ∃ point, input.SemanticSpatialPointAt atom point := by
  obtain ⟨point, computed⟩ :=
    input.exists_spatialPointAt_of_spatial spatial observed wellFormed atom
  exact ⟨point, (input.spatialPointAt?_eq_some_iff atom point).mp computed⟩

/-- Point totality in executable-success form. -/
theorem spatialPointAt?_isSome_of_spatial
    (input : CertifiedLocalizedCIPInput)
    (spatial : SpatialConfiguration)
    (observed : input.certified.input.spatial? = some spatial)
    (wellFormed :
      spatial.positions.length = input.certified.input.molecule.atomCount)
    (atom : input.Atom) :
    (input.spatialPointAt? atom).isSome = true := by
  obtain ⟨point, computed⟩ :=
    input.exists_spatialPointAt_of_spatial spatial observed wellFormed atom
  rw [computed]
  rfl

/-- The semantic coordinate of a fixed atom is unique, so the atomic measure is well defined
independently of which witness is chosen. -/
theorem SemanticSpatialPointAt.unique
    (input : CertifiedLocalizedCIPInput)
    (atom : input.Atom)
    {first second : CartesianPoint3}
    (firstSemantic : input.SemanticSpatialPointAt atom first)
    (secondSemantic : input.SemanticSpatialPointAt atom second) :
    first = second := by
  obtain ⟨spatial, observed, firstLookup⟩ := firstSemantic
  obtain ⟨other, otherObserved, secondLookup⟩ := secondSemantic
  have spatialEq : spatial = other := Option.some.inj (observed.symm.trans otherObserved)
  subst spatialEq
  rw [firstLookup] at secondLookup
  exact Option.some.inj secondLookup

/-! ## The atomic spatial evidence predicate -/

/-- Atomic, independently checkable axial spatial evidence for one pair of endpoint key frames:
the senior reference selected by each non-tie complete-key comparison, semantic coordinates for
the two axis atoms and the two selected references, and a nonzero exact rational torsion measure.
Nothing here mentions an assignment, an endpoint pair, or a descriptor. -/
def LocalizedAxialAtomicSpatialEvidence
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame) : Prop :=
  ∃ startHigh endHigh axisStartPoint axisEndPoint startHighPoint endHighPoint,
    input.localizedAxialHighOfEndpointFrame? startFrame = some startHigh ∧
    input.localizedAxialHighOfEndpointFrame? endFrame = some endHigh ∧
    input.SemanticSpatialPointAt axisStart axisStartPoint ∧
    input.SemanticSpatialPointAt axisEnd axisEndPoint ∧
    input.SemanticSpatialPointAt startHigh startHighPoint ∧
    input.SemanticSpatialPointAt endHigh endHighPoint ∧
    CartesianPoint3.axialChiralityMeasure axisStartPoint axisEndPoint
      startHighPoint endHighPoint ≠ 0

/-- Atomic evidence explicitly carries the non-tie condition at both endpoints. -/
theorem LocalizedAxialAtomicSpatialEvidence.nonTie
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame)
    (atomic : input.LocalizedAxialAtomicSpatialEvidence
      axisStart axisEnd startFrame endFrame) :
    input.compareLocalizedOccurrenceRule3Through5Keys
        startFrame.firstKey startFrame.secondKey ≠ Ordering.eq ∧
      input.compareLocalizedOccurrenceRule3Through5Keys
        endFrame.firstKey endFrame.secondKey ≠ Ordering.eq := by
  obtain ⟨startHigh, endHigh, _, _, _, _, startSelection, endSelection, _⟩ := atomic
  exact
    ⟨(input.localizedAxialHighOfEndpointFrame?_isSome_iff startFrame).mp
        (by rw [startSelection]; rfl),
      (input.localizedAxialHighOfEndpointFrame?_isSome_iff endFrame).mp
        (by rw [endSelection]; rfl)⟩

/-- Assemble atomic evidence from independently checked selections, exact coordinate lookups and a
nonzero measure. -/
theorem LocalizedAxialAtomicSpatialEvidence.ofEndpointComparisons
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd startHigh endHigh : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame)
    (startSelection :
      input.localizedAxialHighOfEndpointFrame? startFrame = some startHigh)
    (endSelection :
      input.localizedAxialHighOfEndpointFrame? endFrame = some endHigh)
    (axisStartPoint axisEndPoint startHighPoint endHighPoint : CartesianPoint3)
    (axisStartComputed : input.spatialPointAt? axisStart = some axisStartPoint)
    (axisEndComputed : input.spatialPointAt? axisEnd = some axisEndPoint)
    (startHighComputed : input.spatialPointAt? startHigh = some startHighPoint)
    (endHighComputed : input.spatialPointAt? endHigh = some endHighPoint)
    (nonzero : CartesianPoint3.axialChiralityMeasure axisStartPoint axisEndPoint
      startHighPoint endHighPoint ≠ 0) :
    input.LocalizedAxialAtomicSpatialEvidence axisStart axisEnd startFrame endFrame :=
  ⟨startHigh, endHigh, axisStartPoint, axisEndPoint, startHighPoint, endHighPoint,
    startSelection, endSelection,
    (input.spatialPointAt?_eq_some_iff axisStart axisStartPoint).mp axisStartComputed,
    (input.spatialPointAt?_eq_some_iff axisEnd axisEndPoint).mp axisEndComputed,
    (input.spatialPointAt?_eq_some_iff startHigh startHighPoint).mp startHighComputed,
    (input.spatialPointAt?_eq_some_iff endHigh endHighPoint).mp endHighComputed,
    nonzero⟩

/-- Under a supplied, atom-count-indexed spatial configuration, atomic evidence reduces to the two
non-tie selections plus a nonzero measure of the four concrete rational positions. -/
theorem exists_localizedAxialAtomicSpatialEvidence_of_spatial
    (input : CertifiedLocalizedCIPInput)
    (spatial : SpatialConfiguration)
    (observed : input.certified.input.spatial? = some spatial)
    (wellFormed :
      spatial.positions.length = input.certified.input.molecule.atomCount)
    (axisStart axisEnd startHigh endHigh : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame)
    (startSelection :
      input.localizedAxialHighOfEndpointFrame? startFrame = some startHigh)
    (endSelection :
      input.localizedAxialHighOfEndpointFrame? endFrame = some endHigh)
    (nonzero : CartesianPoint3.axialChiralityMeasure
      (spatial.positions[axisStart.val]'(by simp [wellFormed]))
      (spatial.positions[axisEnd.val]'(by simp [wellFormed]))
      (spatial.positions[startHigh.val]'(by simp [wellFormed]))
      (spatial.positions[endHigh.val]'(by simp [wellFormed])) ≠ 0) :
    input.LocalizedAxialAtomicSpatialEvidence axisStart axisEnd startFrame endFrame :=
  LocalizedAxialAtomicSpatialEvidence.ofEndpointComparisons input
    axisStart axisEnd startHigh endHigh startFrame endFrame
    startSelection endSelection
    (spatial.positions[axisStart.val]'(by simp [wellFormed]))
    (spatial.positions[axisEnd.val]'(by simp [wellFormed]))
    (spatial.positions[startHigh.val]'(by simp [wellFormed]))
    (spatial.positions[endHigh.val]'(by simp [wellFormed]))
    (input.spatialPointAt?_eq_some_get_of_spatial spatial observed wellFormed axisStart)
    (input.spatialPointAt?_eq_some_get_of_spatial spatial observed wellFormed axisEnd)
    (input.spatialPointAt?_eq_some_get_of_spatial spatial observed wellFormed startHigh)
    (input.spatialPointAt?_eq_some_get_of_spatial spatial observed wellFormed endHigh)
    nonzero

/-! ## Exact decomposition of the pure assignment layer -/

/-- The pure endpoint assignment layer succeeds exactly when the atomic spatial evidence holds.
This is a genuine iff: the right-hand side mentions no assignment, pair or descriptor. -/
theorem localizedAxialAssignmentOfEndpointFrames?_isSome_iff_atomic
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame) :
    (input.localizedAxialAssignmentOfEndpointFrames?
        axisStart axisEnd startFrame endFrame).isSome = true ↔
      input.LocalizedAxialAtomicSpatialEvidence
        axisStart axisEnd startFrame endFrame := by
  constructor
  · intro someComputed
    obtain ⟨assignment, computed⟩ := Option.isSome_iff_exists.mp someComputed
    have derived := input.localizedAxialAssignmentOfEndpointFrames?_sound
      axisStart axisEnd startFrame endFrame assignment computed
    obtain ⟨unit, descriptor⟩ := assignment
    obtain ⟨startDerived, endDerived, _axisStartEq, _axisEndEq,
      axisStartPoint, axisEndPoint, startHighPoint, endHighPoint,
      axisStartSemantic, axisEndSemantic, startHighSemantic, endHighSemantic,
      descriptorDerived⟩ := derived
    have startPair :=
      (input.localizedAxialEndpointPair?_eq_some_iff startFrame
        (unit.startHigh, unit.startLow)).mpr startDerived
    have endPair :=
      (input.localizedAxialEndpointPair?_eq_some_iff endFrame
        (unit.endHigh, unit.endLow)).mpr endDerived
    have startSelection :
        input.localizedAxialHighOfEndpointFrame? startFrame = some unit.startHigh := by
      rw [input.localizedAxialHighOfEndpointFrame?_eq_pair_fst, startPair]
      rfl
    have endSelection :
        input.localizedAxialHighOfEndpointFrame? endFrame = some unit.endHigh := by
      rw [input.localizedAxialHighOfEndpointFrame?_eq_pair_fst, endPair]
      rfl
    have nonzero : CartesianPoint3.axialChiralityMeasure axisStartPoint axisEndPoint
        startHighPoint endHighPoint ≠ 0 := by
      cases descriptor with
      | Ra =>
          simp only [RationalAxialSpatialDescriptor] at descriptorDerived
          exact ne_of_lt descriptorDerived
      | Sa =>
          simp only [RationalAxialSpatialDescriptor] at descriptorDerived
          exact ne_of_gt descriptorDerived
    exact ⟨unit.startHigh, unit.endHigh,
      axisStartPoint, axisEndPoint, startHighPoint, endHighPoint,
      startSelection, endSelection,
      axisStartSemantic, axisEndSemantic, startHighSemantic, endHighSemantic, nonzero⟩
  · intro atomic
    obtain ⟨startHigh, endHigh, axisStartPoint, axisEndPoint,
      startHighPoint, endHighPoint,
      startSelection, endSelection,
      axisStartSemantic, axisEndSemantic, startHighSemantic, endHighSemantic,
      nonzero⟩ := atomic
    obtain ⟨startLow, startPair⟩ :=
      (input.localizedAxialHighOfEndpointFrame?_eq_some_iff_exists_pair
        startFrame startHigh).mp startSelection
    obtain ⟨endLow, endPair⟩ :=
      (input.localizedAxialHighOfEndpointFrame?_eq_some_iff_exists_pair
        endFrame endHigh).mp endSelection
    have axisStartComputed :=
      (input.spatialPointAt?_eq_some_iff axisStart axisStartPoint).mpr axisStartSemantic
    have axisEndComputed :=
      (input.spatialPointAt?_eq_some_iff axisEnd axisEndPoint).mpr axisEndSemantic
    have startHighComputed :=
      (input.spatialPointAt?_eq_some_iff startHigh startHighPoint).mpr startHighSemantic
    have endHighComputed :=
      (input.spatialPointAt?_eq_some_iff endHigh endHighPoint).mpr endHighSemantic
    have descriptorSome := axialDescriptorOfSpatialReferences?_isSome_of_ne_zero
      axisStartPoint axisEndPoint startHighPoint endHighPoint nonzero
    obtain ⟨descriptor, descriptorComputed⟩ :=
      Option.isSome_iff_exists.mp descriptorSome
    refine Option.isSome_iff_exists.mpr ⟨
      { unit :=
          { axisStart := axisStart
            axisEnd := axisEnd
            startHigh := startHigh
            startLow := startLow
            endHigh := endHigh
            endLow := endLow }
        descriptor := descriptor }, ?_⟩
    simp [localizedAxialAssignmentOfEndpointFrames?, startPair, endPair,
      axisStartComputed, axisEndComputed, startHighComputed, endHighComputed,
      descriptorComputed]

/-- The executable assignment and its independent meaning are both constructed from atomic
spatial evidence. -/
theorem exists_localizedAxialAssignment_of_atomicEvidence
    (input : CertifiedLocalizedCIPInput)
    (axisStart axisEnd : input.Atom)
    (startFrame endFrame : input.LocalizedRule3EndpointKeyFrame)
    (atomic : input.LocalizedAxialAtomicSpatialEvidence
      axisStart axisEnd startFrame endFrame) :
    ∃ assignment,
      input.localizedAxialAssignmentOfEndpointFrames?
          axisStart axisEnd startFrame endFrame = some assignment ∧
        input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
          axisStart axisEnd startFrame endFrame assignment := by
  have someComputed :=
    (input.localizedAxialAssignmentOfEndpointFrames?_isSome_iff_atomic
      axisStart axisEnd startFrame endFrame).mpr atomic
  obtain ⟨assignment, computed⟩ := Option.isSome_iff_exists.mp someComputed
  exact ⟨assignment, computed,
    (input.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
      axisStart axisEnd startFrame endFrame assignment).mp computed⟩

/-! ## Per-topology construction at an arbitrary carrier fuel -/

/-- Atomic spatial evidence for one perceived even open cumulene, quantified over every canonical
endpoint topology and every pair of successful complete endpoint compilations at the supplied
carrier fuel.  Topology detection, endpoint compilation and traversal fuel stay explicit
hypotheses of the consumer. -/
def LocalizedEvenCumuleneAtomicSpatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence carrierFuel axis)) : Prop :=
  ∀ (topology : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (leftCompilation rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame
      carrierFuel),
    input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
        (input.localizedEvenAxialFirstChildOccurrence carrierFuel axis) topology →
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        (input.localizedEvenAxialRootOccurrence carrierFuel axis)
        view
        (input.buildLocalizedDescriptorBearingRule3Frame?
          (input.localizedEvenAxialRootOccurrence carrierFuel axis)
          view (localizedEvenCumuleneAxialRule3EvaluationFuel carrierFuel))
        topology.initial.left topology.initial.right topology.initial.leftCursor =
      some leftCompilation →
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        (input.localizedEvenAxialRootOccurrence carrierFuel axis)
        view
        (input.buildLocalizedDescriptorBearingRule3Frame?
          (input.localizedEvenAxialRootOccurrence carrierFuel axis)
          view (localizedEvenCumuleneAxialRule3EvaluationFuel carrierFuel))
        topology.right topology.rightPartner topology.rightCursor =
      some rightCompilation →
    input.LocalizedAxialAtomicSpatialEvidence
      topology.initial.left topology.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame

/-- The atom-count specialization consumed by the existing public readiness package. -/
abbrev LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)) : Prop :=
  input.LocalizedEvenCumuleneAtomicSpatialEvidence
    (carrierFuel := input.certified.input.molecule.atomCount) axis view

/-- At an arbitrary carrier fuel, supplied topology detection, supplied endpoint compilations and
atomic spatial evidence construct an actual result of the parameterized compiler together with
its independent declarative meaning.  The topology and key-computation obligations are not
discharged here; they are explicit equalities. -/
theorem exists_localizedEvenCumuleneAxialAssignmentWith?_of_atomicEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (topology : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (topologyComputed : input.localizedEvenCumuleneEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftCompilation rightCompilation :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf topology.initial.left topology.initial.right
          topology.initial.leftCursor = some leftCompilation)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf topology.right topology.rightPartner
          topology.rightCursor = some rightCompilation)
    (atomic : input.LocalizedAxialAtomicSpatialEvidence
      topology.initial.left topology.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame) :
    ∃ result,
      input.localizedEvenCumuleneAxialAssignmentWith?
          target occurrence view rule3FrameOf = some result ∧
        input.DeclarativeLocalizedEvenCumuleneAxialAssignmentWith
          target occurrence view Rule3FrameMeaning result := by
  obtain ⟨assignment, assignmentComputed, _assignmentMeaning⟩ :=
    input.exists_localizedAxialAssignment_of_atomicEvidence
      topology.initial.left topology.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame atomic
  let result : input.LocalizedEvenCumuleneAxialResult carrierFuel :=
    { topology, leftCompilation, rightCompilation, assignment }
  have computed :
      input.localizedEvenCumuleneAxialAssignmentWith?
          target occurrence view rule3FrameOf = some result := by
    simp [localizedEvenCumuleneAxialAssignmentWith?, topologyComputed,
      leftComputed, rightComputed, assignmentComputed, result]
  exact ⟨result, computed,
    input.localizedEvenCumuleneAxialAssignmentWith?_sound target occurrence view
      rule3FrameOf Rule3FrameMeaning rule3FrameSound result computed⟩

/-! ## Replacement of the assumed per-cumulene spatial evidence -/

/-- Atomic all-topologies evidence implies the former per-cumulene spatial evidence, which asked
directly for an assignment. -/
theorem LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount.toSpatialEvidenceAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (atomic :
      input.LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount axis view) :
    input.LocalizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount axis view := by
  intro topology leftCompilation rightCompilation declarative leftComputed rightComputed
  obtain ⟨assignment, assignmentComputed, _assignmentMeaning⟩ :=
    input.exists_localizedAxialAssignment_of_atomicEvidence
      topology.initial.left topology.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame
      (atomic topology leftCompilation rightCompilation declarative leftComputed rightComputed)
  exact ⟨assignment,
    (input.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
      topology.initial.left topology.right leftCompilation.endpointFrame
      rightCompilation.endpointFrame assignment).mp assignmentComputed⟩

/-- The replacement is exact, not a weakening: over the same canonical topologies and
compilations, the assumed assignment-existence predicate holds exactly when the atomic spatial
evidence holds. -/
theorem localizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount_iff_atomic
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)) :
    input.LocalizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount axis view ↔
      input.LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount axis view := by
  constructor
  · intro spatial topology leftCompilation rightCompilation
      declarative leftComputed rightComputed
    obtain ⟨assignment, derived⟩ :=
      spatial topology leftCompilation rightCompilation declarative leftComputed rightComputed
    exact
      (input.localizedAxialAssignmentOfEndpointFrames?_isSome_iff_atomic
        topology.initial.left topology.right leftCompilation.endpointFrame
        rightCompilation.endpointFrame).mp
        (Option.isSome_iff_exists.mpr ⟨assignment,
          (input.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
            topology.initial.left topology.right leftCompilation.endpointFrame
            rightCompilation.endpointFrame assignment).mpr derived⟩)
  · intro atomic
    exact LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount.toSpatialEvidenceAtAtomCount
      input axis view atomic

/-- The concrete production compiler emits a result with independent meaning from the
non-circular dependency package and atomic spatial evidence.  No topology, carrier, embedding or
fuel premise remains. -/
theorem exists_localizedEvenCumuleneAxialAssignment?_of_atomicSpatialEvidence_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (dependencyEvidence :
      input.LocalizedEvenCumuleneProductionDependencyEvidence axis view)
    (atomic :
      input.LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount axis view) :
    ∃ result,
      input.localizedEvenCumuleneAxialAssignment?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view = some result ∧
        input.DeclarativeLocalizedEvenCumuleneAxialAssignment
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view result :=
  input.exists_localizedEvenCumuleneAxialAssignment?_of_dependencyEvidence_at_atomCount
    axis view dependencyEvidence
    (LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount.toSpatialEvidenceAtAtomCount
      input axis view atomic)

/-- Source-facing form: finite chemical classification plus atomic spatial evidence. -/
theorem exists_localizedEvenCumuleneAxialAssignment?_of_chemicalEvidence_and_atomicSpatialEvidence
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (chemical :
      input.LocalizedEvenCumuleneChemicalProductionDependencyEvidence axis view)
    (atomic :
      input.LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount axis view) :
    ∃ result,
      input.localizedEvenCumuleneAxialAssignment?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view = some result ∧
        input.DeclarativeLocalizedEvenCumuleneAxialAssignment
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view result :=
  input.exists_localizedEvenCumuleneAxialAssignment?_of_atomicSpatialEvidence_at_atomCount
    axis view (chemical.toProductionEvidence input axis view) atomic

/-! ## Readiness with atomic spatial data -/

/-- Complete source-facing readiness for one perceived even open cumulene under the canonical
scheduled auxiliary state, with the circular assignment-existence conjunct replaced by atomic
spatial evidence. -/
def LocalizedEvenCumuleneChemicalAtomicReadyAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) : Prop :=
  let fuel := input.certified.input.molecule.atomCount
  let target := input.localizedEvenAxialRootOccurrence fuel axis
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let view := input.localizedDependencyView state target
  input.LocalizedEvenCumuleneChemicalProductionDependencyEvidence axis view ∧
    input.LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount axis view

/-- Atomic readiness implies the former readiness package. -/
theorem LocalizedEvenCumuleneChemicalAtomicReadyAtAtomCount.toChemicalReady
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (ready :
      input.LocalizedEvenCumuleneChemicalAtomicReadyAtAtomCount axis) :
    input.LocalizedEvenCumuleneChemicalReadyAtAtomCount axis := by
  let fuel := input.certified.input.molecule.atomCount
  let target := input.localizedEvenAxialRootOccurrence fuel axis
  let state := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let view := input.localizedDependencyView state target
  change input.LocalizedEvenCumuleneChemicalProductionDependencyEvidence axis view ∧
    input.LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount axis view at ready
  change input.LocalizedEvenCumuleneChemicalProductionDependencyEvidence axis view ∧
    input.LocalizedEvenCumuleneChemicalSpatialEvidenceAtAtomCount axis view
  exact ⟨ready.1,
    LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount.toSpatialEvidenceAtAtomCount
      input axis view ready.2⟩

/-- A perceived even cumulene that is atomically ready has one independently conforming public
assignment and literal global physical-unit count one. -/
theorem every_chemicallyApplicable_localizedEvenCumulene_public_exactly_once_of_atomicReadiness
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (ready :
      input.LocalizedEvenCumuleneChemicalAtomicReadyAtAtomCount axis) :
    ∃ assignment,
      LocalizedScheduledStereochemicalAssignment.evenAxial assignment ∈
          input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount ∧
        input.DeclarativeLocalizedEvenAxialSpatialAssignment
          input.certified.input.molecule.atomCount assignment ∧
        List.count (.evenAxial axis)
          ((input.analyzeLocalizedScheduledStereochemistry
            input.certified.input.molecule.atomCount).map
              LocalizedScheduledStereochemicalAssignment.physicalUnit) = 1 :=
  input.every_chemicallyApplicable_localizedEvenCumulene_public_exactly_once axis
    (LocalizedEvenCumuleneChemicalAtomicReadyAtAtomCount.toChemicalReady input axis ready)

/-! ## Supplied auxiliary states -/

/-- Readiness at an arbitrary supplied auxiliary state and atom-count fuel.  This does not identify
the supplied state with the canonical scheduler state and does not mention any family reference
state. -/
def LocalizedEvenCumuleneAtomicReadyWithState
    (input : CertifiedLocalizedCIPInput)
    (state : input.LocalizedAuxiliaryState
      input.certified.input.molecule.atomCount)
    (axis : input.LocalizedEvenAxialChain) : Prop :=
  let target := input.localizedEvenAxialRootOccurrence
    input.certified.input.molecule.atomCount axis
  let view := input.localizedDependencyView state target
  input.LocalizedEvenCumuleneProductionDependencyEvidence axis view ∧
    input.LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount axis view

/-- At any supplied auxiliary state at atom-count fuel, readiness with atomic spatial evidence
produces an actual state-relative assignment together with its independent meaning. -/
theorem exists_localizedEvenAxialSpatialAssignmentAtWithState?_of_atomicReady
    (input : CertifiedLocalizedCIPInput)
    (state : input.LocalizedAuxiliaryState
      input.certified.input.molecule.atomCount)
    (axis : input.LocalizedEvenAxialChain)
    (ready : input.LocalizedEvenCumuleneAtomicReadyWithState state axis) :
    ∃ assignment,
      input.localizedEvenAxialSpatialAssignmentAtWithState?
          input.certified.input.molecule.atomCount state axis = some assignment ∧
        input.DeclarativeLocalizedEvenAxialSpatialAssignmentWithState
          input.certified.input.molecule.atomCount state assignment := by
  let fuel := input.certified.input.molecule.atomCount
  let target := input.localizedEvenAxialRootOccurrence fuel axis
  let view := input.localizedDependencyView state target
  change input.LocalizedEvenCumuleneProductionDependencyEvidence axis view ∧
    input.LocalizedEvenCumuleneAtomicSpatialEvidenceAtAtomCount axis view at ready
  obtain ⟨result, resultComputed, _resultMeaning⟩ :=
    input.exists_localizedEvenCumuleneAxialAssignment?_of_atomicSpatialEvidence_at_atomCount
      axis view ready.1 ready.2
  let assignment : input.LocalizedEvenAxialSpatialAssignment fuel := { axis, result }
  have computed : input.localizedEvenAxialSpatialAssignmentAtWithState?
      fuel state axis = some assignment := by
    simp [localizedEvenAxialSpatialAssignmentAtWithState?, fuel, target, view,
      resultComputed, assignment]
  exact ⟨assignment, computed,
    input.localizedEvenAxialSpatialAssignmentAtWithState?_sound
      fuel state axis assignment computed⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
