import TetraStereo.OneCenter.LocalizedOddCumuleneAssignmentCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Chemical applicability for descriptor-bearing Rule-3 nodes

`LocalizedDescriptorBearingRule3NodeWithSupport` is an exact executable support certificate, but
its geometrical constructors contain the conclusion that a complete spatial compiler returned
`some`.  This module factors that conclusion into independent chemical premises:

* exactly two canonical physical reference cursors at each endpoint;
* totality of the strictly smaller common Rule-3 frame on two valid cursors; and
* the declarative exact rational spatial relation for the endpoint frames that are produced.

The resulting node theorem proves executable support.  In particular, none of the chemical
geometry constructors below assumes success of the complete ordinary, cyclic, or odd-cumulene
spatial-unit evaluator.
-/

namespace CertifiedLocalizedCIPInput

/-- The strictly smaller Rule-3 callback is total on every pair of valid physical reference
cursors and preserves the two-key arity needed by an endpoint.  This is deliberately separate
from chemical endpoint applicability: the recursive fuel theorem will discharge it. -/
def LocalizedDescriptorBearingRule3PairFrameTotal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∀ firstCursor secondCursor,
    input.LocalizedRerootCursorValid firstCursor →
    input.LocalizedRerootCursorValid secondCursor →
    ∃ frame,
      rule3FrameOf [firstCursor, secondCursor] = some frame ∧
        frame.keys.length = 2

/-- Prior-level reachable support and the finite reference-expansion bound make the actual
descriptor-bearing recursive callback total on every valid cursor pair.  Two-cursor frames cannot
trigger the four-ligand coupled-topology ambiguity. -/
theorem LocalizedDescriptorBearingRule3ReachableSupportThrough.pairFrameTotal
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (support : input.LocalizedDescriptorBearingRule3ReachableSupportThrough
      target view maximumFuel)
    (frameFuel : Nat)
    (bounded : frameFuel ≤ maximumFuel)
    (coversReferences : 2 * (carrierFuel + 1) < frameFuel) :
    input.LocalizedDescriptorBearingRule3PairFrameTotal
      (input.buildLocalizedDescriptorBearingRule3Frame? target view frameFuel) := by
  intro firstCursor secondCursor firstValid secondValid
  have resolved :=
    LocalizedDescriptorBearingRule3ReachableSupportThrough.resolved
      input target view support
  have lengthNotFour : ([firstCursor, secondCursor] :
      List (input.LocalizedRerootCursor carrierFuel)).length ≠ 4 := by simp
  obtain ⟨keyFuel, frameFuelIdentity⟩ : ∃ keyFuel, frameFuel = keyFuel + 1 := by
    cases frameFuel with
    | zero => omega
    | succ keyFuel => exact ⟨keyFuel, rfl⟩
  subst frameFuel
  obtain ⟨frame, frameComputed⟩ :=
    input.exists_buildLocalizedDescriptorBearingRule3Frame?_of_twice_lt
      target view resolved (keyFuel + 1) bounded coversReferences [firstCursor, secondCursor]
      (input.localizedDescriptorBearingRule3FrameTopologyResolved_of_length_ne_four
        target view keyFuel [firstCursor, secondCursor] lengthNotFour)
      (by
        intro cursor present
        simp at present
        rcases present with rfl | rfl
        · exact firstValid
        · exact secondValid)
  refine ⟨frame, frameComputed, ?_⟩
  simpa using input.buildLocalizedDescriptorBearingRule3Frame?_keys_length_eq
    target view (keyFuel + 1) [firstCursor, secondCursor] frame frameComputed

/-- Computation-free chemical endpoint applicability: there are exactly two explicit
substituents, and each has its unique canonical physical reference cursor. -/
def LocalizedRule3ChemicalEndpointApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ first second firstCursor secondCursor,
    input.localizedRule3ExplicitSubstituents endpoint partner = [first, second] ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor firstCursor first ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor secondCursor second

/-- Chemical endpoint applicability plus smaller-frame totality forces the actual Rules-1a--5
endpoint compiler to return a frame. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_chemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (applicable : input.LocalizedRule3ChemicalEndpointApplicability
      endpoint partner endpointCursor) :
    ∃ frame,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf endpoint partner endpointCursor = some frame := by
  rcases applicable with ⟨first, second, firstCursor, secondCursor,
    candidates, firstCanonical, secondCanonical⟩
  have firstValid := firstCanonical.valid input endpointCursor firstCursor first
  have secondValid := secondCanonical.valid input endpointCursor secondCursor second
  exact input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_two_canonical_references
    target view rule3FrameOf endpoint partner first second endpointCursor
    firstCursor secondCursor candidates firstCanonical secondCanonical
    (pairTotal firstCursor secondCursor firstValid secondValid)

/-- Independent ordinary/branched individual-double-bond applicability.  Topology and canonical
endpoint existence are fixed first.  Spatial evidence is then required for whichever unique
endpoint compilations those data produce; success of the complete occurrence evaluator is not a
premise. -/
def LocalizedRule3OccurrenceGeometryChemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∃ topology,
    input.localizedRule3PhysicalEndpointCursorFrame? occurrence = some topology ∧
      input.LocalizedRule3ChemicalEndpointApplicability
        topology.left topology.right topology.leftCursor ∧
      input.LocalizedRule3ChemicalEndpointApplicability
        topology.right topology.left topology.rightCursor ∧
      ∀ leftCompilation rightCompilation,
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view rule3FrameOf topology.left topology.right topology.leftCursor =
          some leftCompilation →
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view rule3FrameOf topology.right topology.left topology.rightCursor =
          some rightCompilation →
        ∃ unit,
          input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
            topology.left topology.right
            leftCompilation.endpointFrame rightCompilation.endpointFrame
            (fun reference key => ∃ cursor,
              input.DeclarativeLocalizedRule3ReferenceCursor
                topology.leftCursor cursor reference ∧
              ((cursor = leftCompilation.firstCursor ∧
                  key = leftCompilation.endpointFrame.firstKey) ∨
               (cursor = leftCompilation.secondCursor ∧
                  key = leftCompilation.endpointFrame.secondKey)))
            (fun reference key => ∃ cursor,
              input.DeclarativeLocalizedRule3ReferenceCursor
                topology.rightCursor cursor reference ∧
              ((cursor = rightCompilation.firstCursor ∧
                  key = rightCompilation.endpointFrame.firstKey) ∨
               (cursor = rightCompilation.secondCursor ∧
                  key = rightCompilation.endpointFrame.secondKey)))
            unit

/-- Independent individual-double-bond applicability forces the actual descriptor-bearing
occurrence evaluator to succeed. -/
theorem exists_localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_of_chemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (applicable : input.LocalizedRule3OccurrenceGeometryChemicalApplicability
      target occurrence view rule3FrameOf) :
    ∃ result,
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf = some result := by
  rcases applicable with ⟨topology, topologyComputed, leftApplicable, rightApplicable,
    spatial⟩
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_chemicalApplicability
      target view rule3FrameOf pairTotal topology.left topology.right
      topology.leftCursor leftApplicable
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_chemicalApplicability
      target view rule3FrameOf pairTotal topology.right topology.left
      topology.rightCursor rightApplicable
  obtain ⟨unit, unitMeaning⟩ := spatial leftCompilation rightCompilation
    leftComputed rightComputed
  have leftDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view rule3FrameOf
      (fun cursors frame => rule3FrameOf cursors = some frame)
      (fun _cursors _frame computed => computed)
      topology.left topology.right topology.leftCursor leftCompilation leftComputed
  have rightDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view rule3FrameOf
      (fun cursors frame => rule3FrameOf cursors = some frame)
      (fun _cursors _frame computed => computed)
      topology.right topology.left topology.rightCursor rightCompilation rightComputed
  have unitComputed :
      input.localizedRule3DescriptorBearingSpatialUnit?
          topology.left topology.right leftCompilation.endpointFrame
            rightCompilation.endpointFrame = some unit :=
    (input.localizedRule3DescriptorBearingSpatialUnit?_eq_some_iff
      topology.left topology.right leftCompilation.endpointFrame
      rightCompilation.endpointFrame _ _
      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
        input target view (fun cursors frame => rule3FrameOf cursors = some frame)
        topology.left topology.right topology.leftCursor leftCompilation leftDerived)
      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
        input target view (fun cursors frame => rule3FrameOf cursors = some frame)
        topology.right topology.left topology.rightCursor rightCompilation rightDerived)
      unit).mpr unitMeaning
  exact ⟨{ topology, leftCompilation, rightCompilation, unit }, by
    simp [localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?, topologyComputed,
      leftComputed, rightComputed, unitComputed]⟩

/-- Independent required-monocycle applicability.  Route, endpoint, rational geometry, and P-93
assignment are premises; success of the complete cyclic evaluator is the conclusion. -/
def LocalizedRule3RequiredMonocyclicChemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ policyResult,
    input.localizedRule3CyclicAuthorityRoute? occurrence =
        some (.ordinaryMonocyclicPolicy initial closure policyResult) ∧
      policyResult.policy = .requireEZ ∧
      input.LocalizedRule3ChemicalEndpointApplicability
        initial.left initial.right initial.leftCursor ∧
      input.LocalizedRule3ChemicalEndpointApplicability
        initial.right initial.left initial.rightCursor ∧
      ∀ leftCompilation rightCompilation,
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view rule3FrameOf initial.left initial.right initial.leftCursor =
          some leftCompilation →
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view rule3FrameOf initial.right initial.left initial.rightCursor =
          some rightCompilation →
        ∃ unit cyclicGeometry descriptor,
          input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
            initial.left initial.right
            leftCompilation.endpointFrame rightCompilation.endpointFrame
            (fun reference key => ∃ cursor,
              input.DeclarativeLocalizedRule3ReferenceCursor
                initial.leftCursor cursor reference ∧
              ((cursor = leftCompilation.firstCursor ∧
                  key = leftCompilation.endpointFrame.firstKey) ∨
               (cursor = leftCompilation.secondCursor ∧
                  key = leftCompilation.endpointFrame.secondKey)))
            (fun reference key => ∃ cursor,
              input.DeclarativeLocalizedRule3ReferenceCursor
                initial.rightCursor cursor reference ∧
              ((cursor = rightCompilation.firstCursor ∧
                  key = rightCompilation.endpointFrame.firstKey) ∨
               (cursor = rightCompilation.secondCursor ∧
                  key = rightCompilation.endpointFrame.secondKey)))
            unit ∧
          Rule3GeometryRefinesMonocyclicSeniorLigandGeometry unit.geometry cyclicGeometry ∧
          BlueBookP93.Cyclic.RequiredMonocyclicEZAssignment
            policyResult.carrier.ring.card policyResult.doubleBondCount
            cyclicGeometry descriptor

/-- Independent required-monocycle applicability forces the complete cyclic evaluator to
succeed. -/
theorem exists_localizedRule3RequiredMonocyclicEZWith?_of_chemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (applicable : input.LocalizedRule3RequiredMonocyclicChemicalApplicability
      target occurrence view rule3FrameOf initial closure) :
    ∃ result,
      input.localizedRule3RequiredMonocyclicEZWith?
        target occurrence view rule3FrameOf = some result := by
  rcases applicable with ⟨policyResult, routeComputed, required,
    leftApplicable, rightApplicable, spatial⟩
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_chemicalApplicability
      target view rule3FrameOf pairTotal initial.left initial.right
      initial.leftCursor leftApplicable
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_chemicalApplicability
      target view rule3FrameOf pairTotal initial.right initial.left
      initial.rightCursor rightApplicable
  obtain ⟨unit, cyclicGeometry, descriptor, unitMeaning, geometryMeaning,
    descriptorMeaning⟩ := spatial leftCompilation rightCompilation leftComputed rightComputed
  let result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel :=
    { initial
      closure
      policyResult
      leftCompilation
      rightCompilation
      unit
      descriptor }
  refine ⟨result, ?_⟩
  apply (input.localizedRule3RequiredMonocyclicEZWith?_eq_some_iff_of_required_compilations
    target occurrence view rule3FrameOf
    (fun cursors frame => rule3FrameOf cursors = some frame)
    (fun _cursors _frame computed => computed)
    initial closure policyResult leftCompilation rightCompilation routeComputed required
    leftComputed rightComputed unit descriptor).mpr
  exact ⟨unitMeaning, cyclicGeometry, geometryMeaning, descriptorMeaning⟩

/-- Independent odd-cumulene source applicability. -/
def LocalizedRule3OddCumuleneGeometryChemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∃ topology,
    input.localizedRule3OddCumuleneEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology ∧
      input.LocalizedRule3ChemicalEndpointApplicability
        topology.initial.left topology.initial.right topology.initial.leftCursor ∧
      input.LocalizedRule3ChemicalEndpointApplicability
        topology.right topology.rightPartner topology.rightCursor ∧
      ∀ leftCompilation rightCompilation,
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view rule3FrameOf topology.initial.left topology.initial.right
              topology.initial.leftCursor = some leftCompilation →
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view rule3FrameOf topology.right topology.rightPartner
              topology.rightCursor = some rightCompilation →
        ∃ unit,
          input.DeclarativeLocalizedRule3ExtendedDescriptorBearingSpatialUnit
            topology.initial.left topology.initial.right topology.rightPartner topology.right
            leftCompilation.endpointFrame rightCompilation.endpointFrame
            (fun reference key => ∃ cursor,
              input.DeclarativeLocalizedRule3ReferenceCursor
                topology.initial.leftCursor cursor reference ∧
              ((cursor = leftCompilation.firstCursor ∧
                  key = leftCompilation.endpointFrame.firstKey) ∨
               (cursor = leftCompilation.secondCursor ∧
                  key = leftCompilation.endpointFrame.secondKey)))
            (fun reference key => ∃ cursor,
              input.DeclarativeLocalizedRule3ReferenceCursor
                topology.rightCursor cursor reference ∧
              ((cursor = rightCompilation.firstCursor ∧
                  key = rightCompilation.endpointFrame.firstKey) ∨
               (cursor = rightCompilation.secondCursor ∧
                  key = rightCompilation.endpointFrame.secondKey)))
            unit

/-- Independent odd-cumulene applicability forces its complete descriptor-bearing spatial source
evaluator to succeed. -/
theorem exists_localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_of_chemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (applicable : input.LocalizedRule3OddCumuleneGeometryChemicalApplicability
      target occurrence view rule3FrameOf) :
    ∃ result,
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf = some result := by
  rcases applicable with ⟨topology, topologyComputed, leftApplicable, rightApplicable,
    spatial⟩
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_chemicalApplicability
      target view rule3FrameOf pairTotal topology.initial.left topology.initial.right
      topology.initial.leftCursor leftApplicable
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_chemicalApplicability
      target view rule3FrameOf pairTotal topology.right topology.rightPartner
      topology.rightCursor rightApplicable
  obtain ⟨unit, unitMeaning⟩ := spatial leftCompilation rightCompilation
    leftComputed rightComputed
  have leftDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view rule3FrameOf
      (fun cursors frame => rule3FrameOf cursors = some frame)
      (fun _cursors _frame computed => computed)
      topology.initial.left topology.initial.right topology.initial.leftCursor
      leftCompilation leftComputed
  have rightDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view rule3FrameOf
      (fun cursors frame => rule3FrameOf cursors = some frame)
      (fun _cursors _frame computed => computed)
      topology.right topology.rightPartner topology.rightCursor
      rightCompilation rightComputed
  have unitComputed :=
    (input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_eq_some_iff_of_compilations
      target occurrence view rule3FrameOf topology leftCompilation rightCompilation unit
      topologyComputed leftComputed rightComputed
      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
        input target view (fun cursors frame => rule3FrameOf cursors = some frame)
        topology.initial.left topology.initial.right topology.initial.leftCursor
        leftCompilation leftDerived)
      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
        input target view (fun cursors frame => rule3FrameOf cursors = some frame)
        topology.right topology.rightPartner topology.rightCursor
        rightCompilation rightDerived)).mpr unitMeaning
  exact ⟨{ topology, leftCompilation, rightCompilation, unit }, unitComputed⟩

/-- Source-facing chemical classification for one callback-parameterized Rule-3 node.  Geometry
cases contain only endpoint applicability and independent geometry; complete evaluator success is
absent. -/
inductive LocalizedDescriptorBearingRule3NodeChemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop
  | structural
      (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
  | internalCumulatedAxis {initial previousAxis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.internal initial previousAxis))
  | omittedMonocycle {initial closure routeInitial routeClosure policyResult}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.ringClosure initial closure))
      (routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
        some (.ordinaryMonocyclicPolicy routeInitial routeClosure policyResult))
      (omitted : policyResult.policy = .permanentlyOmit)
  | requiredMonocycle {initial closure}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.ringClosure initial closure))
      (applicable : input.LocalizedRule3RequiredMonocyclicChemicalApplicability
        target occurrence view rule3FrameOf initial closure)
  | evenCumulatedAxis {initial axis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.terminalStart initial))
      (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
      (notOrdinary : axis.doubleBondCount ≠ 1)
      (notPlanar : ¬ Odd axis.doubleBondCount)
  | ordinaryGeometry {initial axis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.terminalStart initial))
      (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
      (ordinary : axis.doubleBondCount = 1)
      (applicable : input.LocalizedRule3OccurrenceGeometryChemicalApplicability
        target occurrence view rule3FrameOf)
  | branchedGeometry {initial first second rest}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.branched initial first second rest))
      (applicable : input.LocalizedRule3OccurrenceGeometryChemicalApplicability
        target occurrence view rule3FrameOf)
  | oddCumuleneGeometry {initial axis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.terminalStart initial))
      (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
      (notOrdinary : axis.doubleBondCount ≠ 1)
      (planar : Odd axis.doubleBondCount)
      (applicable : input.LocalizedRule3OddCumuleneGeometryChemicalApplicability
        target occurrence view rule3FrameOf)

/-- The chemical classification and strictly smaller pair-frame totality close the former
executable node-support gap. -/
theorem LocalizedDescriptorBearingRule3NodeChemicalApplicability.support
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (applicable : input.LocalizedDescriptorBearingRule3NodeChemicalApplicability
      target view rule3FrameOf occurrence) :
    input.LocalizedDescriptorBearingRule3NodeWithSupport
      target view rule3FrameOf occurrence := by
  cases applicable with
  | structural notEdge => exact .structural notEdge
  | internalCumulatedAxis edge entryComputed =>
      exact .internalCumulatedAxis edge entryComputed
  | omittedMonocycle edge entryComputed routeComputed omitted =>
      exact .omittedMonocycle edge entryComputed routeComputed omitted
  | requiredMonocycle edge entryComputed chemical =>
      obtain ⟨result, resultComputed⟩ :=
        input.exists_localizedRule3RequiredMonocyclicEZWith?_of_chemicalApplicability
          target occurrence view rule3FrameOf pairTotal _ _ chemical
      exact .cyclicGeometry result edge entryComputed resultComputed
  | evenCumulatedAxis edge entryComputed axisComputed notOrdinary notPlanar =>
      exact .evenCumulatedAxis edge entryComputed axisComputed notOrdinary notPlanar
  | ordinaryGeometry edge entryComputed axisComputed ordinary chemical =>
      obtain ⟨result, resultComputed⟩ :=
        input.exists_localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_of_chemicalApplicability
          target occurrence view rule3FrameOf pairTotal chemical
      exact .ordinaryGeometry result edge entryComputed axisComputed ordinary resultComputed
  | branchedGeometry edge entryComputed chemical =>
      obtain ⟨result, resultComputed⟩ :=
        input.exists_localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_of_chemicalApplicability
          target occurrence view rule3FrameOf pairTotal chemical
      exact .branchedGeometry result edge entryComputed resultComputed
  | oddCumuleneGeometry edge entryComputed axisComputed notOrdinary planar chemical =>
      obtain ⟨result, resultComputed⟩ :=
        input.exists_localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_of_chemicalApplicability
          target occurrence view rule3FrameOf pairTotal chemical
      exact .oddCumuleneGeometry result edge entryComputed axisComputed notOrdinary planar
        resultComputed

/-- Recursive chemical-support step specialized to the production callback.  Prior reachable
support discharges only the strictly smaller two-cursor frame; the current node is discharged by
its source-facing chemical classification. -/
theorem LocalizedDescriptorBearingRule3NodeChemicalApplicability.support_of_priorSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (priorSupport : input.LocalizedDescriptorBearingRule3ReachableSupportThrough
      target view maximumFuel)
    (frameFuel : Nat)
    (bounded : frameFuel ≤ maximumFuel)
    (coversReferences : 2 * (carrierFuel + 1) < frameFuel)
    (applicable : input.LocalizedDescriptorBearingRule3NodeChemicalApplicability
      target view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view frameFuel)
        occurrence) :
    input.LocalizedDescriptorBearingRule3NodeWithSupport
      target view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view frameFuel)
        occurrence :=
  applicable.support input target occurrence view _
    (priorSupport.pairFrameTotal input target view frameFuel bounded coversReferences)

/-! ## Global finite chemical induction -/

/-- Chemical cases that never inspect a smaller Rule-3 frame.  These are precisely the cases
that remain admissible when a query is too shallow to pay the uniform reference-expansion bound. -/
inductive LocalizedDescriptorBearingRule3NonrecursiveChemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop
  | structural
      (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
  | internalCumulatedAxis {initial previousAxis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.internal initial previousAxis))
  | omittedMonocycle {initial closure routeInitial routeClosure policyResult}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.ringClosure initial closure))
      (routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
        some (.ordinaryMonocyclicPolicy routeInitial routeClosure policyResult))
      (omitted : policyResult.policy = .permanentlyOmit)
  | evenCumulatedAxis {initial axis}
      (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.terminalStart initial))
      (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
      (notOrdinary : axis.doubleBondCount ≠ 1)
      (notPlanar : ¬ Odd axis.doubleBondCount)

/-- A nonrecursive chemical case is already an executable node-support case for every callback. -/
theorem LocalizedDescriptorBearingRule3NonrecursiveChemicalApplicability.support
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (applicable : input.LocalizedDescriptorBearingRule3NonrecursiveChemicalApplicability
      occurrence) :
    input.LocalizedDescriptorBearingRule3NodeWithSupport
      target view rule3FrameOf occurrence := by
  cases applicable with
  | structural notEdge => exact .structural notEdge
  | internalCumulatedAxis edge entryComputed =>
      exact .internalCumulatedAxis edge entryComputed
  | omittedMonocycle edge entryComputed routeComputed omitted =>
      exact .omittedMonocycle edge entryComputed routeComputed omitted
  | evenCumulatedAxis edge entryComputed axisComputed notOrdinary notPlanar =>
      exact .evenCumulatedAxis edge entryComputed axisComputed notOrdinary notPlanar

/-- Source-facing chemical applicability for every structurally reachable query through a finite
bound.  At zero the node must be structural.  At successor `frameFuel`, either the query is below
the uniform two-cursor reference bound and is a genuinely nonrecursive chemical case, or it is
above that bound and has the full independent chemical classification.  Unlike
`LocalizedDescriptorBearingRule3ReachableSupportThrough`, this proposition contains no success
certificate for a complete ordinary, cyclic, or odd-cumulene spatial evaluator. -/
def LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (maximumFuel : Nat) : Prop :=
  ∀ fuel, fuel ≤ maximumFuel →
    ∀ cursor,
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ fuel →
      match fuel with
      | 0 => ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence
      | frameFuel + 1 =>
          (frameFuel ≤ 2 * (carrierFuel + 1) ∧
            input.LocalizedDescriptorBearingRule3NonrecursiveChemicalApplicability
              cursor.occurrence) ∨
          (2 * (carrierFuel + 1) < frameFuel ∧
            input.LocalizedDescriptorBearingRule3NodeChemicalApplicability
              target view
                (input.buildLocalizedDescriptorBearingRule3Frame?
                  target view frameFuel)
              cursor.occurrence)

/-- The global finite chemical classification closes the recursive support gap.  The proof is a
strong induction on the queried fuel: every deep geometrical node obtains its smaller pair frame
from the already established prefix, while shallow nonrecursive nodes need no callback. -/
theorem LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough.reachableSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (chemical : input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough
      target view maximumFuel) :
    input.LocalizedDescriptorBearingRule3ReachableSupportThrough
      target view maximumFuel := by
  induction maximumFuel using Nat.strong_induction_on with
  | h maximumFuel inductionHypothesis =>
      intro fuel bounded cursor valid covered
      have classified := chemical fuel bounded cursor valid covered
      cases fuel with
      | zero => exact classified
      | succ frameFuel =>
          rcases classified with
            ⟨_shallow, nonrecursive⟩ | ⟨coversReferences, currentChemical⟩
          · exact nonrecursive.support input target cursor.occurrence view
              (input.buildLocalizedDescriptorBearingRule3Frame? target view frameFuel)
          · have priorChemical :
                input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough
                  target view frameFuel := by
              intro priorFuel priorBound priorCursor priorValid priorCovered
              exact chemical priorFuel (by omega) priorCursor priorValid priorCovered
            have priorSupport :
                input.LocalizedDescriptorBearingRule3ReachableSupportThrough
                  target view frameFuel :=
              inductionHypothesis frameFuel (by omega) priorChemical
            exact currentChemical.support_of_priorSupport input target cursor.occurrence view
              priorSupport frameFuel (by rfl) coversReferences

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
