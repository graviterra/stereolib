import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3ChemicalApplicability

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact-pair endpoint demand applicability for descriptor-bearing Rule-3 nodes

`LocalizedRerootDescriptorBearingRule3ChemicalApplicability` discharges endpoint compilation from
`LocalizedDescriptorBearingRule3PairFrameTotal`, totality of the strictly smaller Rule-3 callback
on *every* pair of valid physical reference cursors.  A recursive demand tree only ever feeds the
callback the two canonical reference cursors that an endpoint's chemical topology evidence actually
selects, so the global totality premise is stronger than needed and awkward to close one node at a
time.

This module factors that premise down to the exact demand:

* `LocalizedRule3ExactPairFrameSupport` is a per-pair support certificate for one chosen pair of
  reference cursors, independent of any complete evaluator output;
* `LocalizedRule3ExactPairEndpointDemand` bundles the two canonical reference cursors of one
  endpoint with that endpoint's exact-pair support; and
* the ordinary, required-monocycle, and odd-cumulene applicability → success theorems are replayed
  with only those two exact endpoint demands, not a universe-quantified pair totality.

The independent geometry predicates (`DeclarativeLocalizedRule3DescriptorBearingSpatialUnit`,
`Rule3GeometryRefinesMonocyclicSeniorLigandGeometry`, …) are preserved verbatim: no constructor
below assumes the complete ordinary, cyclic, or odd-cumulene spatial-unit evaluator returned
`some`.  Compatibility back to the old global totality is proved as `…of_pairFrameTotal` and
`…of_chemicalApplicability`, so the older theorems remain derivable from the new surface.

This surface is for a recursive demand tree; no structural-rank decrease across endpoint reroot
references is asserted or assumed here.
-/

namespace CertifiedLocalizedCIPInput

/-- Exact-pair Rule-3 frame support: the caller-supplied callback returns a two-key frame on the
one specific pair of physical reference cursors the endpoint evidence selects.  Unlike
`LocalizedDescriptorBearingRule3PairFrameTotal` this quantifies neither a validity universe nor an
arbitrary pair; it is precisely the demand the endpoint compiler places on the callback. -/
def LocalizedRule3ExactPairFrameSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ frame,
    rule3FrameOf [firstCursor, secondCursor] = some frame ∧
      frame.keys.length = 2

/-- The old global pair totality is exactly the collection of all exact-pair supports: for a valid
pair it produces the same certificate. -/
theorem LocalizedRule3ExactPairFrameSupport.of_pairFrameTotal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (firstValid : input.LocalizedRerootCursorValid firstCursor)
    (secondValid : input.LocalizedRerootCursorValid secondCursor) :
    input.LocalizedRule3ExactPairFrameSupport rule3FrameOf firstCursor secondCursor :=
  pairTotal firstCursor secondCursor firstValid secondValid

/-- Two canonical physical reference cursors at one endpoint together with the exact-pair Rule-3
frame demand those cursors place on the callback.  This is the endpoint-level premise the
generalized applicability theorems consume. -/
def LocalizedRule3ExactPairEndpointDemand
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ first second firstCursor secondCursor,
    input.localizedRule3ExplicitSubstituents endpoint partner = [first, second] ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor firstCursor first ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor secondCursor second ∧
      input.LocalizedRule3ExactPairFrameSupport rule3FrameOf firstCursor secondCursor

/-- Chemical endpoint applicability plus global pair totality yields the exact-pair endpoint
demand: the canonical references are valid, so the global totality covers their exact pair. -/
theorem LocalizedRule3ExactPairEndpointDemand.of_chemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (applicable : input.LocalizedRule3ChemicalEndpointApplicability
      endpoint partner endpointCursor) :
    input.LocalizedRule3ExactPairEndpointDemand rule3FrameOf endpoint partner endpointCursor := by
  rcases applicable with ⟨first, second, firstCursor, secondCursor,
    candidates, firstCanonical, secondCanonical⟩
  exact ⟨first, second, firstCursor, secondCursor, candidates, firstCanonical, secondCanonical,
    pairTotal firstCursor secondCursor
      (firstCanonical.valid input endpointCursor firstCursor first)
      (secondCanonical.valid input endpointCursor secondCursor second)⟩

/-- An exact-pair endpoint demand is sufficient for the actual Rules-1a--5 endpoint compiler to
return a frame: this is the existing two-canonical-reference helper fed with the exact-pair support
instead of a global totality. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_exactPairDemand
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (demand : input.LocalizedRule3ExactPairEndpointDemand
      rule3FrameOf endpoint partner endpointCursor) :
    ∃ frame,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf endpoint partner endpointCursor = some frame := by
  rcases demand with ⟨first, second, firstCursor, secondCursor,
    candidates, firstCanonical, secondCanonical, exactSupport⟩
  exact input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_two_canonical_references
    target view rule3FrameOf endpoint partner first second endpointCursor
    firstCursor secondCursor candidates firstCanonical secondCanonical exactSupport

/-- Independent ordinary/branched individual-double-bond applicability with only the two exact
endpoint pair demands.  Topology, canonical endpoint existence, and exact-pair callback support are
fixed first.  Spatial evidence is then required for whichever unique endpoint compilations those
data produce; success of the complete occurrence evaluator is not a premise. -/
def LocalizedRule3OccurrenceGeometryExactPairDemandApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∃ topology,
    input.localizedRule3PhysicalEndpointCursorFrame? occurrence = some topology ∧
      input.LocalizedRule3ExactPairEndpointDemand rule3FrameOf
        topology.left topology.right topology.leftCursor ∧
      input.LocalizedRule3ExactPairEndpointDemand rule3FrameOf
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

/-- Global pair totality recovers the exact-pair demand version of the ordinary applicability. -/
theorem LocalizedRule3OccurrenceGeometryExactPairDemandApplicability.of_chemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (applicable : input.LocalizedRule3OccurrenceGeometryChemicalApplicability
      target occurrence view rule3FrameOf) :
    input.LocalizedRule3OccurrenceGeometryExactPairDemandApplicability
      target occurrence view rule3FrameOf := by
  rcases applicable with ⟨topology, topologyComputed, leftApplicable, rightApplicable, spatial⟩
  exact ⟨topology, topologyComputed,
    LocalizedRule3ExactPairEndpointDemand.of_chemicalApplicability input
      rule3FrameOf pairTotal topology.left topology.right topology.leftCursor leftApplicable,
    LocalizedRule3ExactPairEndpointDemand.of_chemicalApplicability input
      rule3FrameOf pairTotal topology.right topology.left topology.rightCursor rightApplicable,
    spatial⟩

/-- Independent individual-double-bond applicability with exact-pair demands forces the actual
descriptor-bearing occurrence evaluator to succeed. -/
theorem exists_localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_of_exactPairDemandApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (applicable : input.LocalizedRule3OccurrenceGeometryExactPairDemandApplicability
      target occurrence view rule3FrameOf) :
    ∃ result,
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf = some result := by
  rcases applicable with ⟨topology, topologyComputed, leftDemand, rightDemand,
    spatial⟩
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_exactPairDemand
      target view rule3FrameOf topology.left topology.right
      topology.leftCursor leftDemand
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_exactPairDemand
      target view rule3FrameOf topology.right topology.left
      topology.rightCursor rightDemand
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

/-- Independent required-monocycle applicability with exact-pair demands.  Route, endpoint, exact
pair support, rational geometry, and P-93 assignment are premises; success of the complete cyclic
evaluator is the conclusion. -/
def LocalizedRule3RequiredMonocyclicExactPairDemandApplicability
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
      input.LocalizedRule3ExactPairEndpointDemand rule3FrameOf
        initial.left initial.right initial.leftCursor ∧
      input.LocalizedRule3ExactPairEndpointDemand rule3FrameOf
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

/-- Global pair totality recovers the exact-pair demand version of the required-monocycle
applicability. -/
theorem LocalizedRule3RequiredMonocyclicExactPairDemandApplicability.of_chemicalApplicability
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
    input.LocalizedRule3RequiredMonocyclicExactPairDemandApplicability
      target occurrence view rule3FrameOf initial closure := by
  rcases applicable with ⟨policyResult, routeComputed, required,
    leftApplicable, rightApplicable, spatial⟩
  exact ⟨policyResult, routeComputed, required,
    LocalizedRule3ExactPairEndpointDemand.of_chemicalApplicability input
      rule3FrameOf pairTotal initial.left initial.right initial.leftCursor leftApplicable,
    LocalizedRule3ExactPairEndpointDemand.of_chemicalApplicability input
      rule3FrameOf pairTotal initial.right initial.left initial.rightCursor rightApplicable,
    spatial⟩

/-- Independent required-monocycle applicability with exact-pair demands forces the complete
cyclic evaluator to succeed. -/
theorem exists_localizedRule3RequiredMonocyclicEZWith?_of_exactPairDemandApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (applicable : input.LocalizedRule3RequiredMonocyclicExactPairDemandApplicability
      target occurrence view rule3FrameOf initial closure) :
    ∃ result,
      input.localizedRule3RequiredMonocyclicEZWith?
        target occurrence view rule3FrameOf = some result := by
  rcases applicable with ⟨policyResult, routeComputed, required,
    leftDemand, rightDemand, spatial⟩
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_exactPairDemand
      target view rule3FrameOf initial.left initial.right
      initial.leftCursor leftDemand
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_exactPairDemand
      target view rule3FrameOf initial.right initial.left
      initial.rightCursor rightDemand
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

/-- Independent odd-cumulene source applicability with exact-pair demands. -/
def LocalizedRule3OddCumuleneGeometryExactPairDemandApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∃ topology,
    input.localizedRule3OddCumuleneEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology ∧
      input.LocalizedRule3ExactPairEndpointDemand rule3FrameOf
        topology.initial.left topology.initial.right topology.initial.leftCursor ∧
      input.LocalizedRule3ExactPairEndpointDemand rule3FrameOf
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

/-- Global pair totality recovers the exact-pair demand version of the odd-cumulene
applicability. -/
theorem LocalizedRule3OddCumuleneGeometryExactPairDemandApplicability.of_chemicalApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (pairTotal : input.LocalizedDescriptorBearingRule3PairFrameTotal rule3FrameOf)
    (applicable : input.LocalizedRule3OddCumuleneGeometryChemicalApplicability
      target occurrence view rule3FrameOf) :
    input.LocalizedRule3OddCumuleneGeometryExactPairDemandApplicability
      target occurrence view rule3FrameOf := by
  rcases applicable with ⟨topology, topologyComputed, leftApplicable, rightApplicable, spatial⟩
  exact ⟨topology, topologyComputed,
    LocalizedRule3ExactPairEndpointDemand.of_chemicalApplicability input
      rule3FrameOf pairTotal topology.initial.left topology.initial.right
      topology.initial.leftCursor leftApplicable,
    LocalizedRule3ExactPairEndpointDemand.of_chemicalApplicability input
      rule3FrameOf pairTotal topology.right topology.rightPartner
      topology.rightCursor rightApplicable,
    spatial⟩

/-- Independent odd-cumulene applicability with exact-pair demands forces its complete
descriptor-bearing spatial source evaluator to succeed. -/
theorem exists_localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_of_exactPairDemandApplicability
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (applicable : input.LocalizedRule3OddCumuleneGeometryExactPairDemandApplicability
      target occurrence view rule3FrameOf) :
    ∃ result,
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf = some result := by
  rcases applicable with ⟨topology, topologyComputed, leftDemand, rightDemand,
    spatial⟩
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_exactPairDemand
      target view rule3FrameOf topology.initial.left topology.initial.right
      topology.initial.leftCursor leftDemand
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_exactPairDemand
      target view rule3FrameOf topology.right topology.rightPartner
      topology.rightCursor rightDemand
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

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
