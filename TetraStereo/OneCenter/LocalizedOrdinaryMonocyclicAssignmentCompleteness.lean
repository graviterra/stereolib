import TetraStereo.OneCenter.LocalizedOrdinaryMonocyclicExactOnceCompleteness
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Assignment completeness for required ordinary-monocyclic E/Z units

This module removes executable endpoint-compilation success from the ordinary-monocycle
completeness boundary.  The retained premises are independent finite chemical applicability:
exactly two explicit substituents at each endpoint, their canonical occurrence realizations,
support for every reachable descriptor-bearing Rules-1a--5 dependency, and an independently
valid strict-priority/nondegenerate spatial assignment.
-/

/-- A complete axis recovered from the distinguished occurrence of a canonical physical bond
retains that bond's canonical two-direction initial frame. -/
theorem localizedRule3CumulatedEndpointCursorFrame?_canonicalDoubleBond_initial
    (input : CertifiedLocalizedCIPInput) (fuel traversalFuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (axis : input.LocalizedRule3CumulatedEndpointCursorFrame fuel)
    (computed : input.localizedRule3CumulatedEndpointCursorFrame? traversalFuel
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) = some axis) :
    axis.initial =
      input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame fuel bond := by
  let canonical :=
    input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame fuel bond
  unfold localizedRule3CumulatedEndpointCursorFrame? at computed
  cases entryComputed : input.localizedRule3CumulatedAxisEntry?
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond) with
  | none => simp [entryComputed] at computed
  | some entry =>
      cases entry with
      | internal initial previousAxis => simp [entryComputed] at computed
      | ringClosure initial closure => simp [entryComputed] at computed
      | branched initial first second rest => simp [entryComputed] at computed
      | terminalStart initial =>
          have initialIdentity : initial = canonical := by
            unfold localizedRule3CumulatedAxisEntry? at entryComputed
            rw [input.localizedRule3PhysicalEndpointCursorFrame?_canonicalDoubleBondFirstChild
              fuel bond] at entryComputed
            cases topologyComputed : input.localizedRule3AxisTopology? canonical.leftCursor with
            | none => simp [canonical, topologyComputed] at entryComputed
            | some topology =>
                cases topology <;> simp [canonical, topologyComputed] at entryComputed
                exact entryComputed.symm
          subst initial
          cases walkComputed : input.walkLocalizedRule3CumulatedAxis?
              traversalFuel canonical.rightCursor with
          | none => simp [entryComputed, walkComputed] at computed
          | some rightward =>
              generalize reversedIdentity :
                  rightward.reverse ++ [canonical.leftCursor] = reversed at computed
              cases reversed with
              | nil => simp [entryComputed, walkComputed, reversedIdentity] at computed
              | cons rightCursor rest =>
                  cases rest with
                  | nil => simp [entryComputed, walkComputed, reversedIdentity] at computed
                  | cons rightPartnerCursor reverseTail =>
                      cases rightPartnerComputed :
                          rightPartnerCursor.occurrence.1.node.current? with
                      | none =>
                          simp [entryComputed, walkComputed, reversedIdentity,
                            rightPartnerComputed] at computed
                      | some rightPartner =>
                          cases rightComputed : rightCursor.occurrence.1.node.current? with
                          | none =>
                              simp [entryComputed, walkComputed, reversedIdentity,
                                rightPartnerComputed, rightComputed] at computed
                          | some right =>
                              simp [entryComputed, walkComputed, reversedIdentity,
                                rightPartnerComputed, rightComputed] at computed
                              subst axis
                              rfl

/-- Every explicit substituent at the canonical lower endpoint has a unique physical reference
cursor in the exact cut neighborhood. -/
theorem exists_canonicalRule3ReferenceCursor_canonicalDoubleBondInitialLeft
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (reference : input.Atom)
    (referencePresent : reference ∈ input.localizedRule3ExplicitSubstituents
      bond.1.1 bond.1.2) :
    ∃ referenceCursor,
      input.CanonicalLocalizedRule3ReferenceCursor
        (input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame
          fuel bond).leftCursor referenceCursor reference := by
  let endpointCursor :=
    (input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame
      fuel bond).leftCursor
  have referenceFacts :=
    (input.mem_localizedRule3ExplicitSubstituents_iff
      bond.1.1 bond.1.2 reference).mp referencePresent
  apply input.exists_canonicalLocalizedRule3ReferenceCursor_of_real_outward
    endpointCursor bond.1.1 reference
  · rfl
  · rfl
  · simp [endpointCursor, localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame,
      localizedAtomRootOccurrence]
  · exact referenceFacts.1
  · simp [endpointCursor, localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame,
      localizedAtomRootOccurrence, OfficialCIPNode.parent?, OfficialCIPNode.root]
  · intro slot childAtSlot previous previousExact
    have previousIdentity : previous =
        input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond := by
      simpa [endpointCursor,
        localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame] using
          Option.some.inj previousExact.symm
    subst previous
    intro addressIdentity
    have slotIdentity : slot =
        input.localizedCanonicalDoubleBondFirstChildSlot bond := by
      simpa [endpointCursor,
        localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame] using
          addressIdentity
    have childAtRoot :
        ((OfficialCIPNode.root bond.1.1).extend reference 0,
            input.localizedCanonicalDoubleBondFirstChildSlot bond) ∈
          (input.executableOfficialCIPChildren
            (OfficialCIPNode.root bond.1.1)).zipIdx := by
      simpa [endpointCursor,
        localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame,
        slotIdentity] using childAtSlot
    have targetIndexed := List.mem_zipIdx childAtRoot
    have canonicalIndexed := List.mem_zipIdx
      (input.localizedCanonicalDoubleBondFirstChildSlot_mem bond)
    have childIdentity :
        (OfficialCIPNode.root bond.1.1).extend reference 0 =
          input.localizedCanonicalDoubleBondFirstChildNode bond :=
      targetIndexed.2.2.trans canonicalIndexed.2.2.symm
    have atomIdentity : reference = bond.1.2 := by
      have observed := congrArg OfficialCIPNode.current? childIdentity
      simpa [localizedCanonicalDoubleBondFirstChildNode] using observed
    exact referenceFacts.2 atomIdentity
  · exact Or.inl (by
      simp [endpointCursor,
        localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame,
        localizedAtomRootOccurrence])

/-- At positive carrier depth, every explicit substituent at the canonical upper endpoint also
has a unique physical reference cursor. -/
theorem exists_canonicalRule3ReferenceCursor_canonicalDoubleBondInitialRight
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (positive : 0 < fuel)
    (reference : input.Atom)
    (referencePresent : reference ∈ input.localizedRule3ExplicitSubstituents
      bond.1.2 bond.1.1) :
    ∃ referenceCursor,
      input.CanonicalLocalizedRule3ReferenceCursor
        (input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame
          fuel bond).rightCursor referenceCursor reference := by
  let endpointCursor :=
    (input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame
      fuel bond).rightCursor
  let previous := input.localizedAtomRootOccurrence fuel bond.1.1
  have physical := input.localizedCanonicalDoubleBondFirstChildOccurrence_physical fuel bond
  have referenceFacts :=
    (input.mem_localizedRule3ExplicitSubstituents_iff
      bond.1.2 bond.1.1 reference).mp referencePresent
  apply input.exists_canonicalLocalizedRule3ReferenceCursor_of_real_outward
    endpointCursor bond.1.2 reference
  · simpa [endpointCursor,
      localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame] using physical.1
  · simpa [endpointCursor,
      localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame] using physical.2.1
  · simpa [endpointCursor,
      localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame] using positive
  · exact referenceFacts.1
  · rw [show endpointCursor.occurrence.1.node.parent? = some bond.1.1 by
      simpa [endpointCursor,
        localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame] using physical.2.2.1]
    intro identity
    exact referenceFacts.2 (Option.some.inj identity).symm
  · intro slot _childAtSlot candidatePrevious candidatePreviousExact
    have candidateIdentity : candidatePrevious = previous := by
      simpa [endpointCursor, previous,
        localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame] using
          Option.some.inj candidatePreviousExact.symm
    subst candidatePrevious
    intro addressIdentity
    have lengths := congrArg List.length addressIdentity
    simp [endpointCursor, previous,
      localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame] at lengths
  · exact Or.inr ⟨previous,
      input.localizedCanonicalDoubleBondFirstChildSlot bond, by
        simp [endpointCursor, previous,
          localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame], by
        simp [endpointCursor, previous,
          localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame]⟩

/-- Independent finite conditions making one ordinary-double-bond endpoint total through the
production Rules-1a--5 compiler. -/
def LocalizedOrdinaryMonocyclicProductionEndpointResolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ first second firstCursor secondCursor,
    input.localizedRule3ExplicitSubstituents endpoint partner = [first, second] ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor firstCursor first ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor secondCursor second ∧
      input.LocalizedDescriptorBearingRule3ReachableSupportThrough target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)

/-- Two-cursor coupled ambiguity is impossible, so independent dependency support and canonical
physical references force the actual finite endpoint compiler to return a frame. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_ordinaryMonocyclic_resolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (resolved : input.LocalizedOrdinaryMonocyclicProductionEndpointResolved
      target view endpoint partner endpointCursor) :
    ∃ frame,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view
            (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
          endpoint partner endpointCursor = some frame := by
  rcases resolved with ⟨first, second, firstCursor, secondCursor,
    candidates, firstReference, secondReference, support⟩
  have nodesResolved :=
    LocalizedDescriptorBearingRule3ReachableSupportThrough.resolved
      input target view support
  have firstValid := firstReference.valid input endpointCursor firstCursor first
  have secondValid := secondReference.valid input endpointCursor secondCursor second
  obtain ⟨rule3Frame, rule3FrameComputed⟩ :=
    input.exists_buildLocalizedDescriptorBearingRule3Frame?_two_at_conservativeFuel
      target view nodesResolved firstCursor secondCursor firstValid secondValid
  have keyCount : rule3Frame.keys.length = 2 := by
    simpa using input.buildLocalizedDescriptorBearingRule3Frame?_keys_length_eq
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      [firstCursor, secondCursor] rule3Frame rule3FrameComputed
  exact input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_two_canonical_references
    target view
    (input.buildLocalizedDescriptorBearingRule3Frame? target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
    endpoint partner first second endpointCursor firstCursor secondCursor
    candidates firstReference secondReference
    ⟨rule3Frame, rule3FrameComputed, keyCount⟩

/-- Independent remaining stereogenicity evidence after both endpoint key frames have been
compiled.  Tied endpoints and missing or degenerate geometry correctly fail this predicate. -/
def LocalizedOrdinaryMonocyclicProductionSpatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
    (leftCompilation rightCompilation :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) : Prop :=
  ∃ unit cyclicGeometry descriptor,
    input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
      axis.initial.left axis.initial.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          axis.initial.leftCursor cursor reference ∧
        ((cursor = leftCompilation.firstCursor ∧
            key = leftCompilation.endpointFrame.firstKey) ∨
         (cursor = leftCompilation.secondCursor ∧
            key = leftCompilation.endpointFrame.secondKey)))
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          axis.initial.rightCursor cursor reference ∧
        ((cursor = rightCompilation.firstCursor ∧
            key = rightCompilation.endpointFrame.firstKey) ∨
         (cursor = rightCompilation.secondCursor ∧
            key = rightCompilation.endpointFrame.secondKey)))
      unit ∧
    Rule3GeometryRefinesMonocyclicSeniorLigandGeometry unit.geometry cyclicGeometry ∧
    BlueBookP93.Cyclic.RequiredMonocyclicEZAssignment
      policyResult.carrier.ring.card policyResult.doubleBondCount
      cyclicGeometry descriptor

/-- Chemical readiness for one canonical physical bond.  It does not assume that either endpoint
compiler or the final descriptor evaluator succeeds.  The two computation equalities occur only
as antecedents selecting the frames whose independent spatial meaning must be provided. -/
def LocalizedOrdinaryMonocyclicProductionReadinessWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond) : Prop :=
  let target := input.localizedAtomRootOccurrence fuel bond.1.1
  let occurrence := input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  ∃ (axis : input.LocalizedRule3CumulatedEndpointCursorFrame fuel)
      (_ordinary : axis.doubleBondCount = 1)
      (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult),
    input.localizedRule3CumulatedEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel fuel) occurrence = some axis ∧
      input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
        axis.initial.left axis.initial.right policyResult ∧
      policyResult.policy = .requireEZ ∧
      input.LocalizedOrdinaryMonocyclicProductionEndpointResolved
        target view axis.initial.left axis.initial.right axis.initial.leftCursor ∧
      input.LocalizedOrdinaryMonocyclicProductionEndpointResolved
        target view axis.initial.right axis.initial.left axis.initial.rightCursor ∧
      ∀ leftCompilation rightCompilation,
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view frameOf axis.initial.left axis.initial.right
              axis.initial.leftCursor = some leftCompilation →
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view frameOf axis.initial.right axis.initial.left
              axis.initial.rightCursor = some rightCompilation →
        input.LocalizedOrdinaryMonocyclicProductionSpatialEvidence
          axis policyResult leftCompilation rightCompilation

/-- Chemical applicability with all occurrence-cursor existence obligations removed.  Canonical
bond embedding supplies those cursors internally; callers provide only positive carrier depth,
the exact two physical substituents at each endpoint, reachable dependency support, the exact
monocycle policy, and strict nondegenerate spatial evidence. -/
def LocalizedOrdinaryMonocyclicProductionDependencyEvidenceWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond) : Prop :=
  let target := input.localizedAtomRootOccurrence fuel bond.1.1
  let occurrence := input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  0 < fuel ∧
    ∃ (axis : input.LocalizedRule3CumulatedEndpointCursorFrame fuel)
        (_ordinary : axis.doubleBondCount = 1)
        (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
        (leftFirst leftSecond rightFirst rightSecond : input.Atom),
      input.localizedRule3CumulatedEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel fuel) occurrence = some axis ∧
        input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
          axis.initial.left axis.initial.right policyResult ∧
        policyResult.policy = .requireEZ ∧
        input.localizedRule3ExplicitSubstituents bond.1.1 bond.1.2 =
          [leftFirst, leftSecond] ∧
        input.localizedRule3ExplicitSubstituents bond.1.2 bond.1.1 =
          [rightFirst, rightSecond] ∧
        input.LocalizedDescriptorBearingRule3ReachableSupportThrough target view
          (localizedDescriptorBearingRule3EvaluationFuel fuel) ∧
        ∀ leftCompilation rightCompilation,
          input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view frameOf axis.initial.left axis.initial.right
                axis.initial.leftCursor = some leftCompilation →
          input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view frameOf axis.initial.right axis.initial.left
                axis.initial.rightCursor = some rightCompilation →
          input.LocalizedOrdinaryMonocyclicProductionSpatialEvidence
            axis policyResult leftCompilation rightCompilation

/-- Canonical physical-bond embedding turns the cursor-free dependency evidence into full local
production readiness. -/
theorem localizedOrdinaryMonocyclicProductionReadiness_of_dependencyEvidence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond)
    (evidence : input.LocalizedOrdinaryMonocyclicProductionDependencyEvidenceWithState
      fuel state bond) :
    input.LocalizedOrdinaryMonocyclicProductionReadinessWithState fuel state bond := by
  dsimp [LocalizedOrdinaryMonocyclicProductionDependencyEvidenceWithState] at evidence
  rcases evidence with ⟨positive, axis, ordinary, policyResult,
    leftFirst, leftSecond, rightFirst, rightSecond,
    axisComputed, policyDerived, required, leftCandidates, rightCandidates,
    support, spatialEvidence⟩
  let target := input.localizedAtomRootOccurrence fuel bond.1.1
  let view := input.localizedDependencyView state target
  let canonical :=
    input.localizedCanonicalDoubleBondInitialPhysicalEndpointCursorFrame fuel bond
  have initialIdentity : axis.initial = canonical :=
    input.localizedRule3CumulatedEndpointCursorFrame?_canonicalDoubleBond_initial
      fuel (input.localizedRule3CumulatedTraversalFuel fuel) bond axis axisComputed
  have leftFirstPresent : leftFirst ∈
      input.localizedRule3ExplicitSubstituents bond.1.1 bond.1.2 := by
    simp [leftCandidates]
  have leftSecondPresent : leftSecond ∈
      input.localizedRule3ExplicitSubstituents bond.1.1 bond.1.2 := by
    simp [leftCandidates]
  have rightFirstPresent : rightFirst ∈
      input.localizedRule3ExplicitSubstituents bond.1.2 bond.1.1 := by
    simp [rightCandidates]
  have rightSecondPresent : rightSecond ∈
      input.localizedRule3ExplicitSubstituents bond.1.2 bond.1.1 := by
    simp [rightCandidates]
  obtain ⟨leftFirstCursor, leftFirstReference⟩ :=
    input.exists_canonicalRule3ReferenceCursor_canonicalDoubleBondInitialLeft
      fuel bond leftFirst leftFirstPresent
  obtain ⟨leftSecondCursor, leftSecondReference⟩ :=
    input.exists_canonicalRule3ReferenceCursor_canonicalDoubleBondInitialLeft
      fuel bond leftSecond leftSecondPresent
  obtain ⟨rightFirstCursor, rightFirstReference⟩ :=
    input.exists_canonicalRule3ReferenceCursor_canonicalDoubleBondInitialRight
      fuel bond positive rightFirst rightFirstPresent
  obtain ⟨rightSecondCursor, rightSecondReference⟩ :=
    input.exists_canonicalRule3ReferenceCursor_canonicalDoubleBondInitialRight
      fuel bond positive rightSecond rightSecondPresent
  have leftResolvedCanonical :
      input.LocalizedOrdinaryMonocyclicProductionEndpointResolved
        target view canonical.left canonical.right canonical.leftCursor :=
    ⟨leftFirst, leftSecond, leftFirstCursor, leftSecondCursor,
      leftCandidates, leftFirstReference, leftSecondReference, support⟩
  have rightResolvedCanonical :
      input.LocalizedOrdinaryMonocyclicProductionEndpointResolved
        target view canonical.right canonical.left canonical.rightCursor :=
    ⟨rightFirst, rightSecond, rightFirstCursor, rightSecondCursor,
      rightCandidates, rightFirstReference, rightSecondReference, support⟩
  dsimp [LocalizedOrdinaryMonocyclicProductionReadinessWithState]
  refine ⟨axis, ordinary, policyResult, axisComputed, policyDerived, required, ?_, ?_, ?_⟩
  · simpa [initialIdentity] using leftResolvedCanonical
  · simpa [initialIdentity] using rightResolvedCanonical
  · exact spatialEvidence

/-- Independent chemical readiness forces the local production evaluator to emit a complete,
independently conforming ordinary-monocyclic E/Z result. -/
theorem exists_localizedRule3OrdinaryMonocyclicEZWith?_of_productionReadiness
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond)
    (readiness : input.LocalizedOrdinaryMonocyclicProductionReadinessWithState
      fuel state bond) :
    ∃ result,
      input.localizedRule3OrdinaryMonocyclicEZWith?
          (input.localizedAtomRootOccurrence fuel bond.1.1)
          (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond)
          (input.localizedDependencyView state
            (input.localizedAtomRootOccurrence fuel bond.1.1))
          (input.buildLocalizedDescriptorBearingRule3Frame?
            (input.localizedAtomRootOccurrence fuel bond.1.1)
            (input.localizedDependencyView state
              (input.localizedAtomRootOccurrence fuel bond.1.1))
            (localizedDescriptorBearingRule3EvaluationFuel fuel)) = some result ∧
        input.DeclarativeLocalizedRule3OrdinaryMonocyclicEZWith
          (input.localizedAtomRootOccurrence fuel bond.1.1)
          (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond)
          (input.localizedDependencyView state
            (input.localizedAtomRootOccurrence fuel bond.1.1))
          (input.DeclarativeLocalizedDescriptorBearingRule3Frame
            (input.localizedAtomRootOccurrence fuel bond.1.1)
            (input.localizedDependencyView state
              (input.localizedAtomRootOccurrence fuel bond.1.1))
            (localizedDescriptorBearingRule3EvaluationFuel fuel)) result := by
  dsimp [LocalizedOrdinaryMonocyclicProductionReadinessWithState] at readiness
  rcases readiness with ⟨axis, ordinary, policyResult, axisComputed, policyDerived,
    required, leftResolved, rightResolved, spatialEvidence⟩
  let target := input.localizedAtomRootOccurrence fuel bond.1.1
  let occurrence := input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  have routeComputed : input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence? occurrence =
      some { axis, ordinary, policyResult } :=
    (input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?_canonical_eq_some_iff
      fuel bond axis ordinary axisComputed policyResult).mpr policyDerived
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_ordinaryMonocyclic_resolved
      target view axis.initial.left axis.initial.right axis.initial.leftCursor leftResolved
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_ordinaryMonocyclic_resolved
      target view axis.initial.right axis.initial.left axis.initial.rightCursor rightResolved
  obtain ⟨unit, cyclicGeometry, descriptor, spatial, geometry, assignment⟩ :=
    spatialEvidence leftCompilation rightCompilation leftComputed rightComputed
  let result : input.LocalizedRule3OrdinaryMonocyclicEZResult fuel :=
    { axis, ordinary, policyResult, leftCompilation, rightCompilation, unit, descriptor }
  have computed : input.localizedRule3OrdinaryMonocyclicEZWith?
      target occurrence view frameOf = some result :=
    (input.localizedRule3OrdinaryMonocyclicEZWith?_eq_some_iff_of_required_compilations
      target occurrence view frameOf
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
        (localizedDescriptorBearingRule3EvaluationFuel fuel))
      (fun cursors frame frameComputed =>
        input.buildLocalizedDescriptorBearingRule3Frame?_sound target view
          (localizedDescriptorBearingRule3EvaluationFuel fuel)
          cursors frame frameComputed)
      axis ordinary policyResult leftCompilation rightCompilation routeComputed required
      leftComputed rightComputed unit descriptor).mpr
        ⟨spatial, cyclicGeometry, geometry, assignment⟩
  refine ⟨result, ?_, ?_⟩
  · simpa [target, occurrence, view, frameOf] using computed
  · exact input.localizedRule3OrdinaryMonocyclicEZWith?_sound
      target occurrence view frameOf
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view
        (localizedDescriptorBearingRule3EvaluationFuel fuel))
      (fun cursors frame frameComputed =>
        input.buildLocalizedDescriptorBearingRule3Frame?_sound target view
          (localizedDescriptorBearingRule3EvaluationFuel fuel)
          cursors frame frameComputed)
      result computed

/-- The public per-bond wrapper is total under the same independent readiness predicate. -/
theorem exists_localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_of_readiness
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (bond : input.LocalizedCanonicalDoubleBond)
    (readiness : input.LocalizedOrdinaryMonocyclicProductionReadinessWithState
      fuel state bond) :
    ∃ assignment,
      input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?
          fuel state bond = some assignment ∧
        input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState
          fuel state assignment := by
  obtain ⟨result, resultComputed, resultDerived⟩ :=
    input.exists_localizedRule3OrdinaryMonocyclicEZWith?_of_productionReadiness
      fuel state bond readiness
  let assignment : input.LocalizedOrdinaryMonocyclicEZSpatialAssignment fuel :=
    { bond, result }
  refine ⟨assignment, ?_, ?_⟩
  · simp [localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?, resultComputed,
      assignment]
  · simpa [DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignmentWithState,
      assignment] using resultDerived

/-- Under the scheduled Rules-1a--5 state, every ready required ordinary-monocyclic bond is
present in the public family list and its physical bond occurs literally once. -/
theorem every_ready_localizedOrdinaryMonocyclicEZ_occurs_exactly_once
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (readiness : input.LocalizedOrdinaryMonocyclicProductionReadinessWithState fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) bond) :
    ∃ assignment,
      assignment.bond = bond ∧
        assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZ fuel ∧
        input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignment
          fuel assignment ∧
        List.count bond
          ((input.analyzeLocalizedOrdinaryMonocyclicEZ fuel).map
            LocalizedOrdinaryMonocyclicEZSpatialAssignment.bond) = 1 := by
  obtain ⟨assignment, computed, derived⟩ :=
    input.exists_localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_of_readiness
      fuel (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
      bond readiness
  have present : assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZ fuel :=
    (input.mem_analyzeLocalizedOrdinaryMonocyclicEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) assignment).mpr
      (by
        have retained :=
          input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond
            fuel (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
            bond assignment computed
        simpa [analyzeLocalizedOrdinaryMonocyclicEZ, retained] using computed)
  have retained := input.localizedOrdinaryMonocyclicEZSpatialAssignmentAtWithState?_bond
    fuel (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
    bond assignment computed
  exact ⟨assignment, retained, present, derived,
    input.localizedOrdinaryMonocyclicEZ_success_bond_count_eq_one
      fuel bond assignment computed⟩

/-- Strong cursor-free form: genuine finite chemical dependency and spatial evidence alone force
one independently correct public assignment with literal multiplicity one. -/
theorem every_dependencyResolved_localizedOrdinaryMonocyclicEZ_occurs_exactly_once
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (evidence : input.LocalizedOrdinaryMonocyclicProductionDependencyEvidenceWithState fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) bond) :
    ∃ assignment,
      assignment.bond = bond ∧
        assignment ∈ input.analyzeLocalizedOrdinaryMonocyclicEZ fuel ∧
        input.DeclarativeLocalizedOrdinaryMonocyclicEZSpatialAssignment
          fuel assignment ∧
        List.count bond
          ((input.analyzeLocalizedOrdinaryMonocyclicEZ fuel).map
            LocalizedOrdinaryMonocyclicEZSpatialAssignment.bond) = 1 := by
  exact input.every_ready_localizedOrdinaryMonocyclicEZ_occurs_exactly_once
    fuel bond
      (input.localizedOrdinaryMonocyclicProductionReadiness_of_dependencyEvidence
        fuel (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)
        bond evidence)

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
