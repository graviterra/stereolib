import TetraStereo.OneCenter.LocalizedCyclicDoubleBondAuthorityRoute
import TetraStereo.OneCenter.LocalizedRule3CumulatedDescriptor
import TetraStereo.OneCenter.LocalizedRule3ParameterizedEndpoint

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Descriptor-bearing ordinary monocyclic double bonds

This module continues the exact P-93.5.1.4.1 authority route through the existing occurrence-local
Rules-1a--5 endpoint compiler and exact rational Rule-3 geometry.  It emits `E/Z` only for the
ordinary-monocycle branch whose independently proved policy requires a descriptor.  Permanent
omission, policy gaps, polycyclic systems, fully cyclic cumulenes, tied endpoints, and absent or
degenerate geometry all remain non-emitting outcomes.
-/

/-- Production Rule-3 geometry refines the independent cyclic senior-ligand relation. -/
def Rule3GeometryRefinesMonocyclicSeniorLigandGeometry
    (geometry : OfficialRule3Geometry)
    (cyclicGeometry : BlueBookP93.Cyclic.MonocyclicSeniorLigandGeometry) : Prop :=
  match geometry, cyclicGeometry with
  | .seqcis, .together | .seqtrans, .opposite => True
  | _, _ => False

/-- Convert only stereogenic Rule-3 geometry to the independent cyclic geometry domain. -/
def monocyclicSeniorLigandGeometryOfRule3? :
    OfficialRule3Geometry →
      Option BlueBookP93.Cyclic.MonocyclicSeniorLigandGeometry
  | .seqcis => some .together
  | .seqtrans => some .opposite
  | .nonstereogenic => none

theorem monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff
    (geometry : OfficialRule3Geometry)
    (cyclicGeometry : BlueBookP93.Cyclic.MonocyclicSeniorLigandGeometry) :
    monocyclicSeniorLigandGeometryOfRule3? geometry = some cyclicGeometry ↔
      Rule3GeometryRefinesMonocyclicSeniorLigandGeometry geometry cyclicGeometry := by
  cases geometry <;> cases cyclicGeometry <;>
    simp [monocyclicSeniorLigandGeometryOfRule3?,
      Rule3GeometryRefinesMonocyclicSeniorLigandGeometry]

/-- Pure exact-spatial cyclic descriptor evaluator after the ring policy inputs are known. -/
def requiredMonocyclicEZDescriptorOfSpatialReferences?
    (ringSize doubleBondCount : Nat)
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    Option BlueBookP93.Acyclic.Descriptor := do
  let geometry ← rule3GeometryOfSpatialReferences?
    leftEndpoint rightEndpoint leftReference rightReference
  let cyclicGeometry ← monocyclicSeniorLigandGeometryOfRule3? geometry
  BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
    ringSize doubleBondCount cyclicGeometry

/-- The pure cyclic descriptor succeeds exactly for exact rational Rule-3 geometry followed by
the independent required-monocycle assignment. -/
theorem requiredMonocyclicEZDescriptorOfSpatialReferences?_eq_some_iff
    (ringSize doubleBondCount : Nat)
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3)
    (descriptor : BlueBookP93.Acyclic.Descriptor) :
    requiredMonocyclicEZDescriptorOfSpatialReferences? ringSize doubleBondCount
        leftEndpoint rightEndpoint leftReference rightReference = some descriptor ↔
      ∃ geometry cyclicGeometry,
        RationalRule3SpatialGeometry leftEndpoint rightEndpoint
          leftReference rightReference geometry ∧
        Rule3GeometryRefinesMonocyclicSeniorLigandGeometry geometry cyclicGeometry ∧
        BlueBookP93.Cyclic.RequiredMonocyclicEZAssignment
          ringSize doubleBondCount cyclicGeometry descriptor := by
  constructor
  · intro computed
    unfold requiredMonocyclicEZDescriptorOfSpatialReferences? at computed
    cases geometryComputed : rule3GeometryOfSpatialReferences?
        leftEndpoint rightEndpoint leftReference rightReference with
    | none => simp [geometryComputed] at computed
    | some geometry =>
        cases cyclicComputed : monocyclicSeniorLigandGeometryOfRule3? geometry with
        | none => simp [geometryComputed, cyclicComputed] at computed
        | some cyclicGeometry =>
            exact ⟨geometry, cyclicGeometry,
              (rule3GeometryOfSpatialReferences?_eq_some_iff
                leftEndpoint rightEndpoint leftReference rightReference geometry).mp
                  geometryComputed,
              (monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff
                geometry cyclicGeometry).mp cyclicComputed,
              (BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?_eq_some_iff
                ringSize doubleBondCount cyclicGeometry descriptor).mp
                  (by simpa [geometryComputed, cyclicComputed] using computed)⟩
  · rintro ⟨geometry, cyclicGeometry, spatial, geometryRefines, assignment⟩
    have geometryComputed :=
      (rule3GeometryOfSpatialReferences?_eq_some_iff
        leftEndpoint rightEndpoint leftReference rightReference geometry).mpr spatial
    have cyclicComputed :=
      (monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff
        geometry cyclicGeometry).mpr geometryRefines
    have descriptorComputed :=
      (BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?_eq_some_iff
        ringSize doubleBondCount cyclicGeometry descriptor).mpr assignment
    simp [requiredMonocyclicEZDescriptorOfSpatialReferences?, geometryComputed,
      cyclicComputed, descriptorComputed]

/-- The final pure cyclic `E/Z` value is invariant under reversal of the physical double bond
and simultaneous exchange of its selected senior references. -/
theorem requiredMonocyclicEZDescriptorOfSpatialReferences?_swap
    (ringSize doubleBondCount : Nat)
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    requiredMonocyclicEZDescriptorOfSpatialReferences? ringSize doubleBondCount
        rightEndpoint leftEndpoint rightReference leftReference =
      requiredMonocyclicEZDescriptorOfSpatialReferences? ringSize doubleBondCount
        leftEndpoint rightEndpoint leftReference rightReference := by
  unfold requiredMonocyclicEZDescriptorOfSpatialReferences?
  rw [rule3GeometryOfSpatialReferences?_swap]

namespace CertifiedLocalizedCIPInput

/-! ## Direct ordinary-monocycle route

An ordinary cycloalkene does not close by following only consecutive double bonds.  Therefore the
P-93.5.1.4.1 policy must be selected directly from each physical order-two occurrence and the
whole covalent component, before the separate cumulene-chain topology classifier is consulted.
-/

/-- Exact physical endpoint frame together with the whole-molecule ordinary-monocycle policy. -/
structure LocalizedRule3OrdinaryMonocyclicPolicyAtOccurrenceResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel
  ordinary : axis.doubleBondCount = 1
  policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult

def LocalizedRule3OrdinaryMonocyclicPolicyAtOccurrenceResult.initial
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3OrdinaryMonocyclicPolicyAtOccurrenceResult carrierFuel) :
    input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel :=
  result.axis.initial

/-- Perceive P-93 ordinary-monocycle applicability directly at any physical double-bond
occurrence. Fully cyclic cumulenes and nonmonocyclic systems return `none`. -/
noncomputable def localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3OrdinaryMonocyclicPolicyAtOccurrenceResult carrierFuel) := do
  let axis ← input.localizedRule3CumulatedEndpointCursorFrame?
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence
  if ordinary : axis.doubleBondCount = 1 then
    let policyResult ←
      input.localizedMonocyclicDoubleBondPolicyAt? axis.initial.left axis.initial.right
    some { axis, ordinary, policyResult }
  else none

/-- Independent meaning of the direct occurrence-to-monocycle policy route. -/
def DeclarativeLocalizedRule3OrdinaryMonocyclicPolicyAtOccurrence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (result : input.LocalizedRule3OrdinaryMonocyclicPolicyAtOccurrenceResult carrierFuel) :
    Prop :=
  input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence result.axis ∧
    result.axis.doubleBondCount = 1 ∧
    input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
      result.initial.left result.initial.right result.policyResult

/-- Every directly returned ordinary-monocycle policy has exact physical-edge and whole-molecule
monocycle meaning. -/
theorem localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (result : input.LocalizedRule3OrdinaryMonocyclicPolicyAtOccurrenceResult carrierFuel) :
    input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence? occurrence = some result →
      input.DeclarativeLocalizedRule3OrdinaryMonocyclicPolicyAtOccurrence occurrence result := by
  intro computed
  unfold localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?
    at computed
  cases axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [axisComputed] at computed
  | some axis =>
      by_cases ordinary : axis.doubleBondCount = 1
      · cases policyComputed : input.localizedMonocyclicDoubleBondPolicyAt?
            axis.initial.left axis.initial.right with
        | none => simp [axisComputed, ordinary, policyComputed] at computed
        | some policyResult =>
            simp [axisComputed, ordinary, policyComputed] at computed
            subst result
            exact ⟨
              input.localizedRule3CumulatedEndpointCursorFrame?_sound
                (input.localizedRule3CumulatedTraversalFuel carrierFuel)
                occurrence axis axisComputed,
              ordinary,
              (input.localizedMonocyclicDoubleBondPolicyAt?_eq_some_iff
                axis.initial.left axis.initial.right policyResult).mp policyComputed⟩
      · simp [axisComputed, ordinary] at computed

/-- For a canonical physical-double-bond occurrence already proved to be an isolated, complete
one-bond axis, direct routing succeeds with a particular policy certificate exactly when the
independent whole-molecule monocycle policy derives that certificate. -/
theorem localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?_canonical_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond)
    (axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (ordinary : axis.doubleBondCount = 1)
    (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel)
      (input.localizedCanonicalDoubleBondFirstChildOccurrence carrierFuel bond) = some axis)
    (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult) :
    input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?
        (input.localizedCanonicalDoubleBondFirstChildOccurrence carrierFuel bond) =
      some
        { axis
          ordinary
          policyResult } ↔
      input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
        axis.initial.left axis.initial.right policyResult := by
  unfold localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?
  constructor
  · intro computed
    cases policyComputed : input.localizedMonocyclicDoubleBondPolicyAt?
        axis.initial.left axis.initial.right with
    | none => simp [axisComputed, ordinary, policyComputed] at computed
    | some actual =>
        simp [axisComputed, ordinary, policyComputed] at computed
        subst actual
        exact (input.localizedMonocyclicDoubleBondPolicyAt?_eq_some_iff
          axis.initial.left axis.initial.right policyResult).mp policyComputed
  · intro derived
    have policyComputed :=
      (input.localizedMonocyclicDoubleBondPolicyAt?_eq_some_iff
        axis.initial.left axis.initial.right policyResult).mpr derived
    simp [axisComputed, ordinary, policyComputed]

/-- Any physical double bond whose maximal nonbranching cumulative frame has more than one bond is
excluded from the ordinary per-bond monocycle route.  It remains available to the even/odd
cumulene analyzers required by P-93.4.2.2--3 and P-93.5.2.3. -/
theorem localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?_eq_none_of_cumulated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis)
    (cumulated : axis.doubleBondCount ≠ 1) :
    input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence? occurrence = none := by
  simp [localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?, axisComputed, cumulated]

/-- If the occurrence is not the terminal start of a complete nonbranching cumulative frame, it
cannot enter the ordinary per-bond monocycle route. -/
theorem localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?_eq_none_of_no_axis
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (axisComputed : input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = none) :
    input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence? occurrence = none := by
  simp [localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?, axisComputed]

/-- Complete descriptor-bearing result for a directly perceived ordinary monocyclic `E/Z` unit. -/
structure LocalizedRule3OrdinaryMonocyclicEZResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel
  ordinary : axis.doubleBondCount = 1
  policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult
  leftCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult
  descriptor : BlueBookP93.Acyclic.Descriptor

def LocalizedRule3OrdinaryMonocyclicEZResult.initial
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3OrdinaryMonocyclicEZResult carrierFuel) :
    input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel :=
  result.axis.initial

/-- Compile a required ordinary-monocycle descriptor from a physical double-bond occurrence only
after it has been proved to be a complete isolated one-bond cumulative frame. -/
noncomputable def localizedRule3OrdinaryMonocyclicEZWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OrdinaryMonocyclicEZResult carrierFuel) := do
  let routed ← input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence? occurrence
  match routed.policyResult.policy with
  | .permanentlyOmit => none
  | .requireEZ => do
      let leftCompilation ←
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf routed.initial.left routed.initial.right
            routed.initial.leftCursor
      let rightCompilation ←
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf routed.initial.right routed.initial.left
            routed.initial.rightCursor
      let unit ← input.localizedRule3DescriptorBearingSpatialUnit?
        routed.initial.left routed.initial.right leftCompilation.endpointFrame
          rightCompilation.endpointFrame
      let cyclicGeometry ← monocyclicSeniorLigandGeometryOfRule3? unit.geometry
      let descriptor ← BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
        routed.policyResult.carrier.ring.card routed.policyResult.doubleBondCount
          cyclicGeometry
      some
        { axis := routed.axis
          ordinary := routed.ordinary
          policyResult := routed.policyResult
          leftCompilation
          rightCompilation
          unit
          descriptor }

/-- Project the direct cyclic assignment to the identity-aware Rule-3 scheduler observation. -/
def localizedRule3OrdinaryMonocyclicEZObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3OrdinaryMonocyclicEZResult carrierFuel) :
    input.LocalizedRule3SpatialNodeResult :=
  let leftReference := match result.unit.leftPriority with
    | .senior reference => reference
    | .nonstereogenic => result.leftCompilation.endpointFrame.first
  let rightReference := match result.unit.rightPriority with
    | .senior reference => reference
    | .nonstereogenic => result.rightCompilation.endpointFrame.first
  { left := result.initial.left
    right := result.initial.right
    unit := { leftReference, rightReference, geometry := result.unit.geometry } }

/-- Independent topology, endpoint priority, exact spatial, and final P-93 meaning of a directly
perceived ordinary-monocycle result. -/
def DeclarativeLocalizedRule3OrdinaryMonocyclicEZWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3OrdinaryMonocyclicEZResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence result.axis ∧
    result.axis.doubleBondCount = 1 ∧
    input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
      result.initial.left result.initial.right result.policyResult ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.initial.left result.initial.right
      result.initial.leftCursor result.leftCompilation ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.initial.right result.initial.left
      result.initial.rightCursor result.rightCompilation ∧
    input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
      result.initial.left result.initial.right
      result.leftCompilation.endpointFrame result.rightCompilation.endpointFrame
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          result.initial.leftCursor cursor reference ∧
        ((cursor = result.leftCompilation.firstCursor ∧
            key = result.leftCompilation.endpointFrame.firstKey) ∨
         (cursor = result.leftCompilation.secondCursor ∧
            key = result.leftCompilation.endpointFrame.secondKey)))
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          result.initial.rightCursor cursor reference ∧
        ((cursor = result.rightCompilation.firstCursor ∧
            key = result.rightCompilation.endpointFrame.firstKey) ∨
         (cursor = result.rightCompilation.secondCursor ∧
            key = result.rightCompilation.endpointFrame.secondKey)))
      result.unit ∧
    ∃ cyclicGeometry,
      Rule3GeometryRefinesMonocyclicSeniorLigandGeometry
        result.unit.geometry cyclicGeometry ∧
      BlueBookP93.Cyclic.RequiredMonocyclicEZAssignment
        result.policyResult.carrier.ring.card result.policyResult.doubleBondCount
        cyclicGeometry result.descriptor

/-- Every descriptor returned by the direct ordinary-monocycle path conforms to the independent
whole-molecule topology, Rules-1a--5 endpoint priorities, rational geometry, and P-93 assignment. -/
theorem localizedRule3OrdinaryMonocyclicEZWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedRule3OrdinaryMonocyclicEZResult carrierFuel)
    (computed : input.localizedRule3OrdinaryMonocyclicEZWith?
      target occurrence view rule3FrameOf = some result) :
    input.DeclarativeLocalizedRule3OrdinaryMonocyclicEZWith
      target occurrence view Rule3FrameMeaning result := by
  unfold localizedRule3OrdinaryMonocyclicEZWith? at computed
  cases routedComputed : input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?
      occurrence with
  | none => simp [routedComputed] at computed
  | some routed =>
      cases policyIdentity : routed.policyResult.policy with
      | permanentlyOmit => simp [routedComputed, policyIdentity] at computed
      | requireEZ =>
          cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf routed.initial.left routed.initial.right
                routed.initial.leftCursor with
          | none => simp [routedComputed, policyIdentity, leftComputed] at computed
          | some leftCompilation =>
              cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                  target view rule3FrameOf routed.initial.right routed.initial.left
                    routed.initial.rightCursor with
              | none =>
                  simp [routedComputed, policyIdentity, leftComputed, rightComputed] at computed
              | some rightCompilation =>
                  cases unitComputed : input.localizedRule3DescriptorBearingSpatialUnit?
                      routed.initial.left routed.initial.right
                        leftCompilation.endpointFrame rightCompilation.endpointFrame with
                  | none =>
                      simp [routedComputed, policyIdentity, leftComputed, rightComputed,
                        unitComputed] at computed
                  | some unit =>
                      cases geometryComputed :
                          monocyclicSeniorLigandGeometryOfRule3? unit.geometry with
                      | none =>
                          simp [routedComputed, policyIdentity, leftComputed, rightComputed,
                            unitComputed, geometryComputed] at computed
                      | some cyclicGeometry =>
                          cases descriptorComputed :
                              BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
                                routed.policyResult.carrier.ring.card
                                  routed.policyResult.doubleBondCount cyclicGeometry with
                          | none =>
                              simp [routedComputed, policyIdentity, leftComputed, rightComputed,
                                unitComputed, geometryComputed, descriptorComputed] at computed
                          | some descriptor =>
                              simp [routedComputed, policyIdentity, leftComputed, rightComputed,
                                unitComputed, geometryComputed, descriptorComputed] at computed
                              subst result
                              have routedDerived :=
                                input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence?_sound
                                  occurrence routed routedComputed
                              have leftDerived :=
                                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                                  target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                                  routed.initial.left routed.initial.right
                                  routed.initial.leftCursor leftCompilation leftComputed
                              have rightDerived :=
                                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                                  target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                                  routed.initial.right routed.initial.left
                                  routed.initial.rightCursor rightCompilation rightComputed
                              exact ⟨routedDerived.1, routedDerived.2.1,
                                routedDerived.2.2, leftDerived, rightDerived,
                                input.localizedRule3DescriptorBearingSpatialUnit?_sound
                                  routed.initial.left routed.initial.right
                                  leftCompilation.endpointFrame rightCompilation.endpointFrame _ _
                                  (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
                                    input target view Rule3FrameMeaning routed.initial.left
                                    routed.initial.right routed.initial.leftCursor leftCompilation
                                    leftDerived)
                                  (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
                                    input target view Rule3FrameMeaning routed.initial.right
                                    routed.initial.left routed.initial.rightCursor rightCompilation
                                    rightDerived)
                                  unit unitComputed,
                                ⟨cyclicGeometry,
                                  (monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff
                                    unit.geometry cyclicGeometry).mp geometryComputed,
                                  (BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?_eq_some_iff
                                    routed.policyResult.carrier.ring.card
                                    routed.policyResult.doubleBondCount cyclicGeometry
                                    descriptor).mp descriptorComputed⟩⟩

/-- Once the direct whole-molecule policy route and both endpoint compilations are fixed,
production success is equivalent in both directions to the independent exact spatial unit and
P-93 cyclic assignment relations. -/
theorem localizedRule3OrdinaryMonocyclicEZWith?_eq_some_iff_of_required_compilations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (ordinary : axis.doubleBondCount = 1)
    (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
    (leftCompilation rightCompilation :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (routeComputed : input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence? occurrence =
      some { axis, ordinary, policyResult })
    (required : policyResult.policy = .requireEZ)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf axis.initial.left axis.initial.right
        axis.initial.leftCursor =
        some leftCompilation)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf axis.initial.right axis.initial.left
        axis.initial.rightCursor =
        some rightCompilation)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (descriptor : BlueBookP93.Acyclic.Descriptor) :
    input.localizedRule3OrdinaryMonocyclicEZWith?
        target occurrence view rule3FrameOf =
      some
        { axis
          ordinary
          policyResult
          leftCompilation
          rightCompilation
          unit
          descriptor } ↔
      input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
          axis.initial.left axis.initial.right leftCompilation.endpointFrame
          rightCompilation.endpointFrame
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
        ∃ cyclicGeometry,
          Rule3GeometryRefinesMonocyclicSeniorLigandGeometry
            unit.geometry cyclicGeometry ∧
          BlueBookP93.Cyclic.RequiredMonocyclicEZAssignment
            policyResult.carrier.ring.card policyResult.doubleBondCount
            cyclicGeometry descriptor := by
  have leftDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
      axis.initial.left axis.initial.right axis.initial.leftCursor
      leftCompilation leftComputed
  have rightDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
      axis.initial.right axis.initial.left axis.initial.rightCursor
      rightCompilation rightComputed
  have leftValid :=
    DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
      input target view Rule3FrameMeaning axis.initial.left axis.initial.right
      axis.initial.leftCursor leftCompilation leftDerived
  have rightValid :=
    DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
      input target view Rule3FrameMeaning axis.initial.right axis.initial.left
      axis.initial.rightCursor rightCompilation rightDerived
  constructor
  · intro computed
    have derived := input.localizedRule3OrdinaryMonocyclicEZWith?_sound
      target occurrence view rule3FrameOf Rule3FrameMeaning rule3FrameSound _ computed
    rcases derived with
      ⟨_axis, _ordinary, _policy, _left, _right, spatial, assignment⟩
    exact ⟨spatial, assignment⟩
  · rintro ⟨spatial, cyclicGeometry, geometryRefines, assignment⟩
    have unitComputed :=
      (input.localizedRule3DescriptorBearingSpatialUnit?_eq_some_iff
        axis.initial.left axis.initial.right leftCompilation.endpointFrame
        rightCompilation.endpointFrame _ _ leftValid rightValid unit).mpr spatial
    have geometryComputed :=
      (monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff
        unit.geometry cyclicGeometry).mpr geometryRefines
    have descriptorComputed :=
      (BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?_eq_some_iff
        policyResult.carrier.ring.card policyResult.doubleBondCount
        cyclicGeometry descriptor).mpr assignment
    simp [localizedRule3OrdinaryMonocyclicEZWith?, routeComputed, required,
      leftComputed, rightComputed, unitComputed, geometryComputed,
      descriptorComputed,
      LocalizedRule3OrdinaryMonocyclicPolicyAtOccurrenceResult.initial]

/-- A direct whole-molecule permanent-omission policy cannot emit an `E/Z` descriptor. -/
theorem localizedRule3OrdinaryMonocyclicEZWith?_eq_none_of_omitted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (ordinary : axis.doubleBondCount = 1)
    (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
    (routeComputed : input.localizedRule3OrdinaryMonocyclicPolicyAtOccurrence? occurrence =
      some { axis, ordinary, policyResult })
    (omitted : policyResult.policy = .permanentlyOmit) :
    input.localizedRule3OrdinaryMonocyclicEZWith?
      target occurrence view rule3FrameOf = none := by
  simp [localizedRule3OrdinaryMonocyclicEZWith?, routeComputed, omitted]

/-- Complete descriptor-bearing result for one required ordinary monocyclic `E/Z` unit. -/
structure LocalizedRule3RequiredMonocyclicEZResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel
  closure : input.LocalizedRerootCursor carrierFuel
  policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult
  leftCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel
  unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult
  descriptor : BlueBookP93.Acyclic.Descriptor

/-- Project a proved cyclic assignment to the identity-aware Rule-3 observation consumed by the
recursive key scheduler. The independently checked final `E/Z` remains in the source result. -/
def localizedRule3RequiredMonocyclicEZObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel) :
    input.LocalizedRule3SpatialNodeResult :=
  let leftReference := match result.unit.leftPriority with
    | .senior reference => reference
    | .nonstereogenic => result.leftCompilation.endpointFrame.first
  let rightReference := match result.unit.rightPriority with
    | .senior reference => reference
    | .nonstereogenic => result.rightCompilation.endpointFrame.first
  { left := result.initial.left
    right := result.initial.right
    unit := { leftReference, rightReference, geometry := result.unit.geometry } }

@[simp] theorem localizedRule3RequiredMonocyclicEZObservation_geometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel) :
    (input.localizedRule3RequiredMonocyclicEZObservation result).unit.geometry =
      result.unit.geometry := by
  rfl

/-- After exact cyclic authority routing, compile both endpoint ligand pairs and emit the
independently specified cyclic `E/Z` descriptor. -/
noncomputable def localizedRule3RequiredMonocyclicEZWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel) := do
  let route ← input.localizedRule3CyclicAuthorityRoute? occurrence
  match route with
  | .ordinaryMonocyclicPolicy initial closure policyResult =>
      match policyResult.policy with
      | .permanentlyOmit => none
      | .requireEZ => do
          let leftCompilation ←
            input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf initial.left initial.right initial.leftCursor
          let rightCompilation ←
            input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
              target view rule3FrameOf initial.right initial.left initial.rightCursor
          let unit ← input.localizedRule3DescriptorBearingSpatialUnit?
            initial.left initial.right leftCompilation.endpointFrame
              rightCompilation.endpointFrame
          let cyclicGeometry ← monocyclicSeniorLigandGeometryOfRule3? unit.geometry
          let descriptor ← BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
            policyResult.carrier.ring.card policyResult.doubleBondCount cyclicGeometry
          some
            { initial
              closure
              policyResult
              leftCompilation
              rightCompilation
              unit
              descriptor }
  | .fullyCyclicCumulene _ _ _
  | .ordinaryMonocyclicPolicyGap _ _ _ _
  | .ordinaryNonmonocyclic _ _ => none

/-- Independent topology, complete endpoint-key, exact spatial, and P-93 descriptor meaning of a
successful cyclic assignment. -/
def DeclarativeLocalizedRule3RequiredMonocyclicEZWith
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.ordinaryMonocyclicPolicy result.initial result.closure result.policyResult) ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.initial.left result.initial.right
      result.initial.leftCursor result.leftCompilation ∧
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning result.initial.right result.initial.left
      result.initial.rightCursor result.rightCompilation ∧
    input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
      result.initial.left result.initial.right
      result.leftCompilation.endpointFrame result.rightCompilation.endpointFrame
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          result.initial.leftCursor cursor reference ∧
        ((cursor = result.leftCompilation.firstCursor ∧
            key = result.leftCompilation.endpointFrame.firstKey) ∨
         (cursor = result.leftCompilation.secondCursor ∧
            key = result.leftCompilation.endpointFrame.secondKey)))
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          result.initial.rightCursor cursor reference ∧
        ((cursor = result.rightCompilation.firstCursor ∧
            key = result.rightCompilation.endpointFrame.firstKey) ∨
         (cursor = result.rightCompilation.secondCursor ∧
            key = result.rightCompilation.endpointFrame.secondKey)))
      result.unit ∧
    ∃ cyclicGeometry,
      Rule3GeometryRefinesMonocyclicSeniorLigandGeometry
        result.unit.geometry cyclicGeometry ∧
      BlueBookP93.Cyclic.RequiredMonocyclicEZAssignment
        result.policyResult.carrier.ring.card result.policyResult.doubleBondCount
        cyclicGeometry result.descriptor

/-- Every emitted cyclic descriptor has exact molecule topology, occurrence-local Rules-1a--5
endpoint priorities, rational senior-ligand geometry, and the independent P-93 assignment. -/
theorem localizedRule3RequiredMonocyclicEZWith?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (computed : input.localizedRule3RequiredMonocyclicEZWith?
      target occurrence view rule3FrameOf = some result) :
    input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
      target occurrence view Rule3FrameMeaning result := by
  unfold localizedRule3RequiredMonocyclicEZWith? at computed
  cases routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence with
  | none => simp [routeComputed] at computed
  | some route =>
      cases route with
      | fullyCyclicCumulene initial closure component =>
          simp [routeComputed] at computed
      | ordinaryMonocyclicPolicyGap initial closure carrier doubleBondCount =>
          simp [routeComputed] at computed
      | ordinaryNonmonocyclic initial closure =>
          simp [routeComputed] at computed
      | ordinaryMonocyclicPolicy initial closure policyResult =>
          cases policyIdentity : policyResult.policy with
          | permanentlyOmit => simp [routeComputed, policyIdentity] at computed
          | requireEZ =>
              cases leftComputed :
                  input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                    target view rule3FrameOf initial.left initial.right
                      initial.leftCursor with
              | none => simp [routeComputed, policyIdentity, leftComputed] at computed
              | some leftCompilation =>
                  cases rightComputed :
                      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                        target view rule3FrameOf initial.right initial.left
                          initial.rightCursor with
                  | none =>
                      simp [routeComputed, policyIdentity, leftComputed,
                        rightComputed] at computed
                  | some rightCompilation =>
                      cases unitComputed :
                          input.localizedRule3DescriptorBearingSpatialUnit?
                            initial.left initial.right leftCompilation.endpointFrame
                              rightCompilation.endpointFrame with
                      | none =>
                          simp [routeComputed, policyIdentity, leftComputed,
                            rightComputed, unitComputed] at computed
                      | some unit =>
                          cases geometryComputed :
                              monocyclicSeniorLigandGeometryOfRule3? unit.geometry with
                          | none =>
                              simp [routeComputed, policyIdentity, leftComputed,
                                rightComputed, unitComputed, geometryComputed] at computed
                          | some cyclicGeometry =>
                              cases descriptorComputed :
                                  BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
                                    policyResult.carrier.ring.card
                                      policyResult.doubleBondCount cyclicGeometry with
                              | none =>
                                  simp [routeComputed, policyIdentity, leftComputed,
                                    rightComputed, unitComputed, geometryComputed,
                                    descriptorComputed] at computed
                              | some descriptor =>
                                  simp [routeComputed, policyIdentity, leftComputed,
                                    rightComputed, unitComputed, geometryComputed,
                                    descriptorComputed] at computed
                                  subst result
                                  have leftDerived :=
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                                      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                                      initial.left initial.right initial.leftCursor
                                      leftCompilation leftComputed
                                  have rightDerived :=
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                                      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                                      initial.right initial.left initial.rightCursor
                                      rightCompilation rightComputed
                                  exact ⟨
                                    input.localizedRule3CyclicAuthorityRoute?_sound occurrence
                                      (.ordinaryMonocyclicPolicy
                                        initial closure policyResult) routeComputed,
                                    leftDerived,
                                    rightDerived,
                                    input.localizedRule3DescriptorBearingSpatialUnit?_sound
                                      initial.left initial.right
                                      leftCompilation.endpointFrame
                                      rightCompilation.endpointFrame _ _
                                      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
                                        input target view Rule3FrameMeaning initial.left
                                        initial.right initial.leftCursor leftCompilation
                                        leftDerived)
                                      (DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
                                        input target view Rule3FrameMeaning initial.right
                                        initial.left initial.rightCursor rightCompilation
                                        rightDerived)
                                      unit unitComputed,
                                    ⟨cyclicGeometry,
                                      (monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff
                                        unit.geometry cyclicGeometry).mp geometryComputed,
                                      (BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?_eq_some_iff
                                        policyResult.carrier.ring.card
                                        policyResult.doubleBondCount cyclicGeometry
                                        descriptor).mp descriptorComputed⟩⟩

/-- Once the exact authority route and both endpoint compilations are fixed, final production
success is equivalent in both directions to the independent spatial and cyclic assignment
relations. This isolates the remaining completeness obligations to route/endpoint discovery. -/
theorem localizedRule3RequiredMonocyclicEZWith?_eq_some_iff_of_required_compilations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
    (leftCompilation rightCompilation :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.ordinaryMonocyclicPolicy initial closure policyResult))
    (required : policyResult.policy = .requireEZ)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf initial.left initial.right initial.leftCursor =
        some leftCompilation)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf initial.right initial.left initial.rightCursor =
        some rightCompilation)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (descriptor : BlueBookP93.Acyclic.Descriptor) :
    input.localizedRule3RequiredMonocyclicEZWith?
        target occurrence view rule3FrameOf =
      some
        { initial
          closure
          policyResult
          leftCompilation
          rightCompilation
          unit
          descriptor } ↔
      input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
          initial.left initial.right leftCompilation.endpointFrame
          rightCompilation.endpointFrame
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
        ∃ cyclicGeometry,
          Rule3GeometryRefinesMonocyclicSeniorLigandGeometry
            unit.geometry cyclicGeometry ∧
          BlueBookP93.Cyclic.RequiredMonocyclicEZAssignment
            policyResult.carrier.ring.card policyResult.doubleBondCount
            cyclicGeometry descriptor := by
  have leftDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
      initial.left initial.right initial.leftCursor leftCompilation leftComputed
  have rightDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
      initial.right initial.left initial.rightCursor rightCompilation rightComputed
  have leftValid :=
    DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
      input target view Rule3FrameMeaning initial.left initial.right
      initial.leftCursor leftCompilation leftDerived
  have rightValid :=
    DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
      input target view Rule3FrameMeaning initial.right initial.left
      initial.rightCursor rightCompilation rightDerived
  constructor
  · intro computed
    have derived := input.localizedRule3RequiredMonocyclicEZWith?_sound
      target occurrence view rule3FrameOf Rule3FrameMeaning rule3FrameSound _ computed
    rcases derived with ⟨_route, _left, _right, spatial, assignment⟩
    exact ⟨spatial, assignment⟩
  · rintro ⟨spatial, cyclicGeometry, geometryRefines, assignment⟩
    have unitComputed :=
      (input.localizedRule3DescriptorBearingSpatialUnit?_eq_some_iff
        initial.left initial.right leftCompilation.endpointFrame
        rightCompilation.endpointFrame _ _ leftValid rightValid unit).mpr spatial
    have geometryComputed :=
      (monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff
        unit.geometry cyclicGeometry).mpr geometryRefines
    have descriptorComputed :=
      (BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?_eq_some_iff
        policyResult.carrier.ring.card policyResult.doubleBondCount
        cyclicGeometry descriptor).mpr assignment
    simp [localizedRule3RequiredMonocyclicEZWith?, routeComputed, required,
      leftComputed, rightComputed, unitComputed, geometryComputed,
      descriptorComputed]

/-- A proved permanent-omission route cannot emit an `E/Z` descriptor. -/
theorem localizedRule3RequiredMonocyclicEZWith?_eq_none_of_omitted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult)
    (routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.ordinaryMonocyclicPolicy initial closure policyResult))
    (omitted : policyResult.policy = .permanentlyOmit) :
    input.localizedRule3RequiredMonocyclicEZWith?
      target occurrence view rule3FrameOf = none := by
  simp [localizedRule3RequiredMonocyclicEZWith?, routeComputed, omitted]

/-- Fully cyclic cumulenes are outside this open endpoint-pair descriptor assignment. -/
theorem localizedRule3RequiredMonocyclicEZWith?_eq_none_of_fullyCyclic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (component : input.LocalizedCyclicCumuleneComponent)
    (routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.fullyCyclicCumulene initial closure component)) :
    input.localizedRule3RequiredMonocyclicEZWith?
      target occurrence view rule3FrameOf = none := by
  simp [localizedRule3RequiredMonocyclicEZWith?, routeComputed]

/-- Polycyclic and otherwise nonmonocyclic cyclic topologies cannot inherit the monocyclic
descriptor path. -/
theorem localizedRule3RequiredMonocyclicEZWith?_eq_none_of_nonmonocyclic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (routeComputed : input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.ordinaryNonmonocyclic initial closure)) :
    input.localizedRule3RequiredMonocyclicEZWith?
      target occurrence view rule3FrameOf = none := by
  simp [localizedRule3RequiredMonocyclicEZWith?, routeComputed]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
