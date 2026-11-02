import TetraStereo.OneCenter.LocalizedExtendedNodeConditionalGeometry
import TetraStereo.OneCenter.LocalizedRule3ReferenceExchange
import TetraStereo.OneCenter.LocalizedRule3GeometryDefinedness
import TetraStereo.OneCenter.LocalizedRule3PhysicalTopologyExecutable
import TetraStereo.OneCenter.LocalizedRule3CumulatedChainExecutable
import TetraStereo.OneCenter.Rule3SpatialReferenceExchangeWitness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

universe u





































































/-! ## Exact reference-pair readiness and its transport -/

namespace CartesianPoint3

/-- Exact readiness of one reference pairing for Rule-3 geometry: the axis and the two reference
arms are coplanar, and the two exact side normals are not orthogonal.  This is the
coordinate-level content of `LocalizedRule3ReferenceGeometryReady`, stated without any atom
lookup. -/
def Rule3ReferencePairReady (leftEndpoint rightEndpoint leftReference rightReference :
    CartesianPoint3) : Prop :=
  rule3Coplanarity leftEndpoint rightEndpoint leftReference rightReference = 0 ∧
    rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference ≠ 0

/-- Readiness is exactly success of the exact classifier on the same coordinates (with the sign of
the nonzero side product selecting the branch). -/
theorem rule3GeometryOfSpatialReferences?_isSome_of_pairReady
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3)
    (ready : Rule3ReferencePairReady leftEndpoint rightEndpoint leftReference rightReference) :
    (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
      leftReference rightReference).isSome := by
  obtain ⟨coplanar, sideNonzero⟩ := ready
  rcases lt_or_gt_of_ne sideNonzero with sideNegative | sidePositive
  · have computed :
        rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
            leftReference rightReference = some OfficialRule3Geometry.seqtrans :=
      (rule3GeometryOfSpatialReferences?_eq_some_iff leftEndpoint rightEndpoint
        leftReference rightReference .seqtrans).mpr ⟨coplanar, sideNegative⟩
    simp [computed]
  · have computed :
        rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
            leftReference rightReference = some OfficialRule3Geometry.seqcis :=
      (rule3GeometryOfSpatialReferences?_eq_some_iff leftEndpoint rightEndpoint
        leftReference rightReference .seqcis).mpr ⟨coplanar, sidePositive⟩
    simp [computed]

/-- Replacing the right-endpoint reference by an opposite-side partner preserves exact reference
readiness.  The exact coplanarity and side product are both scaled by `-k` with `k > 0`. -/
theorem rule3ReferencePairReady_exchangeRight
    (leftEndpoint rightEndpoint leftReference rightReference newRightReference : CartesianPoint3)
    (k t : ℚ) (kpos : 0 < k)
    (arm : RationalVector3.OppositeSideArm
      (displacement rightEndpoint rightReference)
      (displacement rightEndpoint newRightReference)
      (displacement leftEndpoint rightEndpoint) k t)
    (ready : Rule3ReferencePairReady leftEndpoint rightEndpoint leftReference rightReference) :
    Rule3ReferencePairReady leftEndpoint rightEndpoint leftReference newRightReference := by
  obtain ⟨coplanar, sideNonzero⟩ := ready
  refine ⟨?_, ?_⟩
  · rw [rule3Coplanarity_exchangeRightReference leftEndpoint rightEndpoint leftReference
      rightReference newRightReference k t arm, coplanar, mul_zero]
  · rw [rule3SideProduct_exchangeRightReference leftEndpoint rightEndpoint leftReference
      rightReference newRightReference k t arm]
    exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt kpos)) sideNonzero

/-- Replacing the left-endpoint reference by an opposite-side partner preserves exact reference
readiness. -/
theorem rule3ReferencePairReady_exchangeLeft
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference : CartesianPoint3)
    (k t : ℚ) (kpos : 0 < k)
    (arm : RationalVector3.OppositeSideArm
      (displacement leftEndpoint leftReference)
      (displacement leftEndpoint newLeftReference)
      (displacement leftEndpoint rightEndpoint) k t)
    (ready : Rule3ReferencePairReady leftEndpoint rightEndpoint leftReference rightReference) :
    Rule3ReferencePairReady leftEndpoint rightEndpoint newLeftReference rightReference := by
  obtain ⟨coplanar, sideNonzero⟩ := ready
  refine ⟨?_, ?_⟩
  · rw [rule3Coplanarity_exchangeLeftReference leftEndpoint rightEndpoint leftReference
      newLeftReference rightReference k t arm, coplanar, mul_zero]
  · rw [rule3SideProduct_exchangeLeftReference leftEndpoint rightEndpoint leftReference
      newLeftReference rightReference k t arm]
    exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt kpos)) sideNonzero

/-- **All four reference pairings from one ready pairing and two opposite-side alternative arms.**
This is the reusable geometric core: a single coplanar, nondegenerate reference pairing plus one
opposite-side arm relation at each endpoint yields readiness of the reference pairing, of each
single exchange, and of the double exchange.  No further assumption on the alternatives is used. -/
theorem rule3ReferencePairReady_candidatePairs
    (leftEndpoint rightEndpoint baseLeft alternativeLeft baseRight alternativeRight :
      CartesianPoint3)
    (kLeft tLeft kRight tRight : ℚ) (kLeftPos : 0 < kLeft) (kRightPos : 0 < kRight)
    (baseReady : Rule3ReferencePairReady leftEndpoint rightEndpoint baseLeft baseRight)
    (leftArm : RationalVector3.OppositeSideArm
      (displacement leftEndpoint baseLeft)
      (displacement leftEndpoint alternativeLeft)
      (displacement leftEndpoint rightEndpoint) kLeft tLeft)
    (rightArm : RationalVector3.OppositeSideArm
      (displacement rightEndpoint baseRight)
      (displacement rightEndpoint alternativeRight)
      (displacement leftEndpoint rightEndpoint) kRight tRight) :
    Rule3ReferencePairReady leftEndpoint rightEndpoint baseLeft baseRight ∧
      Rule3ReferencePairReady leftEndpoint rightEndpoint baseLeft alternativeRight ∧
      Rule3ReferencePairReady leftEndpoint rightEndpoint alternativeLeft baseRight ∧
      Rule3ReferencePairReady leftEndpoint rightEndpoint alternativeLeft alternativeRight := by
  have rightExchanged : Rule3ReferencePairReady leftEndpoint rightEndpoint baseLeft
      alternativeRight :=
    rule3ReferencePairReady_exchangeRight leftEndpoint rightEndpoint baseLeft baseRight
      alternativeRight kRight tRight kRightPos rightArm baseReady
  have leftExchanged : Rule3ReferencePairReady leftEndpoint rightEndpoint alternativeLeft
      baseRight :=
    rule3ReferencePairReady_exchangeLeft leftEndpoint rightEndpoint baseLeft alternativeLeft
      baseRight kLeft tLeft kLeftPos leftArm baseReady
  have bothExchanged : Rule3ReferencePairReady leftEndpoint rightEndpoint alternativeLeft
      alternativeRight :=
    rule3ReferencePairReady_exchangeLeft leftEndpoint rightEndpoint baseLeft alternativeLeft
      alternativeRight kLeft tLeft kLeftPos leftArm rightExchanged
  exact ⟨baseReady, rightExchanged, leftExchanged, bothExchanged⟩

/-- Two independent opposite-side exchanges scale the exact side product by a positive rational
`kLeft * kRight`; the coplanarity remains zero.  This records the double-exchange normalisation
used by `rule3ReferencePairReady_candidatePairs`. -/
theorem rule3Coplanarity_sideProduct_doubleExchange
    (leftEndpoint rightEndpoint baseLeft alternativeLeft baseRight alternativeRight :
      CartesianPoint3)
    (kLeft tLeft kRight tRight : ℚ)
    (leftArm : RationalVector3.OppositeSideArm
      (displacement leftEndpoint baseLeft)
      (displacement leftEndpoint alternativeLeft)
      (displacement leftEndpoint rightEndpoint) kLeft tLeft)
    (rightArm : RationalVector3.OppositeSideArm
      (displacement rightEndpoint baseRight)
      (displacement rightEndpoint alternativeRight)
      (displacement leftEndpoint rightEndpoint) kRight tRight) :
    rule3Coplanarity leftEndpoint rightEndpoint alternativeLeft alternativeRight =
        kLeft * kRight *
          rule3Coplanarity leftEndpoint rightEndpoint baseLeft baseRight ∧
      rule3SideProduct leftEndpoint rightEndpoint alternativeLeft alternativeRight =
        kLeft * kRight *
          rule3SideProduct leftEndpoint rightEndpoint baseLeft baseRight := by
  have rightCoplanar := rule3Coplanarity_exchangeRightReference leftEndpoint rightEndpoint
    baseLeft baseRight alternativeRight kRight tRight rightArm
  have rightSide := rule3SideProduct_exchangeRightReference leftEndpoint rightEndpoint
    baseLeft baseRight alternativeRight kRight tRight rightArm
  constructor
  · rw [rule3Coplanarity_exchangeLeftReference leftEndpoint rightEndpoint baseLeft
      alternativeLeft alternativeRight kLeft tLeft leftArm, rightCoplanar]
    ring
  · rw [rule3SideProduct_exchangeLeftReference leftEndpoint rightEndpoint baseLeft
      alternativeLeft alternativeRight kLeft tLeft leftArm, rightSide]
    ring

end CartesianPoint3

/-! ## The stronger common-plane condition

`Rule3SpatialReferenceExchangeWitness` derives the negative-scale arm relation from a purely
coordinate-based common-plane statement.  The two existing conditions

* `PlanarFourSubstituentOppositeSideLeft` (the right reference arm is the nondegenerate anchor), and
* `PlanarFourSubstituentOppositeSideRight` (the left reference arm is the anchor)

require every substituent arm to lie in one plane through the directed axis, require each endpoint's
reference arm to be noncollinear with the axis, and require the exact side product between the
selected reference and its alternative to be strictly negative.  They produce the `k > 0` and `t`
data of `OppositeSideArm`; neither a side nor a scale witness is assumed.

Composing the corresponding existing construction lemmas with the four-pair core below therefore
yields all four candidate readiness facts from atom coordinates alone. -/

namespace CartesianPoint3

/-- **All four candidate pairings from the common-plane coordinate conditions.**  The left- and
right-endpoint planar four-substituent conditions supply the two opposite-side arm relations, and
`rule3ReferencePairReady_candidatePairs` then yields the four readiness facts.  Every geometric
hypothesis is an atom-coordinate equation; no scale, axis shift, plane normal, arm relation or
selected-reference success is assumed. -/
theorem rule3ReferencePairReady_candidatePairs_of_planarFourSubstituent
    (leftEndpoint rightEndpoint baseLeft alternativeLeft baseRight alternativeRight :
      CartesianPoint3)
    (planarLeft : PlanarFourSubstituentOppositeSideLeft leftEndpoint rightEndpoint baseLeft
      alternativeLeft baseRight alternativeRight)
    (planarRight : PlanarFourSubstituentOppositeSideRight leftEndpoint rightEndpoint baseLeft
      alternativeLeft baseRight alternativeRight)
    (baseReady : Rule3ReferencePairReady leftEndpoint rightEndpoint baseLeft baseRight) :
    Rule3ReferencePairReady leftEndpoint rightEndpoint baseLeft baseRight ∧
      Rule3ReferencePairReady leftEndpoint rightEndpoint baseLeft alternativeRight ∧
      Rule3ReferencePairReady leftEndpoint rightEndpoint alternativeLeft baseRight ∧
      Rule3ReferencePairReady leftEndpoint rightEndpoint alternativeLeft alternativeRight := by
  obtain ⟨kLeft, tLeft, kLeftPos, leftArm⟩ :=
    exists_oppositeSideArm_of_planarFourSubstituentOppositeSideLeft
      leftEndpoint rightEndpoint baseLeft alternativeLeft baseRight alternativeRight planarLeft
  obtain ⟨kRight, tRight, kRightPos, rightArm⟩ :=
    exists_oppositeSideArm_of_planarFourSubstituentOppositeSideRight
      leftEndpoint rightEndpoint baseLeft alternativeLeft baseRight alternativeRight planarRight
  exact rule3ReferencePairReady_candidatePairs leftEndpoint rightEndpoint baseLeft
    alternativeLeft baseRight alternativeRight kLeft tLeft kRight tRight kLeftPos kRightPos
    baseReady leftArm rightArm

end CartesianPoint3

/-! ## Reasoning-side arm relations -/

namespace RationalVector3

/-- The opposite-side arm relation is symmetric: if `new = (-k) • old + t • axis` with `k > 0`,
then `old = (-(k⁻¹)) • new + (t / k) • axis`, again with a positive scaling factor. -/
theorem OppositeSideArm.symm {oldArm newArm axis : RationalVector3} {k t : ℚ}
    (arm : OppositeSideArm oldArm newArm axis k t) (kpos : 0 < k) :
    ∃ k' t' : ℚ, 0 < k' ∧ OppositeSideArm newArm oldArm axis k' t' := by
  refine ⟨k⁻¹, t / k, inv_pos.mpr kpos, ?_⟩
  rw [OppositeSideArm] at arm ⊢
  rw [arm]
  apply ext <;> simp [vadd, vsmul] <;> field_simp <;> ring

/-- An arm pair is in opposite-side relation about an axis when the relation holds in at least one
direction with a positive scaling factor. -/
def OppositeSideArms (axis first second : RationalVector3) : Prop :=
  ∃ k t : ℚ, 0 < k ∧ OppositeSideArm first second axis k t

/-- The opposite-side relation is independent of which arm is named first. -/
theorem oppositeSideArms_comm {axis first second : RationalVector3}
    (related : OppositeSideArms axis first second) : OppositeSideArms axis second first := by
  obtain ⟨k, t, kpos, arm⟩ := related
  obtain ⟨k', t', k'pos, arm'⟩ := arm.symm kpos
  exact ⟨k', t', k'pos, arm'⟩

end RationalVector3

/-! ## The atom-coordinate geometry condition -/

namespace CertifiedLocalizedCIPInput

/-- **Independent molecular coordinate condition for one physical Rule-3 axis.**  The six atoms are
the two axis endpoints and the two candidate substituents at each endpoint, each read at its actual
semantic coordinate.  The first candidate pairing is coplanar with the directed axis and has a
nonvanishing exact side product; at each endpoint the second candidate arm is the opposite-side
image of the first about that directed axis with positive exact scaling.

No evaluator, callback, key, priority, desired descriptor or selected reference occurs here. -/
def LocalizedRule3AxisCoordinateGeometryReady
    (input : CertifiedLocalizedCIPInput)
    (left right leftFirst leftSecond rightFirst rightSecond : input.Atom) : Prop :=
  ∃ leftPoint rightPoint leftFirstPoint leftSecondPoint rightFirstPoint rightSecondPoint :
      CartesianPoint3,
    ∃ kLeft tLeft kRight tRight : ℚ,
      input.spatialPointAt? left = some leftPoint ∧
        input.spatialPointAt? right = some rightPoint ∧
        input.spatialPointAt? leftFirst = some leftFirstPoint ∧
        input.spatialPointAt? leftSecond = some leftSecondPoint ∧
        input.spatialPointAt? rightFirst = some rightFirstPoint ∧
        input.spatialPointAt? rightSecond = some rightSecondPoint ∧
        0 < kLeft ∧ 0 < kRight ∧
        CartesianPoint3.rule3Coplanarity leftPoint rightPoint
            leftFirstPoint rightFirstPoint = 0 ∧
        CartesianPoint3.rule3SideProduct leftPoint rightPoint
            leftFirstPoint rightFirstPoint ≠ 0 ∧
        RationalVector3.OppositeSideArm
          (CartesianPoint3.displacement leftPoint leftFirstPoint)
          (CartesianPoint3.displacement leftPoint leftSecondPoint)
          (CartesianPoint3.displacement leftPoint rightPoint) kLeft tLeft ∧
        RationalVector3.OppositeSideArm
          (CartesianPoint3.displacement rightPoint rightFirstPoint)
          (CartesianPoint3.displacement rightPoint rightSecondPoint)
          (CartesianPoint3.displacement leftPoint rightPoint) kRight tRight

/-- **The coordinate condition yields all four actual candidate readiness facts.**  Each of the
four pairings obtains its `spatialPointAt?` witness from the same six actual coordinates, and its
exact coplanarity/side-product facts from the reference-exchange core. -/
theorem localizedRule3AxisCandidateGeometryReadiness_of_coordinateGeometry
    (input : CertifiedLocalizedCIPInput)
    (left right leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (ready : input.LocalizedRule3AxisCoordinateGeometryReady
      left right leftFirst leftSecond rightFirst rightSecond) :
    input.LocalizedRule3AxisCandidateGeometryReadiness
      left right leftFirst leftSecond rightFirst rightSecond := by
  obtain ⟨leftPoint, rightPoint, leftFirstPoint, leftSecondPoint, rightFirstPoint,
    rightSecondPoint, kLeft, tLeft, kRight, tRight, leftComputed, rightComputed,
    leftFirstComputed, leftSecondComputed, rightFirstComputed, rightSecondComputed,
    kLeftPos, kRightPos, coplanar, sideNonzero, leftArm, rightArm⟩ := ready
  have pairs := CartesianPoint3.rule3ReferencePairReady_candidatePairs leftPoint rightPoint
    leftFirstPoint leftSecondPoint rightFirstPoint rightSecondPoint kLeft tLeft kRight tRight
    kLeftPos kRightPos ⟨coplanar, sideNonzero⟩ leftArm rightArm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨leftPoint, rightPoint, leftFirstPoint, rightFirstPoint, leftComputed,
      rightComputed, leftFirstComputed, rightFirstComputed, pairs.1.1, pairs.1.2⟩
  · exact ⟨leftPoint, rightPoint, leftFirstPoint, rightSecondPoint, leftComputed,
      rightComputed, leftFirstComputed, rightSecondComputed, pairs.2.1.1, pairs.2.1.2⟩
  · exact ⟨leftPoint, rightPoint, leftSecondPoint, rightFirstPoint, leftComputed,
      rightComputed, leftSecondComputed, rightFirstComputed, pairs.2.2.1.1, pairs.2.2.1.2⟩
  · exact ⟨leftPoint, rightPoint, leftSecondPoint, rightSecondPoint, leftComputed,
      rightComputed, leftSecondComputed, rightSecondComputed, pairs.2.2.2.1, pairs.2.2.2.2⟩

/-! ## The graph-axis coordinate domain -/

/-- **The graph-axis coordinate geometry domain.**

For every declarative physical endpoint frame (a genuine order-two bond path with the recovered
carrier-parent topology) and every exact two-atom candidate list at each endpoint, the six actual
atoms satisfy the coordinate geometry condition.

For every declarative odd-cumulene endpoint frame (a genuine terminal-to-terminal odd cumulated path
with its two terminal substituent partners) and every exact two-atom candidate list at each terminal,
the six actual atoms satisfy the coordinate geometry condition.

The quantification is restricted to axes actually derivable from the molecular graph through those
declarative route relations; candidate lists are the actual terminal-neighbour lists.  No
occurrence, atom pair or candidate list outside the graph structure is quantified over, so the
domain remains a physical statement about the molecule's own atoms. -/
def LocalizedRule3AxisCoordinateGeometryDomain
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) : Prop :=
  (∀ (occurrence : input.LocalizedCIPOccurrence carrierFuel)
     (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
     (leftFirst leftSecond rightFirst rightSecond : input.Atom),
      input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence topology →
      input.localizedRule3ExplicitSubstituents topology.left topology.right =
          [leftFirst, leftSecond] →
      input.localizedRule3ExplicitSubstituents topology.right topology.left =
          [rightFirst, rightSecond] →
      input.LocalizedRule3AxisCoordinateGeometryReady topology.left topology.right
        leftFirst leftSecond rightFirst rightSecond) ∧
  (∀ (occurrence : input.LocalizedCIPOccurrence carrierFuel)
     (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
     (leftFirst leftSecond rightFirst rightSecond : input.Atom),
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence topology →
      input.localizedRule3ExplicitSubstituents topology.initial.left
          topology.initial.right = [leftFirst, leftSecond] →
      input.localizedRule3ExplicitSubstituents topology.right topology.rightPartner =
          [rightFirst, rightSecond] →
      input.LocalizedRule3AxisCoordinateGeometryReady topology.initial.left topology.right
        leftFirst leftSecond rightFirst rightSecond)

/-- The same physical graph-axis condition, stated for every carrier fuel. -/
def LocalizedRule3AxisCoordinateGeometryDomainAll
    (input : CertifiedLocalizedCIPInput) : Prop :=
  ∀ carrierFuel : Nat, input.LocalizedRule3AxisCoordinateGeometryDomain carrierFuel








theorem localizedRule3ExtendedNodeConditionalGeometryDomain_of_axisCoordinateGeometry
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (domain : input.LocalizedRule3AxisCoordinateGeometryDomain carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.LocalizedRule3ExtendedNodeConditionalGeometryDomain occurrence := by
  unfold LocalizedRule3ExtendedNodeConditionalGeometryDomain
  cases odd : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
    intro topology leftFirst leftSecond rightFirst rightSecond
      leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor
      found leftCandidates rightCandidates
      _leftFirstSelected _leftSecondSelected _rightFirstSelected _rightSecondSelected
    have originalComputed :
        input.localizedRule3OddCumuleneEndpointCursorFrame?
            (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence =
          some topology := by
      rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence]
      exact found
    have declarative :
        input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence topology :=
      input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence topology
        originalComputed
    exact input.localizedRule3AxisCandidateGeometryReadiness_of_coordinateGeometry
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
      (domain.2 occurrence topology leftFirst leftSecond rightFirst rightSecond declarative
        leftCandidates rightCandidates)
  | none =>
      cases ordinary : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some certificate =>
          intro topology leftFirst leftSecond rightFirst rightSecond
            leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor
            found leftCandidates rightCandidates
            _leftFirstSelected _leftSecondSelected _rightFirstSelected _rightSecondSelected
          have declarative :
              input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence topology :=
            input.localizedRule3PhysicalEndpointCursorFrameExec?_sound occurrence topology found
          exact input.localizedRule3AxisCandidateGeometryReadiness_of_coordinateGeometry
            topology.left topology.right leftFirst leftSecond rightFirst rightSecond
            (domain.1 occurrence topology leftFirst leftSecond rightFirst rightSecond
              declarative leftCandidates rightCandidates)
      | none => exact trivial




theorem localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometry
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (domain : input.LocalizedRule3AxisCoordinateGeometryDomain carrierFuel) :
    input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel := by
  intro occurrence
  exact input.localizedRule3ExtendedNodeConditionalGeometryDomain_of_axisCoordinateGeometry
    carrierFuel domain occurrence


theorem localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometryAll
    (input : CertifiedLocalizedCIPInput)
    (domain : input.LocalizedRule3AxisCoordinateGeometryDomainAll) (carrierFuel : Nat) :
    input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel :=
  input.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometry
    carrierFuel (domain carrierFuel)

end CertifiedLocalizedCIPInput

/-! ## A nonvacuous planar double-bond example

The six exact rational points below are the coordinate data of the existing certified
difluoroethene fixture (`Examples/LocalizedShortCircuitDoubleBondProbe.source true`): atoms `0`
and `1` are the two carbon endpoints at `(0,0,0)` and `(2,0,0)`, atoms `2`/`4` are the two
substituents on atom `0` at `(0,1,0)`/`(0,-1,0)`, and atoms `3`/`5` are the two substituents on
atom `1` at `(2,1,0)`/`(2,-1,0)`.  Every point has `z = 0`, so the whole unit is planar. -/

namespace PlanarDifluoroetheneExample

/-- Isolated left double-bond endpoint (carbon atom `0`). -/
def leftEndpoint : CartesianPoint3 := { x := 0, y := 0, z := 0 }

/-- Isolated right double-bond endpoint (carbon atom `1`). -/
def rightEndpoint : CartesianPoint3 := { x := 2, y := 0, z := 0 }

/-- First left substituent (fluorine atom `2`), above the axis. -/
def leftFirst : CartesianPoint3 := { x := 0, y := 1, z := 0 }

/-- Second left substituent (hydrogen atom `4`), below the axis. -/
def leftSecond : CartesianPoint3 := { x := 0, y := -1, z := 0 }

/-- First right substituent (fluorine atom `3`), above the axis. -/
def rightFirst : CartesianPoint3 := { x := 2, y := 1, z := 0 }

/-- Second right substituent (hydrogen atom `5`), below the axis. -/
def rightSecond : CartesianPoint3 := { x := 2, y := -1, z := 0 }

/-- The left alternative arm is the opposite-side image of the left reference arm. -/
theorem leftArm : RationalVector3.OppositeSideArm
    (CartesianPoint3.displacement leftEndpoint leftFirst)
    (CartesianPoint3.displacement leftEndpoint leftSecond)
    (CartesianPoint3.displacement leftEndpoint rightEndpoint) 1 0 := by
  apply RationalVector3.ext <;>
    simp [RationalVector3.OppositeSideArm, RationalVector3.vadd, RationalVector3.vsmul,
      CartesianPoint3.displacement, leftEndpoint, rightEndpoint, leftFirst, leftSecond]

/-- The right alternative arm is the opposite-side image of the right reference arm. -/
theorem rightArm : RationalVector3.OppositeSideArm
    (CartesianPoint3.displacement rightEndpoint rightFirst)
    (CartesianPoint3.displacement rightEndpoint rightSecond)
    (CartesianPoint3.displacement leftEndpoint rightEndpoint) 1 0 := by
  apply RationalVector3.ext <;>
    simp [RationalVector3.OppositeSideArm, RationalVector3.vadd, RationalVector3.vsmul,
      CartesianPoint3.displacement, leftEndpoint, rightEndpoint, rightFirst, rightSecond]

/-- The reference pairing is coplanar with the axis and has nonvanishing exact side product. -/
theorem referencePairReady :
    CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftFirst rightFirst := by
  constructor
  · norm_num [CartesianPoint3.rule3Coplanarity, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, leftEndpoint, rightEndpoint,
      leftFirst, rightFirst]
  · norm_num [CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, leftEndpoint, rightEndpoint,
      leftFirst, rightFirst]

/-- **Nonvacuity**: one ready reference pairing plus the two planar opposite-side arms yields all
four actual candidate pairings. -/
theorem allCandidatePairsReady :
    CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftFirst rightFirst ∧
      CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftFirst rightSecond ∧
      CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftSecond rightFirst ∧
      CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftSecond rightSecond :=
  CartesianPoint3.rule3ReferencePairReady_candidatePairs leftEndpoint rightEndpoint
    leftFirst leftSecond rightFirst rightSecond 1 0 1 0 (by norm_num) (by norm_num)
    referencePairReady leftArm rightArm

/-- The left-endpoint common-plane condition holds for the certified difluoroethene coordinates:
all six atoms lie in the plane `z = 0`, both reference arms are noncollinear with the axis, and the
left reference and its alternative have opposite exact side normals. -/
theorem planarLeft :
    CartesianPoint3.PlanarFourSubstituentOppositeSideLeft leftEndpoint rightEndpoint
      leftFirst leftSecond rightFirst rightSecond := by
  unfold CartesianPoint3.PlanarFourSubstituentOppositeSideLeft
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hx := congrArg RationalVector3.x hzero
    norm_num [CartesianPoint3.displacement, leftEndpoint, rightEndpoint] at hx
  · intro hzero
    have hz := congrArg RationalVector3.z hzero
    norm_num [CartesianPoint3.displacement, RationalVector3.cross, leftEndpoint,
      rightEndpoint, rightFirst] at hz
  · intro hzero
    have hz := congrArg RationalVector3.z hzero
    norm_num [CartesianPoint3.displacement, RationalVector3.cross, leftEndpoint,
      rightEndpoint, leftFirst] at hz
  · norm_num [CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross,
      leftEndpoint, rightEndpoint, leftFirst, leftSecond, rightFirst, rightSecond]
  · norm_num [CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross,
      leftEndpoint, rightEndpoint, leftFirst, leftSecond, rightFirst, rightSecond]
  · norm_num [CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross,
      leftEndpoint, rightEndpoint, leftFirst, leftSecond, rightFirst, rightSecond]
  · norm_num [CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross,
      leftEndpoint, rightEndpoint, leftFirst, leftSecond, rightFirst, rightSecond]

/-- The right-endpoint common-plane condition holds for the same certified coordinates. -/
theorem planarRight :
    CartesianPoint3.PlanarFourSubstituentOppositeSideRight leftEndpoint rightEndpoint
      leftFirst leftSecond rightFirst rightSecond := by
  unfold CartesianPoint3.PlanarFourSubstituentOppositeSideRight
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hx := congrArg RationalVector3.x hzero
    norm_num [CartesianPoint3.displacement, leftEndpoint, rightEndpoint] at hx
  · intro hzero
    have hz := congrArg RationalVector3.z hzero
    norm_num [CartesianPoint3.displacement, RationalVector3.cross, leftEndpoint,
      rightEndpoint, leftFirst] at hz
  · intro hzero
    have hz := congrArg RationalVector3.z hzero
    norm_num [CartesianPoint3.displacement, RationalVector3.cross, leftEndpoint,
      rightEndpoint, rightFirst] at hz
  · norm_num [CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross,
      leftEndpoint, rightEndpoint, leftFirst, leftSecond, rightFirst, rightSecond]
  · norm_num [CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross,
      leftEndpoint, rightEndpoint, leftFirst, leftSecond, rightFirst, rightSecond]
  · norm_num [CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross,
      leftEndpoint, rightEndpoint, leftFirst, leftSecond, rightFirst, rightSecond]
  · norm_num [CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross,
      leftEndpoint, rightEndpoint, leftFirst, leftSecond, rightFirst, rightSecond]

/-- **Nonvacuity of the stronger common-plane condition.**  The certified difluoroethene coordinates
satisfy both four-substituent common-plane conditions, so all four pairings are ready from atom
coordinates alone, with no arm relation assumed. -/
theorem allCandidatePairsReadyOfPlanarCoordinates :
    CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftFirst rightFirst ∧
      CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftFirst rightSecond ∧
      CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftSecond rightFirst ∧
      CartesianPoint3.Rule3ReferencePairReady leftEndpoint rightEndpoint leftSecond rightSecond :=
  CartesianPoint3.rule3ReferencePairReady_candidatePairs_of_planarFourSubstituent
    leftEndpoint rightEndpoint leftFirst leftSecond rightFirst rightSecond
    planarLeft planarRight referencePairReady

/-- The reference pairing is classified as `seqcis` by the exact spatial classifier. -/
theorem referencePairCis :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftFirst rightFirst =
      some OfficialRule3Geometry.seqcis := by
  rw [rule3GeometryOfSpatialReferences?_eq_some_iff]
  constructor
  · norm_num [CartesianPoint3.rule3Coplanarity, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, leftEndpoint, rightEndpoint,
      leftFirst, rightFirst]
  · norm_num [CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, leftEndpoint, rightEndpoint,
      leftFirst, rightFirst]

/-- The cross pairing (left reference with the opposite-side right arm) is classified as
`seqtrans`; the four-pair domain is therefore not a vacuous same-side-only statement. -/
theorem crossPairTrans :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftFirst rightSecond =
      some OfficialRule3Geometry.seqtrans := by
  rw [rule3GeometryOfSpatialReferences?_eq_some_iff]
  constructor
  · norm_num [CartesianPoint3.rule3Coplanarity, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, leftEndpoint, rightEndpoint,
      leftFirst, rightSecond]
  · norm_num [CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
      RationalVector3.dot, RationalVector3.cross, leftEndpoint, rightEndpoint,
      leftFirst, rightSecond]

/-- Every one of the four candidate pairings is accepted by the exact classifier. -/
theorem allCandidatePairsClassified :
    (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftFirst rightFirst).isSome ∧
      (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftFirst rightSecond).isSome ∧
      (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftSecond rightFirst).isSome ∧
      (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftSecond rightSecond).isSome := by
  exact ⟨
    CartesianPoint3.rule3GeometryOfSpatialReferences?_isSome_of_pairReady _ _ _ _
      allCandidatePairsReady.1,
    CartesianPoint3.rule3GeometryOfSpatialReferences?_isSome_of_pairReady _ _ _ _
      allCandidatePairsReady.2.1,
    CartesianPoint3.rule3GeometryOfSpatialReferences?_isSome_of_pairReady _ _ _ _
      allCandidatePairsReady.2.2.1,
    CartesianPoint3.rule3GeometryOfSpatialReferences?_isSome_of_pairReady _ _ _ _
      allCandidatePairsReady.2.2.2⟩

end PlanarDifluoroetheneExample

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.Rule3ReferencePairReady
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3GeometryOfSpatialReferences?_isSome_of_pairReady
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3ReferencePairReady_exchangeRight
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3ReferencePairReady_exchangeLeft
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3ReferencePairReady_candidatePairs
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3Coplanarity_sideProduct_doubleExchange
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3ReferencePairReady_candidatePairs_of_planarFourSubstituent
assert_kernel_only TetraStereo.OneCenter.RationalVector3.OppositeSideArm.symm
assert_kernel_only TetraStereo.OneCenter.RationalVector3.OppositeSideArms
assert_kernel_only TetraStereo.OneCenter.RationalVector3.oppositeSideArms_comm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3AxisCoordinateGeometryReady
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3AxisCandidateGeometryReadiness_of_coordinateGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3AxisCoordinateGeometryDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3AxisCoordinateGeometryDomainAll
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodeConditionalGeometryDomain_of_axisCoordinateGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometryAll
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.leftArm
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.rightArm
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.referencePairReady
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.allCandidatePairsReady
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.planarLeft
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.planarRight
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.allCandidatePairsReadyOfPlanarCoordinates
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.referencePairCis
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.crossPairTrans
assert_kernel_only TetraStereo.OneCenter.PlanarDifluoroetheneExample.allCandidatePairsClassified
