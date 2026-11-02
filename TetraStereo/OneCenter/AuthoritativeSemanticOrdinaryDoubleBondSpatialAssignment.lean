import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondEndpointRule5Parity

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source ordinary-double-bond spatial assignment

This module joins the exclusive individual-bond carrier, both occurrence-exact Rules-1a--5
endpoint selections, and exact rational geometry.  Rule-5 endpoint parity chooses the ordinary
`Z/E` family or the reflection-variant `seqCis/seqTrans` family.
-/

/-- Independent final outcome relation for exact rational together/opposite geometry and the
Rule-5 enantiomorphic status of the two endpoints. -/
def AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment
    (leftEnantiomorphic rightEnantiomorphic : Bool)
    (geometry : OfficialRule3Geometry) (outcome : StereoOutcome) : Prop :=
  match geometry with
  | .seqcis =>
      if leftEnantiomorphic != rightEnantiomorphic then
        outcome = StereoOutcome.enantiomorphicDoubleBond
          SequenceDoubleBondDescriptor.seqCis
      else outcome = StereoOutcome.alkene DoubleBondStereo.Z
  | .seqtrans =>
      if leftEnantiomorphic != rightEnantiomorphic then
        outcome = StereoOutcome.enantiomorphicDoubleBond
          SequenceDoubleBondDescriptor.seqTrans
      else outcome = StereoOutcome.alkene DoubleBondStereo.E
  | .nonstereogenic => False

/-- Executable transcription of the independent planar outcome relation. -/
def aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
    (leftEnantiomorphic rightEnantiomorphic : Bool) :
    OfficialRule3Geometry → Option StereoOutcome
  | .seqcis =>
      if leftEnantiomorphic != rightEnantiomorphic then
        some (StereoOutcome.enantiomorphicDoubleBond
          SequenceDoubleBondDescriptor.seqCis)
      else some (StereoOutcome.alkene DoubleBondStereo.Z)
  | .seqtrans =>
      if leftEnantiomorphic != rightEnantiomorphic then
        some (StereoOutcome.enantiomorphicDoubleBond
          SequenceDoubleBondDescriptor.seqTrans)
      else some (StereoOutcome.alkene DoubleBondStereo.E)
  | .nonstereogenic => none

theorem aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?_eq_some_iff
    (leftEnantiomorphic rightEnantiomorphic : Bool)
    (geometry : OfficialRule3Geometry) (outcome : StereoOutcome) :
    aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
        leftEnantiomorphic rightEnantiomorphic geometry = some outcome ↔
      AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment
        leftEnantiomorphic rightEnantiomorphic geometry outcome := by
  cases leftEnantiomorphic <;> cases rightEnantiomorphic <;>
    cases geometry <;> simp [aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?,
      AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment, eq_comm]

/-- One source-indexed planar assignment from the complete individual-double-bond route. -/
structure AromaticCanonicalOrdinaryDoubleBondSpatialAssignment
    (source : AuthoritativeChemicalInput) where
  bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier
  leftReference : source.AromaticCanonicalAtom
  rightReference : source.AromaticCanonicalAtom
  geometry : OfficialRule3Geometry
  outcome : StereoOutcome
  deriving DecidableEq

/-- Analyze one canonical physical bond only when the exclusive topology partition assigns it to
the individual-double-bond route. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (leftEnantiomorphic rightEnantiomorphic : Bool) :
    Option source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment := by
  classical
  exact
    if bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers then do
      let leftFrame ←
        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1))
      let rightFrame ←
        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1))
      let leftReference ←
        source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? leftFrame
      let rightReference ←
        source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? rightFrame
      let leftPoint ← source.aromaticCanonicalSpatialPointAt? bond.left
      let rightPoint ← source.aromaticCanonicalSpatialPointAt? bond.right
      let leftReferencePoint ← source.aromaticCanonicalSpatialPointAt? leftReference
      let rightReferencePoint ← source.aromaticCanonicalSpatialPointAt? rightReference
      let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
        leftReferencePoint rightReferencePoint
      let outcome ← aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
        leftEnantiomorphic rightEnantiomorphic geometry
      some { bond, leftReference, rightReference, geometry, outcome }
    else none

/-- The exact executable meaning of one successful ordinary-double-bond analysis.  Unlike the
independent chemical judgment below, this relation deliberately records every fallible boundary
of the implementation.  It is the kernel-checked success/refusal contract for the executable. -/
def AromaticCanonicalOrdinaryDoubleBondSpatialExecutableJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (leftEnantiomorphic rightEnantiomorphic : Bool)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers ∧
    ∃ leftFrame rightFrame leftReference rightReference
        leftPoint rightPoint leftReferencePoint rightReferencePoint geometry outcome,
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) =
        some leftFrame ∧
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) =
        some rightFrame ∧
      source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? leftFrame =
        some leftReference ∧
      source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? rightFrame =
        some rightReference ∧
      source.aromaticCanonicalSpatialPointAt? bond.left = some leftPoint ∧
      source.aromaticCanonicalSpatialPointAt? bond.right = some rightPoint ∧
      source.aromaticCanonicalSpatialPointAt? leftReference = some leftReferencePoint ∧
      source.aromaticCanonicalSpatialPointAt? rightReference = some rightReferencePoint ∧
      rule3GeometryOfSpatialReferences? leftPoint rightPoint
          leftReferencePoint rightReferencePoint = some geometry ∧
      aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
          leftEnantiomorphic rightEnantiomorphic geometry = some outcome ∧
      ({ bond, leftReference, rightReference, geometry, outcome } :
        source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) = assignment

/-- Exact success boundary for the executable ordinary-double-bond analyzer. -/
theorem aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_eq_some_iff
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (leftEnantiomorphic rightEnantiomorphic : Bool)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
        carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic =
          some assignment ↔
      source.AromaticCanonicalOrdinaryDoubleBondSpatialExecutableJudgment
        carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic assignment := by
  classical
  unfold aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
    AromaticCanonicalOrdinaryDoubleBondSpatialExecutableJudgment
  by_cases owner : bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers
  · rw [if_pos owner]
    constructor
    · intro computed
      cases leftFrameComputed :
          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
            carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) with
      | none => simp [leftFrameComputed] at computed
      | some leftFrame =>
        cases rightFrameComputed :
            source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
              carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) with
        | none => simp [leftFrameComputed, rightFrameComputed] at computed
        | some rightFrame =>
          cases leftReferenceComputed :
              source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? leftFrame with
          | none => simp [leftFrameComputed, rightFrameComputed,
              leftReferenceComputed] at computed
          | some leftReference =>
            cases rightReferenceComputed :
                source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? rightFrame with
            | none => simp [leftFrameComputed, rightFrameComputed,
                rightReferenceComputed] at computed
            | some rightReference =>
              cases leftPointComputed : source.aromaticCanonicalSpatialPointAt? bond.left with
              | none => simp [leftFrameComputed, rightFrameComputed,
                  leftPointComputed] at computed
              | some leftPoint =>
                cases rightPointComputed : source.aromaticCanonicalSpatialPointAt? bond.right with
                | none => simp [leftFrameComputed, rightFrameComputed,
                    leftPointComputed, rightPointComputed] at computed
                | some rightPoint =>
                  cases leftReferencePointComputed :
                      source.aromaticCanonicalSpatialPointAt? leftReference with
                  | none => simp [leftFrameComputed, rightFrameComputed,
                      leftReferenceComputed, rightReferenceComputed,
                      leftPointComputed, rightPointComputed,
                      leftReferencePointComputed] at computed
                  | some leftReferencePoint =>
                    cases rightReferencePointComputed :
                        source.aromaticCanonicalSpatialPointAt? rightReference with
                    | none => simp [leftFrameComputed, rightFrameComputed,
                        rightReferenceComputed,
                        leftPointComputed, rightPointComputed,
                        rightReferencePointComputed] at computed
                    | some rightReferencePoint =>
                      cases geometryComputed : rule3GeometryOfSpatialReferences?
                          leftPoint rightPoint leftReferencePoint rightReferencePoint with
                      | none => simp [leftFrameComputed, rightFrameComputed,
                          leftReferenceComputed, rightReferenceComputed,
                          leftPointComputed, rightPointComputed,
                          leftReferencePointComputed, rightReferencePointComputed,
                          geometryComputed] at computed
                      | some geometry =>
                        cases outcomeComputed :
                            aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
                              leftEnantiomorphic rightEnantiomorphic geometry with
                        | none => simp [leftFrameComputed, rightFrameComputed,
                            leftReferenceComputed, rightReferenceComputed,
                            leftPointComputed, rightPointComputed,
                            leftReferencePointComputed, rightReferencePointComputed,
                            geometryComputed, outcomeComputed] at computed
                        | some outcome =>
                          have finalEq :
                              ({ bond, leftReference, rightReference, geometry, outcome } :
                                source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) =
                                assignment := by
                            simpa [leftFrameComputed, rightFrameComputed,
                              leftReferenceComputed, rightReferenceComputed,
                              leftPointComputed, rightPointComputed,
                              leftReferencePointComputed, rightReferencePointComputed,
                              geometryComputed, outcomeComputed] using computed
                          exact ⟨owner, leftFrame, rightFrame, leftReference, rightReference,
                            leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
                            geometry, outcome, rfl, rfl, leftReferenceComputed,
                            rightReferenceComputed, rfl, rfl,
                            leftReferencePointComputed,
                            rightReferencePointComputed,
                            geometryComputed, outcomeComputed, finalEq⟩
    · rintro ⟨_, leftFrame, rightFrame, leftReference, rightReference,
        leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
        geometry, outcome, leftFrameComputed, rightFrameComputed,
        leftReferenceComputed, rightReferenceComputed,
        leftPointComputed, rightPointComputed,
        leftReferencePointComputed, rightReferencePointComputed,
        geometryComputed, outcomeComputed, finalEq⟩
      subst assignment
      simp [leftFrameComputed, rightFrameComputed,
        leftReferenceComputed, rightReferenceComputed,
        leftPointComputed, rightPointComputed,
        leftReferencePointComputed, rightReferencePointComputed,
        geometryComputed, outcomeComputed]
  · simp [owner]

/-- Exact readiness of the executable ordinary-double-bond pipeline. -/
def AromaticCanonicalOrdinaryDoubleBondSpatialExecutableReady
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (leftEnantiomorphic rightEnantiomorphic : Bool) : Prop :=
  ∃ assignment, source.AromaticCanonicalOrdinaryDoubleBondSpatialExecutableJudgment
    carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic assignment

theorem aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_isSome_iff
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (leftEnantiomorphic rightEnantiomorphic : Bool) :
    (source.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
        carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic).isSome = true ↔
      source.AromaticCanonicalOrdinaryDoubleBondSpatialExecutableReady
        carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic := by
  rw [Option.isSome_iff_exists]
  exact ⟨fun ⟨assignment, computed⟩ =>
      ⟨assignment,
        (source.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_eq_some_iff
          carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic
          assignment).mp computed⟩,
    fun ⟨assignment, judgment⟩ =>
      ⟨assignment,
        (source.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_eq_some_iff
          carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic
          assignment).mpr judgment⟩⟩

/-- Exact refusal boundary: the analyzer returns `none` precisely when its complete recorded
executable precondition is absent. -/
theorem aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_eq_none_iff
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (leftEnantiomorphic rightEnantiomorphic : Bool) :
    source.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
        carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic = none ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondSpatialExecutableReady
        carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic := by
  rw [← not_iff_not]
  simp only [not_not]
  rw [← source.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_isSome_iff
    carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic]
  exact Option.ne_none_iff_isSome

/-- Independent positive meaning of a complete source ordinary-double-bond assignment. -/
def DeclarativeAromaticCanonicalOrdinaryDoubleBondSpatialAssignment
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (leftEnantiomorphic rightEnantiomorphic : Bool)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  assignment.bond = bond ∧
    bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers ∧
    ∃ leftFrame rightFrame leftCandidate rightCandidate
        leftPoint rightPoint leftReferencePoint rightReferencePoint,
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) leftFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) rightFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
        leftFrame.ranked leftCandidate ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
        rightFrame.ranked rightCandidate ∧
      leftCandidate.1.occurrence.1.node.current? = some assignment.leftReference ∧
      rightCandidate.1.occurrence.1.node.current? = some assignment.rightReference ∧
      source.SemanticAromaticCanonicalSpatialPointAt bond.left leftPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt bond.right rightPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        assignment.leftReference leftReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        assignment.rightReference rightReferencePoint ∧
      RationalRule3SpatialGeometry leftPoint rightPoint
        leftReferencePoint rightReferencePoint assignment.geometry ∧
      AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment
        leftEnantiomorphic rightEnantiomorphic assignment.geometry assignment.outcome

/-- Every emitted source assignment is owned by the individual route, uses independently derived
Rules-1a--5 strict endpoint maxima, and has exact rational geometry and descriptor-family parity. -/
theorem aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?_sound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (leftEnantiomorphic rightEnantiomorphic : Bool)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (computed : source.aromaticCanonicalOrdinaryDoubleBondSpatialAssignment?
      carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic =
        some assignment) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondSpatialAssignment
      carrierFuel bond leftView rightView leftEnantiomorphic rightEnantiomorphic assignment := by
  unfold aromaticCanonicalOrdinaryDoubleBondSpatialAssignment? at computed
  by_cases owner : bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers
  · rw [if_pos owner] at computed
    cases leftFrameComputed :
        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) with
    | none => simp [leftFrameComputed] at computed
    | some leftFrame =>
      cases rightFrameComputed :
          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
            carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) with
      | none => simp [leftFrameComputed, rightFrameComputed] at computed
      | some rightFrame =>
        cases leftReferenceComputed :
            source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? leftFrame with
        | none => simp [leftFrameComputed, rightFrameComputed,
            leftReferenceComputed] at computed
        | some leftReference =>
          cases rightReferenceComputed :
              source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? rightFrame with
          | none => simp [leftFrameComputed, rightFrameComputed,
              rightReferenceComputed] at computed
          | some rightReference =>
            cases leftPointComputed : source.aromaticCanonicalSpatialPointAt? bond.left with
            | none => simp [leftFrameComputed, rightFrameComputed,
                leftPointComputed] at computed
            | some leftPoint =>
              cases rightPointComputed : source.aromaticCanonicalSpatialPointAt? bond.right with
              | none => simp [leftFrameComputed, rightFrameComputed,
                  leftPointComputed, rightPointComputed] at computed
              | some rightPoint =>
                cases leftReferencePointComputed :
                    source.aromaticCanonicalSpatialPointAt? leftReference with
                | none => simp [leftFrameComputed, rightFrameComputed,
                    leftReferenceComputed, rightReferenceComputed,
                    leftPointComputed, rightPointComputed,
                    leftReferencePointComputed] at computed
                | some leftReferencePoint =>
                  cases rightReferencePointComputed :
                      source.aromaticCanonicalSpatialPointAt? rightReference with
                  | none => simp [leftFrameComputed, rightFrameComputed,
                      rightReferenceComputed,
                      leftPointComputed, rightPointComputed,
                      rightReferencePointComputed] at computed
                  | some rightReferencePoint =>
                    cases geometryComputed : rule3GeometryOfSpatialReferences?
                        leftPoint rightPoint leftReferencePoint rightReferencePoint with
                    | none => simp [leftFrameComputed, rightFrameComputed,
                        leftReferenceComputed, rightReferenceComputed,
                        leftPointComputed, rightPointComputed,
                        leftReferencePointComputed, rightReferencePointComputed,
                        geometryComputed] at computed
                    | some geometry =>
                      cases outcomeComputed :
                          aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
                            leftEnantiomorphic rightEnantiomorphic geometry with
                      | none => simp [leftFrameComputed, rightFrameComputed,
                          leftReferenceComputed, rightReferenceComputed,
                          leftPointComputed, rightPointComputed,
                          leftReferencePointComputed, rightReferencePointComputed,
                          geometryComputed, outcomeComputed] at computed
                      | some outcome =>
                        simp [leftFrameComputed, rightFrameComputed,
                          leftReferenceComputed, rightReferenceComputed,
                          leftPointComputed, rightPointComputed,
                          leftReferencePointComputed, rightReferencePointComputed,
                          geometryComputed, outcomeComputed] at computed
                        subst assignment
                        have leftFrameDerived :=
                          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
                            carrierFuel bond.left bond.right leftView
                            (2 * (carrierFuel + 1)) leftFrame leftFrameComputed
                        have rightFrameDerived :=
                          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
                            carrierFuel bond.right bond.left rightView
                            (2 * (carrierFuel + 1)) rightFrame rightFrameComputed
                        obtain ⟨leftCandidate, leftSenior, leftCurrent, _⟩ :=
                          source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference?_sound
                            bond.left bond.right leftView (2 * (carrierFuel + 1))
                            leftFrame leftFrameDerived leftReference leftReferenceComputed
                        obtain ⟨rightCandidate, rightSenior, rightCurrent, _⟩ :=
                          source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference?_sound
                            bond.right bond.left rightView (2 * (carrierFuel + 1))
                            rightFrame rightFrameDerived rightReference rightReferenceComputed
                        exact ⟨rfl, owner, leftFrame, rightFrame,
                          leftCandidate, rightCandidate, leftPoint, rightPoint,
                          leftReferencePoint, rightReferencePoint,
                          leftFrameDerived, rightFrameDerived, leftSenior, rightSenior,
                          leftCurrent, rightCurrent,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            bond.left leftPoint).mp leftPointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            bond.right rightPoint).mp rightPointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            leftReference leftReferencePoint).mp leftReferencePointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            rightReference rightReferencePoint).mp rightReferencePointComputed,
                          (rule3GeometryOfSpatialReferences?_eq_some_iff
                            leftPoint rightPoint leftReferencePoint rightReferencePoint
                            geometry).mp geometryComputed,
                          (aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?_eq_some_iff
                            leftEnantiomorphic rightEnantiomorphic geometry outcome).mp
                              outcomeComputed⟩
  · simp [owner] at computed

/-! ## Fully automatic endpoint-Rule-5 assignment -/

/-- Analyze one ordinary double bond while deriving both endpoint Rule-5 parity bits from the
same occurrence-exact Rules-1a--5 frames used to select its reference atoms. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    Option source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment := by
  classical
  exact
    if bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers then do
      let leftFrame ←
        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1))
      let rightFrame ←
        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1))
      let leftSelection ←
        source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? leftFrame
      let rightSelection ←
        source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? rightFrame
      let leftPoint ← source.aromaticCanonicalSpatialPointAt? bond.left
      let rightPoint ← source.aromaticCanonicalSpatialPointAt? bond.right
      let leftReferencePoint ←
        source.aromaticCanonicalSpatialPointAt? leftSelection.reference
      let rightReferencePoint ←
        source.aromaticCanonicalSpatialPointAt? rightSelection.reference
      let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
        leftReferencePoint rightReferencePoint
      let outcome ← aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
        leftSelection.enantiomorphic rightSelection.enantiomorphic geometry
      some {
        bond
        leftReference := leftSelection.reference
        rightReference := rightSelection.reference
        geometry
        outcome
      }
    else none

/-- Independent positive meaning of the automatic per-bond result: both endpoint frames and
Rule-5 selections are independently justified, their reference atoms are used in exact rational
geometry, and their derived parity selects the final descriptor family. -/
def DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  assignment.bond = bond ∧
    bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers ∧
    ∃ leftFrame rightFrame leftSelection rightSelection
        leftPoint rightPoint leftReferencePoint rightReferencePoint,
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) leftFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) rightFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        leftFrame leftSelection ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        rightFrame rightSelection ∧
      assignment.leftReference = leftSelection.reference ∧
      assignment.rightReference = rightSelection.reference ∧
      source.SemanticAromaticCanonicalSpatialPointAt bond.left leftPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt bond.right rightPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        leftSelection.reference leftReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        rightSelection.reference rightReferencePoint ∧
      RationalRule3SpatialGeometry leftPoint rightPoint
        leftReferencePoint rightReferencePoint assignment.geometry ∧
      AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment
        leftSelection.enantiomorphic rightSelection.enantiomorphic
        assignment.geometry assignment.outcome

/-- Every automatically emitted descriptor has independently derived endpoint Rules 1a--5,
Rule-5 parity, exact source coordinates, rational geometry, and final descriptor-family meaning. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_sound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (computed : source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
      carrierFuel bond leftView rightView = some assignment) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment
      carrierFuel bond leftView rightView assignment := by
  unfold aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment? at computed
  by_cases owner : bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers
  · rw [if_pos owner] at computed
    cases leftFrameComputed :
        source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) with
    | none => simp [leftFrameComputed] at computed
    | some leftFrame =>
      cases rightFrameComputed :
          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
            carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) with
      | none => simp [leftFrameComputed, rightFrameComputed] at computed
      | some rightFrame =>
        cases leftSelectionComputed :
            source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? leftFrame with
        | none => simp [leftFrameComputed, rightFrameComputed,
            leftSelectionComputed] at computed
        | some leftSelection =>
          cases rightSelectionComputed :
              source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? rightFrame with
          | none => simp [leftFrameComputed, rightFrameComputed,
              rightSelectionComputed] at computed
          | some rightSelection =>
            cases leftPointComputed : source.aromaticCanonicalSpatialPointAt? bond.left with
            | none => simp [leftFrameComputed, rightFrameComputed,
                leftPointComputed] at computed
            | some leftPoint =>
              cases rightPointComputed : source.aromaticCanonicalSpatialPointAt? bond.right with
              | none => simp [leftFrameComputed, rightFrameComputed,
                  leftPointComputed, rightPointComputed] at computed
              | some rightPoint =>
                cases leftReferencePointComputed :
                    source.aromaticCanonicalSpatialPointAt? leftSelection.reference with
                | none => simp [leftFrameComputed, rightFrameComputed,
                    leftSelectionComputed, rightSelectionComputed,
                    leftPointComputed, rightPointComputed,
                    leftReferencePointComputed] at computed
                | some leftReferencePoint =>
                  cases rightReferencePointComputed :
                      source.aromaticCanonicalSpatialPointAt? rightSelection.reference with
                  | none => simp [leftFrameComputed, rightFrameComputed,
                      rightSelectionComputed,
                      leftPointComputed, rightPointComputed,
                      rightReferencePointComputed] at computed
                  | some rightReferencePoint =>
                    cases geometryComputed : rule3GeometryOfSpatialReferences?
                        leftPoint rightPoint leftReferencePoint rightReferencePoint with
                    | none => simp [leftFrameComputed, rightFrameComputed,
                        leftSelectionComputed, rightSelectionComputed,
                        leftPointComputed, rightPointComputed,
                        leftReferencePointComputed, rightReferencePointComputed,
                        geometryComputed] at computed
                    | some geometry =>
                      cases outcomeComputed :
                          aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
                            leftSelection.enantiomorphic rightSelection.enantiomorphic
                            geometry with
                      | none => simp [leftFrameComputed, rightFrameComputed,
                          leftSelectionComputed, rightSelectionComputed,
                          leftPointComputed, rightPointComputed,
                          leftReferencePointComputed, rightReferencePointComputed,
                          geometryComputed, outcomeComputed] at computed
                      | some outcome =>
                        simp [leftFrameComputed, rightFrameComputed,
                          leftSelectionComputed, rightSelectionComputed,
                          leftPointComputed, rightPointComputed,
                          leftReferencePointComputed, rightReferencePointComputed,
                          geometryComputed, outcomeComputed] at computed
                        subst assignment
                        have leftFrameDerived :=
                          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
                            carrierFuel bond.left bond.right leftView
                            (2 * (carrierFuel + 1)) leftFrame leftFrameComputed
                        have rightFrameDerived :=
                          source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
                            carrierFuel bond.right bond.left rightView
                            (2 * (carrierFuel + 1)) rightFrame rightFrameComputed
                        exact ⟨rfl, owner, leftFrame, rightFrame,
                          leftSelection, rightSelection,
                          leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
                          leftFrameDerived, rightFrameDerived,
                          source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_sound
                            leftFrame leftSelection leftSelectionComputed,
                          source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_sound
                            rightFrame rightSelection rightSelectionComputed,
                          rfl, rfl,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            bond.left leftPoint).mp leftPointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            bond.right rightPoint).mp rightPointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            leftSelection.reference leftReferencePoint).mp
                              leftReferencePointComputed,
                          (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                            rightSelection.reference rightReferencePoint).mp
                              rightReferencePointComputed,
                          (rule3GeometryOfSpatialReferences?_eq_some_iff
                            leftPoint rightPoint leftReferencePoint rightReferencePoint
                            geometry).mp geometryComputed,
                          (aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?_eq_some_iff
                            leftSelection.enantiomorphic rightSelection.enantiomorphic
                            geometry outcome).mp outcomeComputed⟩
  · simp [owner] at computed

/-- Chemically meaningful production evidence retained by automatic per-bond completeness.
Recursive Rules-1a--5 construction is discharged by the proved finite bound.  The remaining
premises say that each materialized two-ligand endpoint has a strict independent selection and
that the four selected source points define nondegenerate planar geometry. -/
structure AromaticCanonicalOrdinaryDoubleBondAutomaticDependencyEvidence
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) : Prop where
  owner : bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers
  leftDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel bond.left bond.right
  rightDependencies :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
      carrierFuel bond.right bond.left
  leftSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  rightSelectable : ∀ frame,
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) frame →
      ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection
  spatiallyNondegenerate :
    ∀ (leftFrame rightFrame :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
      (leftSelection rightSelection :
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel),
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        leftFrame leftSelection →
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        rightFrame rightSelection →
      ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint geometry,
        source.SemanticAromaticCanonicalSpatialPointAt bond.left leftPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt bond.right rightPoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          leftSelection.reference leftReferencePoint ∧
        source.SemanticAromaticCanonicalSpatialPointAt
          rightSelection.reference rightReferencePoint ∧
        RationalRule3SpatialGeometry leftPoint rightPoint
          leftReferencePoint rightReferencePoint geometry ∧
        geometry ≠ OfficialRule3Geometry.nonstereogenic

/-- Conditional chemical completeness of the fully automatic per-bond implementation.  No
recursive-builder success is assumed: the finite Rules-1a--5 frames are constructed from the
dependency evidence, independent endpoint selections are compiled by their exact iff theorems,
and independent rational geometry is compiled into a final assignment. -/
theorem exists_aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (evidence :
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticDependencyEvidence
        carrierFuel bond leftView rightView) :
    ∃ assignment,
      source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
        carrierFuel bond leftView rightView = some assignment := by
  obtain ⟨leftFrame, leftFrameComputed⟩ :=
    source.exists_buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame_at_twice
      carrierFuel bond.left bond.right leftView evidence.leftDependencies
  obtain ⟨rightFrame, rightFrameComputed⟩ :=
    source.exists_buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame_at_twice
      carrierFuel bond.right bond.left rightView evidence.rightDependencies
  have leftFrameDerived :=
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
      carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1))
      leftFrame leftFrameComputed
  have rightFrameDerived :=
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
      carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1))
      rightFrame rightFrameComputed
  obtain ⟨leftSelection, leftSelectionDerived⟩ :=
    evidence.leftSelectable leftFrame leftFrameDerived
  obtain ⟨rightSelection, rightSelectionDerived⟩ :=
    evidence.rightSelectable rightFrame rightFrameDerived
  have leftSelectionComputed :=
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
      leftFrame leftSelection).mpr leftSelectionDerived
  have rightSelectionComputed :=
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
      rightFrame rightSelection).mpr rightSelectionDerived
  obtain ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint, geometry,
      leftPointDerived, rightPointDerived, leftReferencePointDerived,
      rightReferencePointDerived, geometryDerived, geometryNondegenerate⟩ :=
    evidence.spatiallyNondegenerate leftFrame rightFrame leftSelection rightSelection
      leftSelectionDerived rightSelectionDerived
  have leftPointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff bond.left leftPoint).mpr
      leftPointDerived
  have rightPointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff bond.right rightPoint).mpr
      rightPointDerived
  have leftReferencePointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      leftSelection.reference leftReferencePoint).mpr leftReferencePointDerived
  have rightReferencePointComputed :=
    (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
      rightSelection.reference rightReferencePoint).mpr rightReferencePointDerived
  have geometryComputed :=
    (rule3GeometryOfSpatialReferences?_eq_some_iff
      leftPoint rightPoint leftReferencePoint rightReferencePoint geometry).mpr
        geometryDerived
  obtain ⟨outcome, outcomeComputed⟩ :
      ∃ outcome, aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
        leftSelection.enantiomorphic rightSelection.enantiomorphic geometry = some outcome := by
    cases geometry with
    | nonstereogenic => contradiction
    | seqcis =>
        cases leftSelection.enantiomorphic <;> cases rightSelection.enantiomorphic <;>
          simp [aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?]
    | seqtrans =>
        cases leftSelection.enantiomorphic <;> cases rightSelection.enantiomorphic <;>
          simp [aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?]
  refine ⟨{
      bond
      leftReference := leftSelection.reference
      rightReference := rightSelection.reference
      geometry
      outcome
    }, ?_⟩
  simp [aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?, evidence.owner,
    leftFrameComputed, rightFrameComputed, leftSelectionComputed, rightSelectionComputed,
    leftPointComputed, rightPointComputed,
    leftReferencePointComputed, rightReferencePointComputed,
    geometryComputed, outcomeComputed]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
