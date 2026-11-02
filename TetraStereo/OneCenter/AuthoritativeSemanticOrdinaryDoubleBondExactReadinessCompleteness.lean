import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondWholeMoleculeAnalysis
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule45Exact
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CanonicalFrameExact

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact ordinary-double-bond readiness and refusal

This module characterizes deterministic endpoint-frame normalization through exact canonical
relations and composes it with the independent chemical judgments already proved exact for
endpoint Rule 5, source coordinates, rational planar geometry, and the final `Z`/`E` or
`seqCis`/`seqTrans` outcome.

The endpoint normal form replaces both the complete recursive Rule-3 frame computation and the
recursive Rules-4a--5 computation by independently defined canonical derivations.  Rule 3's leaf
relation still exposes the source spatial-unit observation; traversal, sibling ordering, physical
topology resolution, and common-unit exclusion are all relational.  This gives a
necessary-and-sufficient per-bond contract and, consequently, exact whole-family readiness,
refusal, uniqueness, and count-one theorems.
-/

/-- Canonical meaning of one compiled endpoint key.  Both the recursive Rule-3 key and the full
recursive Rules-4a--5 half are stated relationally. -/
def CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalOccurrenceRule3Through5Key) : Prop :=
  source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
      excluded fuel cursor key.rule3 ∧
    source.CanonicalAromaticCanonicalRerootCompoundRule45Key
      target view fuel cursor key.rule45

/-- One through-Rule-5 endpoint key succeeds exactly on its canonical source derivation. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalOccurrenceRule3Through5Key) :
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
        excluded target view fuel cursor = some key ↔
      source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
        excluded target view fuel cursor key := by
  constructor
  · intro computed
    unfold buildAromaticCanonicalOccurrenceRule3Through5KeyExcept? at computed
    cases rule3Computed : source.buildAromaticCanonicalRule3SpatialKeyExcept?
        excluded fuel cursor with
    | none => simp [rule3Computed] at computed
    | some rule3 =>
        cases rule45Computed : source.buildAromaticCanonicalRerootCompoundRule45Key?
            target view fuel cursor with
        | none => simp [rule3Computed, rule45Computed] at computed
        | some rule45 =>
            simp [rule3Computed, rule45Computed] at computed
            subst key
            exact ⟨
              (source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
                excluded fuel cursor rule3).mp rule3Computed,
              (source.buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
                target view fuel cursor rule45).mp rule45Computed⟩
  · rintro ⟨rule3Derived, rule45Derived⟩
    have rule3Computed :=
      (source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
        excluded fuel cursor key.rule3).mpr rule3Derived
    have rule45Computed :=
      (source.buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
        target view fuel cursor key.rule45).mpr rule45Derived
    simp [buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?,
      rule3Computed, rule45Computed]

/-- The canonical endpoint key refines the broad Rules-1a--5 chemical semantics. -/
theorem CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept.sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalOccurrenceRule3Through5Key)
    (canonical : source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
      excluded target view fuel cursor key) :
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
      excluded target view fuel cursor key := by
  exact ⟨
    source.buildAromaticCanonicalRule3SpatialKeyExcept?_sound
      excluded fuel cursor key.rule3
      ((source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
        excluded fuel cursor key.rule3).mpr canonical.1),
    canonical.2.sound⟩

/-- Pointwise endpoint-key compilation is exactly the canonical pointwise relation. -/
theorem mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) :
    ∀ cursors keys,
      cursors.mapM (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
          excluded target view fuel) = some keys ↔
        List.Forall₂
          (source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
            excluded target view fuel) cursors keys
  | [], keys => by
      constructor
      · intro computed
        simp at computed
        subst keys
        exact .nil
      · intro derived
        cases derived
        rfl
  | cursor :: cursors, keys => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases headComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            excluded target view fuel cursor with
        | none => simp [headComputed] at computed
        | some head =>
            cases tailComputed : cursors.mapM
                (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
                  excluded target view fuel) with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst keys
                exact .cons
                  ((source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                    excluded target view fuel cursor head).mp headComputed)
                  ((source.mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                    excluded target view fuel cursors tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            rw [List.mapM_cons]
            rw [(source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
              excluded target view fuel _ _).mpr head]
            rw [(source.mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
              excluded target view fuel _ _).mpr tail]
            rfl

/-- Canonical normal form of an endpoint-wide Rules-1a--5 frame.  The cursor list is fixed by
the molecule; both the common Rule-3 frame and every aligned Rules-4a--5 key are certified by
exact source-canonical recursive relations. -/
def AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat)
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) : Prop :=
  frame.cursors = source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
      carrierFuel endpoint partner ∧
    source.CanonicalAromaticCanonicalRule3CanonicalKeyFrame
        evaluationFuel frame.cursors frame.rule3Frame ∧
    List.Forall₂
      (source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
        frame.rule3Frame.excluded
        (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
        view evaluationFuel)
      frame.cursors frame.keys

/-- The endpoint builder succeeds exactly on its canonical two-stage normal form. -/
theorem buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat)
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) :
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
        carrierFuel endpoint partner view evaluationFuel = some frame ↔
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
        carrierFuel endpoint partner view evaluationFuel frame := by
  classical
  constructor
  · intro computed
    unfold buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame? at computed
    let cursors := source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
      carrierFuel endpoint partner
    cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
        evaluationFuel cursors with
    | none => simp [cursors, rule3Computed] at computed
    | some rule3Frame =>
        cases keysComputed : cursors.mapM
            (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
              rule3Frame.excluded
              (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
              view evaluationFuel) with
        | none => simp [cursors, rule3Computed, keysComputed] at computed
        | some keys =>
            simp [cursors, rule3Computed, keysComputed] at computed
            subst frame
            exact ⟨rfl,
              (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
                evaluationFuel cursors rule3Frame).mp rule3Computed,
              (source.mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                rule3Frame.excluded
                (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
                view evaluationFuel cursors keys).mp keysComputed⟩
  · rintro ⟨cursorsEq, rule3Derived, keysDerived⟩
    have rule3Computed :=
      (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
        evaluationFuel frame.cursors frame.rule3Frame).mpr rule3Derived
    have keysComputed :=
      (source.mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
        frame.rule3Frame.excluded
        (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
        view evaluationFuel frame.cursors frame.keys).mpr keysDerived
    unfold buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
    rw [← cursorsEq]
    simp [rule3Computed, keysComputed]

/-- A canonical endpoint normal form still carries the full independent Rules-1a--5 meaning. -/
theorem AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame.sound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat)
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel)
    (canonical :
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
        carrierFuel endpoint partner view evaluationFuel frame) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel endpoint partner view evaluationFuel frame := by
  apply source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
  exact
    (source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_eq_some_iff_canonical
      carrierFuel endpoint partner view evaluationFuel frame).mpr canonical

/-- Exact implementation-level decomposition of automatic per-bond success. -/
def AromaticCanonicalOrdinaryDoubleBondAutomaticSpatialExecutableJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers ∧
    ∃ leftFrame rightFrame leftSelection rightSelection
        leftPoint rightPoint leftReferencePoint rightReferencePoint geometry outcome,
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) =
        some leftFrame ∧
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
          carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) =
        some rightFrame ∧
      source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? leftFrame =
        some leftSelection ∧
      source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? rightFrame =
        some rightSelection ∧
      source.aromaticCanonicalSpatialPointAt? bond.left = some leftPoint ∧
      source.aromaticCanonicalSpatialPointAt? bond.right = some rightPoint ∧
      source.aromaticCanonicalSpatialPointAt? leftSelection.reference =
        some leftReferencePoint ∧
      source.aromaticCanonicalSpatialPointAt? rightSelection.reference =
        some rightReferencePoint ∧
      rule3GeometryOfSpatialReferences? leftPoint rightPoint
          leftReferencePoint rightReferencePoint = some geometry ∧
      aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?
          leftSelection.enantiomorphic rightSelection.enantiomorphic geometry =
        some outcome ∧
      ({ bond
         leftReference := leftSelection.reference
         rightReference := rightSelection.reference
         geometry
         outcome } : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) = assignment

/-- The automatic executable succeeds exactly when all of its fallible boundaries succeed. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_executable
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
        carrierFuel bond leftView rightView = some assignment ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticSpatialExecutableJudgment
        carrierFuel bond leftView rightView assignment := by
  classical
  unfold aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
    AromaticCanonicalOrdinaryDoubleBondAutomaticSpatialExecutableJudgment
  by_cases owner : bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers <;>
    simp [owner, Option.bind_eq_some_iff]

/-- Canonical chemical meaning of an automatic per-bond result.  Endpoint frames use the exact
two-stage normal form; endpoint choice, coordinates, geometry, and descriptor outcome use their
independent declarative relations. -/
def AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers ∧
    ∃ leftFrame rightFrame leftSelection rightSelection
        leftPoint rightPoint leftReferencePoint rightReferencePoint geometry outcome,
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
          carrierFuel bond.left bond.right leftView (2 * (carrierFuel + 1)) leftFrame ∧
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5CanonicalFrame
          carrierFuel bond.right bond.left rightView (2 * (carrierFuel + 1)) rightFrame ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        leftFrame leftSelection ∧
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        rightFrame rightSelection ∧
      source.SemanticAromaticCanonicalSpatialPointAt bond.left leftPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt bond.right rightPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        leftSelection.reference leftReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        rightSelection.reference rightReferencePoint ∧
      RationalRule3SpatialGeometry leftPoint rightPoint
        leftReferencePoint rightReferencePoint geometry ∧
      AromaticCanonicalOrdinaryDoubleBondPlanarOutcomeJudgment
        leftSelection.enantiomorphic rightSelection.enantiomorphic geometry outcome ∧
      ({ bond
         leftReference := leftSelection.reference
         rightReference := rightSelection.reference
         geometry
         outcome } : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) = assignment

/-- The executable decomposition is equivalent to the canonical chemical judgment. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialExecutableJudgment_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.AromaticCanonicalOrdinaryDoubleBondAutomaticSpatialExecutableJudgment
        carrierFuel bond leftView rightView assignment ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
        carrierFuel bond leftView rightView assignment := by
  simp only [AromaticCanonicalOrdinaryDoubleBondAutomaticSpatialExecutableJudgment,
    AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment,
    source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_eq_some_iff_canonical,
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative,
    source.aromaticCanonicalSpatialPointAt?_eq_some_iff,
    rule3GeometryOfSpatialReferences?_eq_some_iff,
    aromaticCanonicalOrdinaryDoubleBondPlanarOutcome?_eq_some_iff]

/-- Necessary-and-sufficient per-bond theorem: emission is exactly the canonical endpoint,
selection, coordinate, rational-geometry, and descriptor judgment. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
        carrierFuel bond leftView rightView = some assignment ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
        carrierFuel bond leftView rightView assignment :=
  (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_executable
    carrierFuel bond leftView rightView assignment).trans
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialExecutableJudgment_iff_canonical
        carrierFuel bond leftView rightView assignment)

/-- The exact canonical judgment entails the pre-existing fully independent positive judgment. -/
theorem AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment.sound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (canonical :
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
        carrierFuel bond leftView rightView assignment) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment
      carrierFuel bond leftView rightView assignment := by
  rcases canonical with ⟨owner, leftFrame, rightFrame, leftSelection, rightSelection,
    leftPoint, rightPoint, leftReferencePoint, rightReferencePoint, geometry, outcome,
    leftFrameCanonical, rightFrameCanonical, leftSelectionDerived,
    rightSelectionDerived, leftPointDerived, rightPointDerived,
    leftReferencePointDerived, rightReferencePointDerived, geometryDerived,
    outcomeDerived, assignmentEq⟩
  subst assignment
  exact ⟨rfl, owner, leftFrame, rightFrame, leftSelection, rightSelection,
    leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
    leftFrameCanonical.sound, rightFrameCanonical.sound,
    leftSelectionDerived, rightSelectionDerived, rfl, rfl,
    leftPointDerived, rightPointDerived, leftReferencePointDerived,
    rightReferencePointDerived, geometryDerived, outcomeDerived⟩

/-- Minimal exact readiness: there exists precisely the canonical chemical judgment compiled by
the per-bond analyzer. -/
def AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) : Prop :=
  ∃ assignment,
    source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
      carrierFuel bond leftView rightView assignment

/-- Per-bond success is exactly canonical chemical readiness. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_isSome_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
      carrierFuel bond leftView rightView).isSome = true ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
        carrierFuel bond leftView rightView := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
      carrierFuel bond leftView rightView assignment

/-- Per-bond refusal is exactly the negation of canonical chemical readiness. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_none_iff_not_ready
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
        carrierFuel bond leftView rightView = none ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
        carrierFuel bond leftView rightView := by
  constructor
  · intro refused ⟨assignment, canonical⟩
    have emitted :=
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
        carrierFuel bond leftView rightView assignment).mpr canonical
    rw [refused] at emitted
    contradiction
  · intro notReady
    cases computed : source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
        carrierFuel bond leftView rightView with
    | none => rfl
    | some assignment =>
        exact False.elim (notReady ⟨assignment,
          (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
            carrierFuel bond leftView rightView assignment).mp computed⟩)

/-- Whole-family membership is exactly existence of a canonical per-bond judgment. -/
theorem mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
        carrierFuel viewAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
          carrierFuel bond (viewAt bond.left) (viewAt bond.right) assignment := by
  rw [source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff]
  constructor
  · rintro ⟨bond, _owner, computed⟩
    exact ⟨bond,
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
        carrierFuel bond (viewAt bond.left) (viewAt bond.right) assignment).mp computed⟩
  · rintro ⟨bond, canonical⟩
    exact ⟨bond, canonical.1,
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
        carrierFuel bond (viewAt bond.left) (viewAt bond.right) assignment).mpr canonical⟩

/-- Existence of a whole-family result for one physical bond is equivalent to the exact
per-bond readiness relation. -/
theorem exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃ assignment,
        assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
            carrierFuel viewAt ∧
          assignment.bond = bond) ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
        carrierFuel bond (viewAt bond.left) (viewAt bond.right) := by
  constructor
  · rintro ⟨assignment, present, assignmentBond⟩
    obtain ⟨origin, canonical⟩ :=
      (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_canonical
        carrierFuel viewAt assignment).mp present
    have originIdentity : origin = bond := by
      exact canonical.sound.1.symm.trans assignmentBond
    subst origin
    exact ⟨assignment, canonical⟩
  · rintro ⟨assignment, canonical⟩
    refine ⟨assignment, ?_, canonical.sound.1⟩
    exact
      (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_canonical
        carrierFuel viewAt assignment).mpr ⟨bond, canonical⟩

/-- Exact readiness is equivalent to unique whole-family occurrence by retained physical-bond
identity. -/
theorem existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃! assignment,
        assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
            carrierFuel viewAt ∧
          assignment.bond = bond) ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
        carrierFuel bond (viewAt bond.left) (viewAt bond.right) := by
  constructor
  · rintro ⟨assignment, property, _unique⟩
    exact
      (source.exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_readiness
        carrierFuel viewAt bond).mp ⟨assignment, property⟩
  · intro ready
    obtain ⟨assignment, assignmentPresent, assignmentBond⟩ :=
      (source.exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_readiness
        carrierFuel viewAt bond).mpr ready
    refine ⟨assignment, ⟨assignmentPresent, assignmentBond⟩, ?_⟩
    intro other ⟨otherPresent, otherBond⟩
    obtain ⟨assignmentOrigin, _assignmentOwner, assignmentComputed⟩ :=
      (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff
        carrierFuel viewAt assignment).mp assignmentPresent
    obtain ⟨otherOrigin, _otherOwner, otherComputed⟩ :=
      (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff
        carrierFuel viewAt other).mp otherPresent
    have assignmentCanonical :=
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
        carrierFuel assignmentOrigin (viewAt assignmentOrigin.left)
          (viewAt assignmentOrigin.right) assignment).mp assignmentComputed
    have otherCanonical :=
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
        carrierFuel otherOrigin (viewAt otherOrigin.left)
          (viewAt otherOrigin.right) other).mp otherComputed
    have assignmentOriginIdentity : assignmentOrigin = bond :=
      assignmentCanonical.sound.1.symm.trans assignmentBond
    have otherOriginIdentity : otherOrigin = bond :=
      otherCanonical.sound.1.symm.trans otherBond
    subst assignmentOrigin
    subst otherOrigin
    rw [assignmentComputed] at otherComputed
    exact Option.some.inj otherComputed.symm

/-- Literal count-one coverage of one physical bond is equivalent to exact readiness. -/
theorem exists_count_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_eq_one_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
            carrierFuel viewAt).count assignment = 1) ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
        carrierFuel bond (viewAt bond.left) (viewAt bond.right) := by
  constructor
  · rintro ⟨assignment, assignmentBond, countOne⟩
    apply
      (source.exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_readiness
        carrierFuel viewAt bond).mp
    refine ⟨assignment, ?_, assignmentBond⟩
    exact List.count_pos_iff.mp (by omega)
  · intro ready
    obtain ⟨assignment, property, _unique⟩ :=
      (source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_readiness
        carrierFuel viewAt bond).mpr ready
    refine ⟨assignment, property.2, ?_⟩
    rw [(source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_nodup
      carrierFuel viewAt).count]
    simp [property.1]

/-- Whole-molecule exact classification: every canonical individual bond either has its unique
count-one canonical assignment or is refused precisely because its per-bond readiness is false. -/
theorem every_aromaticCanonicalOrdinaryDoubleBond_exact_readiness_or_refusal
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
          carrierFuel bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
              carrierFuel viewAt ∧
            assignment.bond = bond) ∨
      (¬ source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
          carrierFuel bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
          carrierFuel bond (viewAt bond.left) (viewAt bond.right) = none) := by
  intro bond _owner
  by_cases ready :
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
        carrierFuel bond (viewAt bond.left) (viewAt bond.right)
  · exact Or.inl ⟨ready,
      (source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_readiness
        carrierFuel viewAt bond).mpr ready⟩
  · exact Or.inr ⟨ready,
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_none_iff_not_ready
        carrierFuel bond (viewAt bond.left) (viewAt bond.right)).mpr ready⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
