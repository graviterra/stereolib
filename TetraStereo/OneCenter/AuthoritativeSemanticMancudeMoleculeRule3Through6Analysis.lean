import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Scheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Molecule-level source-canonical analysis through Rule 6

This module removes the remaining manually supplied objects from the source Rule-3--6 endpoint.
For every perceived four-coordinate source center it constructs the final occurrence, its ordered
reroot ligand frame, the dependency view decoded from the causal fixed point, and the exact
tetrahedral input parity obtained from source coordinates.  The analyzer remains parameterized by
the occurrence evaluator: chemically completing that evaluator is a separate, explicit proof
obligation rather than hidden data in this bridge.
-/

/-! ## Exact geometry-to-parity bridge -/

/-- A source coordinate attached to a real (not duplicate or placeholder) reroot node. -/
def DeclarativeAromaticCanonicalRerootSpatialPoint
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (point : CartesianPoint3) : Prop :=
  ∃ atom : source.AromaticCanonicalAtom,
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      cursor.occurrence.1.node.current? = some atom ∧
      source.aromaticCanonicalSpatialPointAt? atom = some point

/-- Fail-closed coordinate lookup for a real reroot node.  Duplicate and phantom positions do not
borrow the coordinates of their representative atom. -/
def aromaticCanonicalRerootSpatialPoint?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option CartesianPoint3 :=
  if cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
    cursor.occurrence.1.node.current?.bind source.aromaticCanonicalSpatialPointAt?
  else none

theorem aromaticCanonicalRerootSpatialPoint?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (point : CartesianPoint3) :
    source.aromaticCanonicalRerootSpatialPoint? cursor = some point ↔
      source.DeclarativeAromaticCanonicalRerootSpatialPoint cursor point := by
  unfold aromaticCanonicalRerootSpatialPoint?
    DeclarativeAromaticCanonicalRerootSpatialPoint
  by_cases real : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom
  · simp only [if_pos real]
    cases current : cursor.occurrence.1.node.current? with
    | none => simp
    | some atom => simp [real]
  · simp [real]

/-- Exact geometric meaning of the written-order parity used by the Rule-6 descriptor algebra,
under the standard right-handed Cartesian frame (`x` right, `y` up, `z` toward the viewer).  In
that frame a written-order affine determinant with the fourth position remote is negative for a
`clockwise` run of the first three positions and positive for an `anticlockwise` run; zero volume
has no parity. -/
def RationalTetrahedralInputParity
    (points : List CartesianPoint3) (parity : TetrahedralInputParity) : Prop :=
  ∃ first second third fourth,
    points = [first, second, third, fourth] ∧
      match parity with
      | .clockwise =>
          CartesianPoint3.orientedVolume first second third fourth < 0
      | .anticlockwise =>
          0 < CartesianPoint3.orientedVolume first second third fourth

/-- Exact rational geometry-to-parity computation.  Negative written-order volume is the
`clockwise` carrier and positive volume is the `anticlockwise` carrier; zero volume is refused. -/
def tetrahedralInputParityOfPoints? :
    List CartesianPoint3 → Option TetrahedralInputParity
  | [first, second, third, fourth] =>
      let volume := CartesianPoint3.orientedVolume first second third fourth
      if volume < 0 then some .clockwise
      else if 0 < volume then some .anticlockwise
      else none
  | _ => none

theorem tetrahedralInputParityOfPoints?_eq_some_iff
    (points : List CartesianPoint3) (parity : TetrahedralInputParity) :
    tetrahedralInputParityOfPoints? points = some parity ↔
      RationalTetrahedralInputParity points parity := by
  rcases points with _ | ⟨first, points⟩
  · simp [tetrahedralInputParityOfPoints?, RationalTetrahedralInputParity]
  rcases points with _ | ⟨second, points⟩
  · simp [tetrahedralInputParityOfPoints?, RationalTetrahedralInputParity]
  rcases points with _ | ⟨third, points⟩
  · simp [tetrahedralInputParityOfPoints?, RationalTetrahedralInputParity]
  rcases points with _ | ⟨fourth, points⟩
  · simp [tetrahedralInputParityOfPoints?, RationalTetrahedralInputParity]
  rcases points with _ | ⟨fifth, rest⟩
  · rcases lt_trichotomy
        (CartesianPoint3.orientedVolume first second third fourth) 0 with
      negative | zero | positive
    · have notPositive : ¬ 0 < CartesianPoint3.orientedVolume
          first second third fourth := not_lt_of_ge negative.le
      cases parity <;>
        simp [tetrahedralInputParityOfPoints?, RationalTetrahedralInputParity,
          negative, notPositive]
    · cases parity <;>
        simp [tetrahedralInputParityOfPoints?, RationalTetrahedralInputParity, zero]
    · have notNegative : ¬ CartesianPoint3.orientedVolume
          first second third fourth < 0 := not_lt_of_ge positive.le
      cases parity <;>
        simp [tetrahedralInputParityOfPoints?, RationalTetrahedralInputParity,
          positive, notNegative]
  · cases parity <;>
      simp [tetrahedralInputParityOfPoints?, RationalTetrahedralInputParity]

/-- Declarative source-coordinate and exact-volume meaning of a parity on an ordered root frame. -/
def DeclarativeAromaticCanonicalRerootFrameParity
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) : Prop :=
  ∃ points,
    List.Forall₂ source.DeclarativeAromaticCanonicalRerootSpatialPoint roots points ∧
      RationalTetrahedralInputParity points parity

/-- Compute the parity of the exact source coordinates in canonical root-frame order. -/
def aromaticCanonicalRerootFrameParity?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option TetrahedralInputParity := do
  let points ← roots.mapM source.aromaticCanonicalRerootSpatialPoint?
  tetrahedralInputParityOfPoints? points

private theorem mapM_aromaticCanonicalRerootSpatialPoint?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    ∀ (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (points : List CartesianPoint3),
      roots.mapM source.aromaticCanonicalRerootSpatialPoint? = some points →
        List.Forall₂ source.DeclarativeAromaticCanonicalRerootSpatialPoint roots points
  | [], points, computed => by
      simp at computed
      subst points
      exact .nil
  | root :: roots, points, computed => by
      rw [List.mapM_cons] at computed
      cases pointComputed : source.aromaticCanonicalRerootSpatialPoint? root with
      | none => simp [pointComputed] at computed
      | some point =>
          cases pointsComputed : roots.mapM source.aromaticCanonicalRerootSpatialPoint? with
          | none => simp [pointComputed, pointsComputed] at computed
          | some tail =>
              simp [pointComputed, pointsComputed] at computed
              subst points
              exact .cons
                ((source.aromaticCanonicalRerootSpatialPoint?_eq_some_iff
                  root point).mp pointComputed)
                (mapM_aromaticCanonicalRerootSpatialPoint?_sound
                  source roots tail pointsComputed)

private theorem mapM_aromaticCanonicalRerootSpatialPoint?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    ∀ (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (points : List CartesianPoint3),
      roots.mapM source.aromaticCanonicalRerootSpatialPoint? = some points ↔
        List.Forall₂ source.DeclarativeAromaticCanonicalRerootSpatialPoint roots points
  | [], points => by
      constructor
      · intro computed
        simp at computed
        subst points
        exact .nil
      · intro related
        cases related
        rfl
  | root :: roots, points => by
      constructor
      · exact mapM_aromaticCanonicalRerootSpatialPoint?_sound
          source (root :: roots) points
      · intro related
        obtain ⟨point, tailPoints, headRelated, tailRelated, rfl⟩ :=
          List.forall₂_cons_left_iff.mp related
        rw [List.mapM_cons,
          (source.aromaticCanonicalRerootSpatialPoint?_eq_some_iff
            root point).mpr headRelated,
          (mapM_aromaticCanonicalRerootSpatialPoint?_eq_some_iff
            source roots tailPoints).mpr tailRelated]
        rfl

theorem aromaticCanonicalRerootFrameParity?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity)
    (computed : source.aromaticCanonicalRerootFrameParity? roots = some parity) :
    source.DeclarativeAromaticCanonicalRerootFrameParity roots parity := by
  unfold aromaticCanonicalRerootFrameParity? at computed
  cases pointsComputed : roots.mapM source.aromaticCanonicalRerootSpatialPoint? with
  | none => simp [pointsComputed] at computed
  | some points =>
      refine ⟨points,
        mapM_aromaticCanonicalRerootSpatialPoint?_sound
          source roots points pointsComputed, ?_⟩
      exact (tetrahedralInputParityOfPoints?_eq_some_iff points parity).mp
        (by simpa [pointsComputed] using computed)

/-- Coordinate collection and determinant-sign classification are complete as well as sound:
the executable frame computation returns exactly the declaratively witnessed source parity. -/
theorem aromaticCanonicalRerootFrameParity?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) :
    source.aromaticCanonicalRerootFrameParity? roots = some parity ↔
      source.DeclarativeAromaticCanonicalRerootFrameParity roots parity := by
  constructor
  · exact source.aromaticCanonicalRerootFrameParity?_sound roots parity
  · rintro ⟨points, pointsDerived, inputParity⟩
    have pointsComputed :
        roots.mapM source.aromaticCanonicalRerootSpatialPoint? = some points :=
      (mapM_aromaticCanonicalRerootSpatialPoint?_eq_some_iff
        source roots points).mpr pointsDerived
    have parityComputed : tetrahedralInputParityOfPoints? points = some parity :=
      (tetrahedralInputParityOfPoints?_eq_some_iff points parity).mpr inputParity
    simp [aromaticCanonicalRerootFrameParity?, pointsComputed, parityComputed]

/-! ## Causally scheduled molecule endpoint -/

/-- The source occurrence state decoded from the complete causal scheduler closure. -/
noncomputable def aromaticCanonicalScheduledAuxiliaryState
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  DeclarativeCIP.OccurrenceScheduler.decode
    (source.aromaticCanonicalOccurrenceSystem semantics)
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (DeclarativeCIP.OccurrenceScheduler.closure
      (source.aromaticCanonicalOccurrenceSystem semantics)
      (@source.AromaticCanonicalDepthDependency carrierFuel))

theorem aromaticCanonicalScheduledAuxiliaryState_cipModel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel) :
    (source.aromaticCanonicalOccurrenceSystem semantics).CIPModel
      (source.aromaticCanonicalScheduledAuxiliaryState semantics) := by
  exact source.aromaticCanonicalSchedulerClosure_cipModel semantics

/-- Per-center molecule endpoint.  No target occurrence, root list, dependency view, or parity is
accepted from the caller. -/
noncomputable def aromaticCanonicalScheduledRule3Through6Descriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) : Option RS := do
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  let parity ← source.aromaticCanonicalRerootFrameParity? roots
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  source.aromaticCanonicalRule3Through6Descriptor? center.1 target
    (source.aromaticCanonicalDependencyView state target) ruleFuel roots parity

/-- Independent meaning of a molecule-level emitted descriptor. -/
def AromaticCanonicalScheduledRule3Through6DescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS) : Prop :=
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  ∃ roots parity,
    source.DeclarativeAromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } roots ∧
    source.DeclarativeAromaticCanonicalRerootFrameParity roots parity ∧
    source.AromaticCanonicalRule3Through6CompleteDescriptorJudgment center.1 target
      (source.aromaticCanonicalDependencyView state target) ruleFuel roots parity descriptor

/-- Every molecule-level emission has exact source-derived roots, exact rational geometry parity,
and the independently specified complete Rule-3--6 descriptor judgment. -/
theorem aromaticCanonicalScheduledRule3Through6Descriptor?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS)
    (computed : source.aromaticCanonicalScheduledRule3Through6Descriptor?
      semantics ruleFuel center = some descriptor) :
    source.AromaticCanonicalScheduledRule3Through6DescriptorJudgment
      semantics ruleFuel center descriptor := by
  unfold aromaticCanonicalScheduledRule3Through6Descriptor? at computed
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
  | none => simp [target, rootsComputed] at computed
  | some roots =>
      cases parityComputed : source.aromaticCanonicalRerootFrameParity? roots with
      | none => simp [target, rootsComputed, parityComputed] at computed
      | some parity =>
          let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
          have finalComputed : source.aromaticCanonicalRule3Through6Descriptor? center.1 target
              (source.aromaticCanonicalDependencyView state target) ruleFuel roots parity =
                some descriptor := by
            simpa [target, rootsComputed, parityComputed, state] using computed
          exact ⟨roots, parity,
            source.aromaticCanonicalOccurrenceLigandFrame?_sound
              target roots rootsComputed,
            source.aromaticCanonicalRerootFrameParity?_sound
              roots parity parityComputed,
            source.aromaticCanonicalRule3Through6Descriptor?_sound center.1 target
              (source.aromaticCanonicalDependencyView state target)
              ruleFuel roots parity descriptor finalComputed⟩

/-- One public source-indexed assignment from the complete scheduled route. -/
structure AromaticCanonicalScheduledRule3Through6Assignment
    (source : AuthoritativeChemicalInput) where
  center : source.AromaticCanonicalTetrahedralCenter
  descriptor : RS
  deriving DecidableEq

/-- Analyze every perceived four-coordinate source center in deterministic source order. -/
noncomputable def analyzeAromaticCanonicalScheduledRule3Through6
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) :
    List source.AromaticCanonicalScheduledRule3Through6Assignment :=
  source.aromaticCanonicalTetrahedralCenters.filterMap fun center =>
    (source.aromaticCanonicalScheduledRule3Through6Descriptor?
      semantics ruleFuel center).map fun descriptor => { center, descriptor }

theorem mem_analyzeAromaticCanonicalScheduledRule3Through6_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment) :
    assignment ∈ source.analyzeAromaticCanonicalScheduledRule3Through6 semantics ruleFuel ↔
      source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics ruleFuel assignment.center = some assignment.descriptor := by
  constructor
  · intro present
    rw [analyzeAromaticCanonicalScheduledRule3Through6, List.mem_filterMap] at present
    obtain ⟨center, _centerPresent, observed⟩ := present
    cases descriptorComputed : source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics ruleFuel center with
    | none => simp [descriptorComputed] at observed
    | some descriptor =>
        simp [descriptorComputed] at observed
        subst assignment
        exact descriptorComputed
  · intro emitted
    rw [analyzeAromaticCanonicalScheduledRule3Through6, List.mem_filterMap]
    refine ⟨assignment.center,
      (source.mem_aromaticCanonicalTetrahedralCenters_iff assignment.center).mpr
        assignment.center.2, ?_⟩
    simp [emitted]

/-- Every assignment in the whole-molecule list satisfies the molecule-level independent
judgment. -/
theorem analyzeAromaticCanonicalScheduledRule3Through6_member_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment)
    (present : assignment ∈
      source.analyzeAromaticCanonicalScheduledRule3Through6 semantics ruleFuel) :
    source.AromaticCanonicalScheduledRule3Through6DescriptorJudgment
      semantics ruleFuel assignment.center assignment.descriptor := by
  apply source.aromaticCanonicalScheduledRule3Through6Descriptor?_sound
  exact (source.mem_analyzeAromaticCanonicalScheduledRule3Through6_iff
    semantics ruleFuel assignment).mp present

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
