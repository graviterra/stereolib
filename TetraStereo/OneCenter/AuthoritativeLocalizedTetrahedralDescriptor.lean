import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact spatial descriptors for localized semantic tetrahedral centers

This module joins the executable semantic-molecule hierarchy to exact rational 3D evidence. It
computes handedness without a floating-point tolerance and proves that the rational determinant is
the same oriented volume used by the real-valued tetrahedral geometry theory.
-/

namespace CartesianPoint3

/-- Exact affine determinant of four rational points, written as the determinant of the three edge
rows anchored at the fourth point. -/
def orientedVolume (first second third fourth : CartesianPoint3) : ℚ :=
  let ax := first.x - fourth.x
  let ay := first.y - fourth.y
  let az := first.z - fourth.z
  let bx := second.x - fourth.x
  let byCoordinate := second.y - fourth.y
  let bz := second.z - fourth.z
  let cx := third.x - fourth.x
  let cy := third.y - fourth.y
  let cz := third.z - fourth.z
  ax * (byCoordinate * cz - bz * cy) - ay * (bx * cz - bz * cx) +
    az * (bx * cy - byCoordinate * cx)

/-- Exact conversion into the existing real Euclidean geometry theory. -/
noncomputable def toRealPoint (point : CartesianPoint3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(point.x : ℝ), (point.y : ℝ), (point.z : ℝ)]

/-- Four exact rational points viewed as the existing real tetrahedral geometry. -/
noncomputable def toRealTetrahedralGeometry
    (first second third fourth : CartesianPoint3) : TetrahedralGeometry where
  vertex
    | 0 => first.toRealPoint
    | 1 => second.toRealPoint
    | 2 => third.toRealPoint
    | 3 => fourth.toRealPoint

/-- The executable rational determinant is exactly the real affine determinant after embedding. -/
theorem orientedVolume_toRealTetrahedralGeometry
    (first second third fourth : CartesianPoint3) :
    TetrahedralGeometry.orientedVolume
        (toRealTetrahedralGeometry first second third fourth) =
      (orientedVolume first second third fourth : ℝ) := by
  rw [TetrahedralGeometry.orientedVolume_eq_edgeMatrix_det, Matrix.det_fin_three]
  simp [TetrahedralGeometry.edgeMatrix, toRealTetrahedralGeometry, toRealPoint,
    orientedVolume]
  ring

end CartesianPoint3

namespace CertifiedLocalizedCIPInput

/-- A spatial descriptor from an exact oriented volume.

Calibration (IUPAC P-92.1.2.1; preferred viewing side remote from the lowest-precedence ligand):
the four points are supplied in descending CIP priority order `1 > 2 > 3 > 4`.  With the standard
right-handed Cartesian frame (`x` right, `y` up, `z` toward the viewer), the `R` case -- the
highest-to-lowest path turning clockwise when viewed from the side remote from the lowest-priority
group -- has negative exact oriented volume.  Hence negative volume is `R` and positive volume is
`S`.  Zero is refused as degenerate evidence. -/
def descriptorOfOrientedVolume? (volume : ℚ) : Option RS :=
  if volume < 0 then some RS.R else if 0 < volume then some RS.S else none

@[simp] theorem descriptorOfOrientedVolume?_eq_some_R_iff (volume : ℚ) :
    descriptorOfOrientedVolume? volume = some RS.R ↔ volume < 0 := by
  by_cases negative : volume < 0
  · simp [descriptorOfOrientedVolume?, negative]
  · by_cases positive : 0 < volume
    · simp [descriptorOfOrientedVolume?, negative, positive]
    · simp [descriptorOfOrientedVolume?, negative, positive]

@[simp] theorem descriptorOfOrientedVolume?_eq_some_S_iff (volume : ℚ) :
    descriptorOfOrientedVolume? volume = some RS.S ↔ 0 < volume := by
  by_cases negative : volume < 0
  · have notPositive : ¬ 0 < volume := not_lt_of_ge negative.le
    simp [descriptorOfOrientedVolume?, negative, notPositive]
  · by_cases positive : 0 < volume
    · simp [descriptorOfOrientedVolume?, negative, positive]
    · simp [descriptorOfOrientedVolume?, negative, positive]

@[simp] theorem descriptorOfOrientedVolume?_eq_none_iff (volume : ℚ) :
    descriptorOfOrientedVolume? volume = none ↔ volume = 0 := by
  by_cases negative : volume < 0
  · simp [descriptorOfOrientedVolume?, negative, ne_of_lt negative]
  · by_cases positive : 0 < volume
    · simp [descriptorOfOrientedVolume?, negative, positive, ne_of_gt positive]
    · have zero : volume = 0 := le_antisymm (not_lt.mp positive) (not_lt.mp negative)
      simp [descriptorOfOrientedVolume?, zero]

/-- Safe exact coordinate lookup at a semantic atom. -/
def spatialPointAt? (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    Option CartesianPoint3 := do
  let spatial ← input.certified.input.spatial?
  spatial.positions[atom.val]?

/-- Direct semantic-coordinate relation, independent of the pipeline's monadic lookup wrapper. -/
def SemanticSpatialPointAt (input : CertifiedLocalizedCIPInput)
    (atom : input.Atom) (point : CartesianPoint3) : Prop :=
  ∃ spatial,
    input.certified.input.spatial? = some spatial ∧
    spatial.positions[atom.val]? = some point

theorem spatialPointAt?_eq_some_iff (input : CertifiedLocalizedCIPInput)
    (atom : input.Atom) (point : CartesianPoint3) :
    input.spatialPointAt? atom = some point ↔
      input.SemanticSpatialPointAt atom point := by
  unfold spatialPointAt? SemanticSpatialPointAt
  cases input.certified.input.spatial? <;> simp

/-- Exact points in descending executable official-CIP priority order. -/
def priorityOrderedSpatialPoints? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    Option (List CartesianPoint3) := do
  let priorityOrder ← input.ligandOrderAt? center context
  priorityOrder.mapM fun index =>
    input.spatialPointAt? (input.canonicalLigandAtom center index)

/-- Spatial points routed through the older proof-facing hierarchy API. This is an internal
reference implementation, not yet the independent IUPAC rule-major specification. -/
noncomputable def referencePriorityOrderedSpatialPoints?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    Option (List CartesianPoint3) := do
  let priorityOrder ←
    (input.detectedOneCenterMolecule center).cipOfficialOrder? context
  priorityOrder.mapM fun index =>
    input.spatialPointAt? (input.canonicalLigandAtom center index)

/-- The executable coordinate ordering is exactly the internal proof-facing ordering, including
tie refusal. -/
theorem priorityOrderedSpatialPoints?_eq_reference
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    input.priorityOrderedSpatialPoints? center context =
      input.referencePriorityOrderedSpatialPoints? center context := by
  unfold priorityOrderedSpatialPoints? referencePriorityOrderedSpatialPoints?
  rw [input.ligandOrderAt?_eq_reference center context]

/-- Safe exact tetrahedral `R/S` assignment. It refuses tied CIP priorities, absent coordinates,
out-of-range coordinates, and coplanar/degenerate four-point evidence. -/
def tetrahedralSpatialDescriptorAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Option RS := do
  let points ← input.priorityOrderedSpatialPoints? center context
  match points with
  | [first, second, third, fourth] =>
      descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume first second third fourth)
  | _ => none

/-- Geometry-only executable reading of an already priority-ordered point list. -/
def descriptorOfPriorityOrderedPoints? : List CartesianPoint3 → Option RS
  | [first, second, third, fourth] =>
      descriptorOfOrientedVolume?
        (CartesianPoint3.orientedVolume first second third fourth)
  | _ => none

/-- Exact semantic coordinates in the replacement exhaustive rule-major priority order. -/
def ruleMajorPriorityOrderedSpatialPoints? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    Option (List CartesianPoint3) := do
  let priorityOrder ← input.ruleMajorLigandOrderAt? center context
  priorityOrder.mapM fun index =>
    input.spatialPointAt? (input.canonicalLigandAtom center index)

/-- Safe spatial assignment using exhaustive Rule 1a → Rule 1b → Rule 2 branch keys. -/
def ruleMajorTetrahedralSpatialDescriptorAt? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Option RS := do
  let points ← input.ruleMajorPriorityOrderedSpatialPoints? center context
  descriptorOfPriorityOrderedPoints? points

/-- Independent geometry-side relation: four already priority-ordered rational points determine
`R` by negative affine determinant and `S` by positive affine determinant.  This is the exact
calibration of the IUPAC highest-to-lowest-path rule in the standard right-handed Cartesian
frame: `R` corresponds to a clockwise projected path when the lowest-priority point is away from
the viewer, which is negative oriented volume for points listed in descending priority order. -/
def RationalTetrahedralDescriptor (points : List CartesianPoint3) (descriptor : RS) : Prop :=
  ∃ first second third fourth,
    points = [first, second, third, fourth] ∧
      match descriptor with
      | RS.R => CartesianPoint3.orientedVolume first second third fourth < 0
      | RS.S => 0 < CartesianPoint3.orientedVolume first second third fourth

/-- Pointwise direct semantic coordinates for a proposed canonical-ligand priority order. -/
def DeclarativePrioritySpatialPoints (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (order : List (Fin 4)) (points : List CartesianPoint3) : Prop :=
  List.Forall₂
    (fun index point => input.SemanticSpatialPointAt
      (input.canonicalLigandAtom center index) point)
    order points

/-- Independent localized descriptor relation at the current Rules 3--5 context boundary. It
contains no executable sorter or descriptor-pipeline call: all four ligands occur once; every
earlier/later pair has a declarative recursive-expansion priority witness; coordinates come
directly from semantic input; and exact determinant sign fixes `R/S`. -/
def DeclarativeRuleMajorLocalizedTetrahedralDescriptor
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (descriptor : RS) : Prop :=
  ∃ order points,
    input.DeclarativeRuleMajorPriorityOrder center context order ∧
    input.DeclarativePrioritySpatialPoints center order points ∧
    RationalTetrahedralDescriptor points descriptor

/-- Reference relation for the replacement localized constitutional path. The priority component
is exhaustive and rule-major; its supplied Rule 3/4/5 contexts still require an independent
perception/refinement proof before this becomes a complete P-92 theorem. -/
def RuleMajorLocalizedTetrahedralDescriptor
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (descriptor : RS) : Prop :=
  ∃ points,
    input.ruleMajorPriorityOrderedSpatialPoints? center context = some points ∧
      RationalTetrahedralDescriptor points descriptor

/-- Internal localized tetrahedral reference relation: the proof-facing safe order selects four
exact semantic coordinates, whose affine sign determines the descriptor. The geometry clause is
independent; the priority clause still awaits refinement to the independent rule-major P-92 model. -/
def ReferenceLocalizedTetrahedralDescriptor
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (descriptor : RS) : Prop :=
  ∃ points,
    input.referencePriorityOrderedSpatialPoints? center context = some points ∧
      RationalTetrahedralDescriptor points descriptor

@[simp] theorem descriptorOfPriorityOrderedPoints?_eq_some_iff
    (points : List CartesianPoint3) (descriptor : RS) :
    descriptorOfPriorityOrderedPoints? points = some descriptor ↔
      RationalTetrahedralDescriptor points descriptor := by
  cases points with
  | nil => simp [descriptorOfPriorityOrderedPoints?, RationalTetrahedralDescriptor]
  | cons first rest =>
      cases rest with
      | nil => simp [descriptorOfPriorityOrderedPoints?, RationalTetrahedralDescriptor]
      | cons second rest =>
          cases rest with
          | nil => simp [descriptorOfPriorityOrderedPoints?, RationalTetrahedralDescriptor]
          | cons third rest =>
              cases rest with
              | nil => simp [descriptorOfPriorityOrderedPoints?, RationalTetrahedralDescriptor]
              | cons fourth rest =>
                  cases rest with
                  | cons fifth rest =>
                      simp [descriptorOfPriorityOrderedPoints?, RationalTetrahedralDescriptor]
                  | nil =>
                      cases descriptor with
                      | R =>
                          simp [descriptorOfPriorityOrderedPoints?,
                            RationalTetrahedralDescriptor]
                      | S =>
                          simp [descriptorOfPriorityOrderedPoints?,
                            RationalTetrahedralDescriptor]

/-! ### Source-calibration witnesses -/





theorem sourceCalibrationWitness_orientedVolume :
    CartesianPoint3.orientedVolume
      ⟨0, 1, 1⟩ ⟨1, -1, 1⟩ ⟨-1, -1, 1⟩ ⟨0, 0, -1⟩ = -8 := by
  norm_num [CartesianPoint3.orientedVolume]

/-- The negative-volume calibration witness is assigned `R`, as required by the standard
right-handed clockwise/`R` rule. -/
theorem sourceCalibrationWitness_descriptor :
    descriptorOfOrientedVolume?
      (CartesianPoint3.orientedVolume
        ⟨0, 1, 1⟩ ⟨1, -1, 1⟩ ⟨-1, -1, 1⟩ ⟨0, 0, -1⟩) = some RS.R := by
  rw [sourceCalibrationWitness_orientedVolume]
  exact (descriptorOfOrientedVolume?_eq_some_R_iff (-8)).mpr (by norm_num)

/-- The declarative independent geometry relation also assigns `R` to the same priority-ordered
negative-volume witness. -/
theorem sourceCalibrationWitness_rationalDescriptor :
    RationalTetrahedralDescriptor
      [⟨0, 1, 1⟩, ⟨1, -1, 1⟩, ⟨-1, -1, 1⟩, ⟨0, 0, -1⟩] RS.R := by
  refine ⟨⟨0, 1, 1⟩, ⟨1, -1, 1⟩, ⟨-1, -1, 1⟩, ⟨0, 0, -1⟩, rfl, ?_⟩
  rw [sourceCalibrationWitness_orientedVolume]
  norm_num

/-- Exact executable/reference boundary for the replacement rule-major localized path. -/
theorem ruleMajorTetrahedralSpatialDescriptorAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (descriptor : RS) :
    input.ruleMajorTetrahedralSpatialDescriptorAt? center context = some descriptor ↔
      RuleMajorLocalizedTetrahedralDescriptor input center context descriptor := by
  change
    (input.ruleMajorPriorityOrderedSpatialPoints? center context).bind
        descriptorOfPriorityOrderedPoints? = some descriptor ↔ _
  rw [Option.bind_eq_some_iff]
  apply exists_congr
  intro points
  rw [descriptorOfPriorityOrderedPoints?_eq_some_iff]

private theorem mapM_forall₂_semantic
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) :
    ∀ (order : List (Fin 4)) (points : List CartesianPoint3),
      order.mapM (fun index =>
        input.spatialPointAt? (input.canonicalLigandAtom center index)) = some points →
      input.DeclarativePrioritySpatialPoints center order points
  | [], points, computed => by
      simp at computed
      subst points
      exact List.Forall₂.nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases pointComputed : input.spatialPointAt?
          (input.canonicalLigandAtom center index) with
      | none =>
          rw [pointComputed] at computed
          contradiction
      | some point =>
          cases restComputed : order.mapM (fun next =>
              input.spatialPointAt? (input.canonicalLigandAtom center next)) with
          | none =>
              rw [pointComputed, restComputed] at computed
              contradiction
          | some rest =>
              rw [pointComputed, restComputed] at computed
              injection computed with identity
              subst points
              exact List.Forall₂.cons
                ((input.spatialPointAt?_eq_some_iff
                  (input.canonicalLigandAtom center index) point).mp pointComputed)
                (mapM_forall₂_semantic input center order rest restComputed)

/-- Every successfully assembled priority-point list has an independent declarative priority
order and direct semantic-coordinate witnesses. -/
theorem ruleMajorPriorityOrderedSpatialPoints?_sound_declarative
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (points : List CartesianPoint3)
    (computed : input.ruleMajorPriorityOrderedSpatialPoints? center context = some points) :
    ∃ order,
      input.DeclarativeRuleMajorPriorityOrder center context order ∧
      input.DeclarativePrioritySpatialPoints center order points := by
  unfold ruleMajorPriorityOrderedSpatialPoints? at computed
  cases orderComputed : input.ruleMajorLigandOrderAt? center context with
  | none => simp [orderComputed] at computed
  | some order =>
      simp only [orderComputed] at computed
      exact ⟨order,
        input.ruleMajorLigandOrderAt?_sound_declarative
          center context order orderComputed,
        mapM_forall₂_semantic input center order points computed⟩

/-- End-to-end localized soundness for the replacement path: every emitted `R/S` satisfies the
independent recursive rule-major priority, direct semantic-coordinate, and exact-sign relation. -/
theorem ruleMajorTetrahedralSpatialDescriptorAt?_sound_declarative
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (descriptor : RS)
    (emitted : input.ruleMajorTetrahedralSpatialDescriptorAt?
      center context = some descriptor) :
    input.DeclarativeRuleMajorLocalizedTetrahedralDescriptor
      center context descriptor := by
  obtain ⟨points, pointsComputed, geometry⟩ :=
    (input.ruleMajorTetrahedralSpatialDescriptorAt?_eq_some_iff
      center context descriptor).mp emitted
  obtain ⟨order, priority, spatial⟩ :=
    input.ruleMajorPriorityOrderedSpatialPoints?_sound_declarative
      center context points pointsComputed
  exact ⟨order, points, priority, spatial, geometry⟩

/-- Exact end of the localized spatial pipeline: an emitted descriptor is equivalent to the
independent sign relation on the four points returned in descending official-CIP order. -/
theorem tetrahedralSpatialDescriptorAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (descriptor : RS) :
    input.tetrahedralSpatialDescriptorAt? center context = some descriptor ↔
      ∃ points,
        input.priorityOrderedSpatialPoints? center context = some points ∧
          RationalTetrahedralDescriptor points descriptor := by
  change
    (input.priorityOrderedSpatialPoints? center context).bind
        descriptorOfPriorityOrderedPoints? = some descriptor ↔ _
  rw [Option.bind_eq_some_iff]
  apply exists_congr
  intro points
  rw [descriptorOfPriorityOrderedPoints?_eq_some_iff]

/-- Local implementation-refinement theorem. An executable descriptor is emitted exactly when the
proof-facing internal comparator and independent exact-geometry relation specify it. This is not
yet the IUPAC end-to-end theorem because the internal comparator is not the rule-major authority. -/
theorem tetrahedralSpatialDescriptorAt?_eq_some_iff_reference
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (descriptor : RS) :
    input.tetrahedralSpatialDescriptorAt? center context = some descriptor ↔
      ReferenceLocalizedTetrahedralDescriptor input center context descriptor := by
  rw [input.tetrahedralSpatialDescriptorAt?_eq_some_iff center context descriptor]
  unfold ReferenceLocalizedTetrahedralDescriptor
  rw [← input.priorityOrderedSpatialPoints?_eq_reference center context]

/-- Every rational geometry descriptor is exactly the descriptor read by the existing real-valued
tetrahedral handedness semantics after the canonical rational-to-real embedding.  Under the
calibrated convention, negative exact volume gives real handedness `-1` and descriptor `R`, and
positive exact volume gives real handedness `1` and descriptor `S`. -/
theorem rationalTetrahedralDescriptor_conforms_real_handedness
    {points : List CartesianPoint3} {descriptor : RS}
    (correct : RationalTetrahedralDescriptor points descriptor) :
    ∃ first second third fourth,
      points = [first, second, third, fourth] ∧
      descriptor = RS.ofHandedness
        (TetrahedralGeometry.handedness
          (CartesianPoint3.toRealTetrahedralGeometry first second third fourth)) := by
  rcases correct with ⟨first, second, third, fourth, rfl, sign⟩
  cases descriptor with
  | R =>
      refine ⟨first, second, third, fourth, rfl, ?_⟩
      rw [TetrahedralGeometry.handedness,
        CartesianPoint3.orientedVolume_toRealTetrahedralGeometry,
        Real.sign_of_neg (by exact_mod_cast sign)]
      exact RS.ofHandedness_neg_one.symm
  | S =>
      refine ⟨first, second, third, fourth, rfl, ?_⟩
      rw [TetrahedralGeometry.handedness,
        CartesianPoint3.orientedVolume_toRealTetrahedralGeometry,
        Real.sign_of_pos (by exact_mod_cast sign)]
      exact RS.ofHandedness_one.symm

/-- Every emitted localized spatial descriptor therefore has a priority-ordered rational witness
whose value agrees with the existing real-valued tetrahedral handedness semantics. -/
theorem tetrahedralSpatialDescriptorAt?_sound_real_handedness
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (descriptor : RS)
    (emitted : input.tetrahedralSpatialDescriptorAt? center context = some descriptor) :
    ∃ points first second third fourth,
      input.priorityOrderedSpatialPoints? center context = some points ∧
      points = [first, second, third, fourth] ∧
      descriptor = RS.ofHandedness
        (TetrahedralGeometry.handedness
          (CartesianPoint3.toRealTetrahedralGeometry first second third fourth)) := by
  obtain ⟨points, pointsObserved, correct⟩ :=
    (input.tetrahedralSpatialDescriptorAt?_eq_some_iff center context descriptor).mp emitted
  obtain ⟨first, second, third, fourth, pointsIdentity, descriptorIdentity⟩ :=
    rationalTetrahedralDescriptor_conforms_real_handedness correct
  exact ⟨points, first, second, third, fourth, pointsObserved, pointsIdentity,
    descriptorIdentity⟩

/-- One descriptor emitted for an automatically detected localized center. -/
structure LocalizedTetrahedralSpatialAssignment (input : CertifiedLocalizedCIPInput) where
  center : input.TetrahedralCenter
  descriptor : RS
  deriving DecidableEq

/-- Analyze every automatically detected four-neighbor center in canonical atom-index order.
Each center independently refuses tied priorities, absent coordinates, and degenerate geometry. -/
def analyzeTetrahedralSpatial (input : CertifiedLocalizedCIPInput)
    (context : input.TetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext) :
    List (LocalizedTetrahedralSpatialAssignment input) :=
  input.canonicalTetrahedralCenters.filterMap fun center =>
    (input.tetrahedralSpatialDescriptorAt? center (context center)).map fun descriptor =>
      { center := center, descriptor := descriptor }

/-- Whole-molecule localized analyzer using the replacement exhaustive rule-major constitutional
keys. As on the older path, supplied descriptor contexts are an explicit remaining boundary. -/
def analyzeRuleMajorTetrahedralSpatial (input : CertifiedLocalizedCIPInput)
    (context : input.TetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext) :
    List (LocalizedTetrahedralSpatialAssignment input) :=
  input.canonicalTetrahedralCenters.filterMap fun center =>
    (input.ruleMajorTetrahedralSpatialDescriptorAt? center (context center)).map fun descriptor =>
      { center := center, descriptor := descriptor }

/-- Exact membership for the replacement whole-molecule analyzer. -/
theorem mem_analyzeRuleMajorTetrahedralSpatial_iff
    (input : CertifiedLocalizedCIPInput)
    (context : input.TetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext)
    (assignment : LocalizedTetrahedralSpatialAssignment input) :
    assignment ∈ input.analyzeRuleMajorTetrahedralSpatial context ↔
      input.ruleMajorTetrahedralSpatialDescriptorAt? assignment.center
        (context assignment.center) = some assignment.descriptor := by
  constructor
  · intro present
    rw [analyzeRuleMajorTetrahedralSpatial, List.mem_filterMap] at present
    obtain ⟨center, _centerPresent, assignmentObserved⟩ := present
    cases descriptorObserved :
        input.ruleMajorTetrahedralSpatialDescriptorAt? center (context center) with
    | none => simp [descriptorObserved] at assignmentObserved
    | some descriptor =>
        simp [descriptorObserved] at assignmentObserved
        subst assignment
        exact descriptorObserved
  · intro emitted
    rw [analyzeRuleMajorTetrahedralSpatial, List.mem_filterMap]
    refine ⟨assignment.center, ?_, ?_⟩
    · exact (input.mem_canonicalTetrahedralCenters_iff assignment.center).mpr
        assignment.center.2
    · simp [emitted]

/-- Every descriptor emitted by the replacement whole-molecule path satisfies its exhaustive
rule-major priority and exact-geometry relation. -/
theorem analyzeRuleMajorTetrahedralSpatial_member_conforms
    (input : CertifiedLocalizedCIPInput)
    (context : input.TetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext)
    (assignment : LocalizedTetrahedralSpatialAssignment input)
    (present : assignment ∈ input.analyzeRuleMajorTetrahedralSpatial context) :
    RuleMajorLocalizedTetrahedralDescriptor input assignment.center
      (context assignment.center) assignment.descriptor := by
  apply (input.ruleMajorTetrahedralSpatialDescriptorAt?_eq_some_iff
    assignment.center (context assignment.center) assignment.descriptor).mp
  exact (input.mem_analyzeRuleMajorTetrahedralSpatial_iff context assignment).mp present

/-- Every whole-molecule assignment from the replacement path satisfies the independent
recursive-priority and exact semantic-geometry descriptor relation. -/
theorem analyzeRuleMajorTetrahedralSpatial_member_conforms_declarative
    (input : CertifiedLocalizedCIPInput)
    (context : input.TetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext)
    (assignment : LocalizedTetrahedralSpatialAssignment input)
    (present : assignment ∈ input.analyzeRuleMajorTetrahedralSpatial context) :
    input.DeclarativeRuleMajorLocalizedTetrahedralDescriptor assignment.center
      (context assignment.center) assignment.descriptor := by
  apply input.ruleMajorTetrahedralSpatialDescriptorAt?_sound_declarative
  exact (input.mem_analyzeRuleMajorTetrahedralSpatial_iff context assignment).mp present

/-- Exact output membership: an assignment occurs precisely when its detected center's safe
priority-and-spatial pipeline emits that descriptor. -/
theorem mem_analyzeTetrahedralSpatial_iff
    (input : CertifiedLocalizedCIPInput)
    (context : input.TetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext)
    (assignment : LocalizedTetrahedralSpatialAssignment input) :
    assignment ∈ input.analyzeTetrahedralSpatial context ↔
      input.tetrahedralSpatialDescriptorAt? assignment.center
        (context assignment.center) = some assignment.descriptor := by
  constructor
  · intro present
    rw [analyzeTetrahedralSpatial, List.mem_filterMap] at present
    obtain ⟨center, _centerPresent, assignmentObserved⟩ := present
    cases descriptorObserved :
        input.tetrahedralSpatialDescriptorAt? center (context center) with
    | none => simp [descriptorObserved] at assignmentObserved
    | some descriptor =>
        simp [descriptorObserved] at assignmentObserved
        subst assignment
        exact descriptorObserved
  · intro emitted
    rw [analyzeTetrahedralSpatial, List.mem_filterMap]
    refine ⟨assignment.center, ?_, ?_⟩
    · exact (input.mem_canonicalTetrahedralCenters_iff assignment.center).mpr
        assignment.center.2
    · simp [emitted]

/-- Every descriptor emitted by the whole-molecule localized analyzer satisfies the internal
priority/exact-geometry reference relation at its detected center. -/
theorem analyzeTetrahedralSpatial_member_conforms_reference
    (input : CertifiedLocalizedCIPInput)
    (context : input.TetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext)
    (assignment : LocalizedTetrahedralSpatialAssignment input)
    (present : assignment ∈ input.analyzeTetrahedralSpatial context) :
    ReferenceLocalizedTetrahedralDescriptor input assignment.center
      (context assignment.center) assignment.descriptor := by
  apply (input.tetrahedralSpatialDescriptorAt?_eq_some_iff_reference
    assignment.center (context assignment.center) assignment.descriptor).mp
  exact (input.mem_analyzeTetrahedralSpatial_iff context assignment).mp present

/-- Every member of the whole-molecule output has an exact priority-ordered rational witness and
agrees with the real-valued tetrahedral handedness semantics. -/
theorem analyzeTetrahedralSpatial_member_sound_real_handedness
    (input : CertifiedLocalizedCIPInput)
    (context : input.TetrahedralCenter → Fin 4 →
      CIPRuleEngine.OfficialLigandRuleContext)
    (assignment : LocalizedTetrahedralSpatialAssignment input)
    (present : assignment ∈ input.analyzeTetrahedralSpatial context) :
    ∃ points first second third fourth,
      input.priorityOrderedSpatialPoints? assignment.center
          (context assignment.center) = some points ∧
      points = [first, second, third, fourth] ∧
      assignment.descriptor = RS.ofHandedness
        (TetrahedralGeometry.handedness
          (CartesianPoint3.toRealTetrahedralGeometry first second third fourth)) := by
  apply input.tetrahedralSpatialDescriptorAt?_sound_real_handedness
  exact (input.mem_analyzeTetrahedralSpatial_iff context assignment).mp present

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
