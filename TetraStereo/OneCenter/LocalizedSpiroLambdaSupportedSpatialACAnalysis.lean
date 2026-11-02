import TetraStereo.OneCenter.LocalizedSpiroLambdaSpatialFrame
import TetraStereo.OneCenter.CIPIR9SeeSawSpatialOrientationIntegration
import TetraStereo.OneCenter.CIPIR9SquarePyramid4SpatialOrientationIntegration
import TetraStereo.OneCenter.CIPIR9SquarePyramid5SpatialIntegration
import TetraStereo.OneCenter.CIPIR9TrigonalBipyramid5SpatialIntegration
import TetraStereo.OneCenter.CIPIR9OctahedronSpatialIntegration
import TetraStereo.OneCenter.CIPIR9TrigonalPrism6SpatialIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

/-!
# Exact lambda-spiro A/C analysis on the represented coordinate geometries

The router below covers the coordinate-derived chiral geometries currently implemented by the
IR-9 layer: SS-4 and SPY-4 for coordination four, SPY-5 and TBPY-5 for coordination five, and
OC-6 and TPR-6 for coordination six.  The name contains `Supported` intentionally: this is the
exact finite set of coordinate geometries routed here, not an assertion that every coordination
geometry or every distortion policy has already been formalized.
-/

/-- Exact represented-geometry route before the result is attached to its source spiro carrier. -/
def supportedLambdaSpiroCoordinateAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat) (coordination : SpiroCenterCoordination) :
    Option StereoAssignment :=
  match coordination with
  | .tetrahedral => none
  | .lambda4 =>
      match result.seeSawSpatialOrientationAssignment? spatial { center, ligands } with
      | some assignment => some assignment
      | none => result.squarePyramid4SpatialOrientationAssignment? spatial { center, ligands }
  | .lambda5 =>
      match result.squarePyramid5SpatialAssignment? spatial { center, ligands } with
      | some assignment => some assignment
      | none => result.trigonalBipyramid5SpatialAssignment? spatial { center, ligands }
  | .lambda6 =>
      match result.octahedronSpatialAssignment? spatial { center, ligands } with
      | some assignment => some assignment
      | none => result.trigonalPrism6SpatialAssignment? spatial { center, ligands }

/-- Independent branch-sensitive meaning of the represented coordinate router. -/
def SupportedLambdaSpiroCoordinateAssignmentJudgment
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat) (coordination : SpiroCenterCoordination)
    (assignment : StereoAssignment) : Prop :=
  match coordination with
  | .tetrahedral => False
  | .lambda4 =>
      result.seeSawSpatialOrientationAssignment? spatial { center, ligands } =
          some assignment ∨
        (result.seeSawSpatialOrientationAssignment? spatial { center, ligands } = none ∧
          result.squarePyramid4SpatialOrientationAssignment? spatial { center, ligands } =
            some assignment)
  | .lambda5 =>
      result.squarePyramid5SpatialAssignment? spatial { center, ligands } = some assignment ∨
        (result.squarePyramid5SpatialAssignment? spatial { center, ligands } = none ∧
          result.trigonalBipyramid5SpatialAssignment? spatial { center, ligands } =
            some assignment)
  | .lambda6 =>
      result.octahedronSpatialAssignment? spatial { center, ligands } = some assignment ∨
        (result.octahedronSpatialAssignment? spatial { center, ligands } = none ∧
          result.trigonalPrism6SpatialAssignment? spatial { center, ligands } = some assignment)

theorem supportedLambdaSpiroCoordinateAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat) (coordination : SpiroCenterCoordination)
    (assignment : StereoAssignment) :
    supportedLambdaSpiroCoordinateAssignment? result spatial center ligands coordination =
        some assignment ↔
      SupportedLambdaSpiroCoordinateAssignmentJudgment result spatial center ligands
        coordination assignment := by
  cases coordination with
  | tetrahedral => simp [supportedLambdaSpiroCoordinateAssignment?,
      SupportedLambdaSpiroCoordinateAssignmentJudgment]
  | lambda4 =>
      cases seeSawEq : result.seeSawSpatialOrientationAssignment? spatial { center, ligands } <;>
        simp [supportedLambdaSpiroCoordinateAssignment?,
          SupportedLambdaSpiroCoordinateAssignmentJudgment, seeSawEq]
  | lambda5 =>
      cases squarePyramidEq : result.squarePyramid5SpatialAssignment? spatial
          { center, ligands } <;>
        simp [supportedLambdaSpiroCoordinateAssignment?,
          SupportedLambdaSpiroCoordinateAssignmentJudgment, squarePyramidEq]
  | lambda6 =>
      cases octahedronEq : result.octahedronSpatialAssignment? spatial
          { center, ligands } <;>
        simp [supportedLambdaSpiroCoordinateAssignment?,
          SupportedLambdaSpiroCoordinateAssignmentJudgment, octahedronEq]

theorem supportedLambdaSpiroCoordinateAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : Nat) (ligands : List Nat) (coordination : SpiroCenterCoordination) :
    supportedLambdaSpiroCoordinateAssignment? result spatial center ligands coordination = none ↔
      ∀ assignment,
        ¬SupportedLambdaSpiroCoordinateAssignmentJudgment result spatial center ligands
          coordination assignment := by
  constructor
  · intro absent assignment judged
    have produced :=
      (supportedLambdaSpiroCoordinateAssignment?_eq_some_iff result spatial center ligands
        coordination assignment).mpr judged
    rw [absent] at produced
    contradiction
  · intro noJudgment
    cases produced : supportedLambdaSpiroCoordinateAssignment? result spatial center ligands
        coordination with
    | none => rfl
    | some assignment =>
        exact False.elim (noJudgment assignment
          ((supportedLambdaSpiroCoordinateAssignment?_eq_some_iff result spatial center ligands
            coordination assignment).mp produced))

/-- Extract the polyhedral descriptor only when the public unit is the requested center and the
descriptor has the P-93-required coordination number and A/C suffix. -/
def exactSpiroPolyhedralACDescriptor?
    (center : Nat) (coordination : SpiroCenterCoordination)
    (assignment : StereoAssignment) : Option PolyhedralDescriptor :=
  match assignment.unit, assignment.outcome with
  | .polyhedron assignedCenter, .polyhedral descriptor =>
      if assignedCenter = center then
        if SpiroPolyhedralACDescriptorJudgment coordination descriptor then some descriptor
        else none
      else none
  | _, _ => none

theorem exactSpiroPolyhedralACDescriptor?_eq_some_iff
    (center : Nat) (coordination : SpiroCenterCoordination)
    (assignment : StereoAssignment) (descriptor : PolyhedralDescriptor) :
    exactSpiroPolyhedralACDescriptor? center coordination assignment = some descriptor ↔
      assignment.unit = .polyhedron center ∧
      assignment.outcome = .polyhedral descriptor ∧
      SpiroPolyhedralACDescriptorJudgment coordination descriptor := by
  cases assignment with
  | mk unit outcome =>
      cases unit <;> cases outcome <;>
        simp [exactSpiroPolyhedralACDescriptor?]
      rename_i assignedCenter observed
      by_cases centerEq : assignedCenter = center
      · subst assignedCenter
        by_cases judged : SpiroPolyhedralACDescriptorJudgment coordination observed <;>
          simp [judged] <;>
          intro equality <;> subst descriptor <;> exact judged
      · simp [centerEq]

namespace CertifiedLocalizedCIPInput

/-- Final source-attached A/C result for one lambda-spiro center. -/
structure LocalizedLambdaSpiroSupportedACAssignment
    (input : CertifiedLocalizedCIPInput) where
  center : input.Atom
  carrier : input.LocalizedLambdaSpiroCenter center
  descriptor : PolyhedralDescriptor
  deriving DecidableEq

/-- Complete semantic judgment for the represented lambda-spiro spatial route.  In particular,
the production normalization molecule is checked to be the same semantic molecule as the source
carrier, rather than being an unrelated priority oracle. -/
def LocalizedLambdaSpiroSupportedACAssignmentJudgment
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment) : Prop :=
  certified.result.parsed.toSemanticMolecule? = some input.certified.input.molecule ∧
    ∃ sourceFrame spatial publicAssignment,
      input.DeclarativeLocalizedLambdaSpiroSpatialFrame assignment.center sourceFrame ∧
      sourceFrame.candidate = assignment.carrier ∧
      input.certified.input.spatial? = some spatial ∧
      SupportedLambdaSpiroCoordinateAssignmentJudgment certified.result spatial
        assignment.center.val
        ((input.localizedLambdaSpiroDonors assignment.center).map (fun donor => donor.val))
        assignment.carrier.coordination publicAssignment ∧
      publicAssignment.unit = .polyhedron assignment.center.val ∧
      publicAssignment.outcome = .polyhedral assignment.descriptor ∧
      SpiroPolyhedralACDescriptorJudgment assignment.carrier.coordination
        assignment.descriptor

/-- Source-to-coordinate-to-IR-9 A/C analyzer for all represented lambda-spiro geometries. -/
noncomputable def localizedLambdaSpiroSupportedACAssignmentAt?
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) :
    Option input.LocalizedLambdaSpiroSupportedACAssignment :=
  if certified.result.parsed.toSemanticMolecule? = some input.certified.input.molecule then do
    let sourceFrame ← input.localizedLambdaSpiroSpatialFrameAt? center
    let spatial ← input.certified.input.spatial?
    let publicAssignment ← supportedLambdaSpiroCoordinateAssignment? certified.result spatial
      center.val ((input.localizedLambdaSpiroDonors center).map (fun donor => donor.val))
      sourceFrame.candidate.coordination
    let descriptor ← exactSpiroPolyhedralACDescriptor? center.val
      sourceFrame.candidate.coordination publicAssignment
    some { center, carrier := sourceFrame.candidate, descriptor }
  else none

/-- The complete represented lambda-spiro pipeline is exact against its independent judgment. -/
theorem localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom)
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment) :
    input.localizedLambdaSpiroSupportedACAssignmentAt? certified center = some assignment ↔
      assignment.center = center ∧
        input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified assignment := by
  classical
  unfold localizedLambdaSpiroSupportedACAssignmentAt?
  by_cases agreement :
      certified.result.parsed.toSemanticMolecule? = some input.certified.input.molecule
  · cases frameEq : input.localizedLambdaSpiroSpatialFrameAt? center with
    | none =>
        constructor
        · simp [agreement]
        · rintro ⟨rfl, _, sourceFrame, _, _, frameJudged, _⟩
          have produced :=
            (input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff assignment.center sourceFrame).mpr
              frameJudged
          rw [frameEq] at produced
          contradiction
    | some sourceFrame =>
        cases spatialEq : input.certified.input.spatial? with
        | none =>
            constructor
            · simp [agreement]
            · rintro ⟨rfl, _, _, spatial, _, _, _, sourceSpatial, _⟩
              rw [spatialEq] at sourceSpatial
              contradiction
        | some spatial =>
            let ligands :=
              (input.localizedLambdaSpiroDonors center).map (fun donor => donor.val)
            cases publicEq : supportedLambdaSpiroCoordinateAssignment? certified.result spatial
                center.val ligands sourceFrame.candidate.coordination with
            | none =>
                constructor
                · simp [agreement, ligands, publicEq]
                · rintro ⟨rfl, _, judgedFrame, judgedSpatial, publicAssignment,
                    frameJudged, candidateEq, sourceSpatial, publicJudged, _⟩
                  have uniqueFrame :=
                    input.declarativeLocalizedLambdaSpiroSpatialFrame_subsingleton assignment.center
                      ((input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff
                        assignment.center sourceFrame).mp frameEq) frameJudged
                  subst judgedFrame
                  have judgedSpatialEq : judgedSpatial = spatial :=
                    Option.some.inj (sourceSpatial.symm.trans spatialEq)
                  subst judgedSpatial
                  rw [candidateEq] at publicEq
                  have produced :=
                    (supportedLambdaSpiroCoordinateAssignment?_eq_some_iff certified.result
                      spatial assignment.center.val ligands assignment.carrier.coordination
                      publicAssignment).mpr publicJudged
                  rw [publicEq] at produced
                  contradiction
            | some publicAssignment =>
                cases descriptorEq : exactSpiroPolyhedralACDescriptor? center.val
                    sourceFrame.candidate.coordination publicAssignment with
                | none =>
                    constructor
                    · simp [agreement, ligands, publicEq, descriptorEq]
                    · rintro ⟨rfl, _, judgedFrame, judgedSpatial, judgedPublic,
                        frameJudged, candidateEq, sourceSpatial, publicJudged,
                        unitEq, outcomeEq, descriptorJudged⟩
                      have uniqueFrame :=
                        input.declarativeLocalizedLambdaSpiroSpatialFrame_subsingleton
                          assignment.center
                          ((input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff
                            assignment.center sourceFrame).mp frameEq) frameJudged
                      subst judgedFrame
                      have judgedSpatialEq : judgedSpatial = spatial :=
                        Option.some.inj (sourceSpatial.symm.trans spatialEq)
                      subst judgedSpatial
                      rw [candidateEq] at publicEq descriptorEq
                      have uniquePublic : judgedPublic = publicAssignment := by
                        have produced :=
                          (supportedLambdaSpiroCoordinateAssignment?_eq_some_iff certified.result
                            spatial assignment.center.val ligands assignment.carrier.coordination
                            judgedPublic).mpr publicJudged
                        rw [publicEq] at produced
                        exact Option.some.inj produced.symm
                      subst judgedPublic
                      have descriptorSome :=
                        (exactSpiroPolyhedralACDescriptor?_eq_some_iff assignment.center.val
                          assignment.carrier.coordination publicAssignment
                          assignment.descriptor).mpr ⟨unitEq, outcomeEq, descriptorJudged⟩
                      rw [descriptorEq] at descriptorSome
                      contradiction
                | some descriptor =>
                    constructor
                    · intro computed
                      have assignmentEq :
                          assignment = ({ center, carrier := sourceFrame.candidate, descriptor } :
                            input.LocalizedLambdaSpiroSupportedACAssignment) := by
                        simpa [agreement, frameEq, spatialEq, ligands, publicEq, descriptorEq]
                          using computed.symm
                      subst assignment
                      have frameJudged :=
                        (input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff
                          center sourceFrame).mp frameEq
                      have publicJudged :=
                        (supportedLambdaSpiroCoordinateAssignment?_eq_some_iff certified.result
                          spatial center.val ligands sourceFrame.candidate.coordination
                          publicAssignment).mp publicEq
                      have descriptorJudged :=
                        (exactSpiroPolyhedralACDescriptor?_eq_some_iff center.val
                          sourceFrame.candidate.coordination publicAssignment descriptor).mp
                            descriptorEq
                      exact ⟨rfl, agreement, sourceFrame, spatial, publicAssignment,
                        frameJudged, rfl, spatialEq, by simpa [ligands] using publicJudged,
                        descriptorJudged.1, descriptorJudged.2.1, descriptorJudged.2.2⟩
                    · rintro ⟨rfl, _, judgedFrame, judgedSpatial, judgedPublic,
                        frameJudged, candidateEq, sourceSpatial, publicJudged,
                        unitEq, outcomeEq, descriptorJudged⟩
                      have uniqueFrame :=
                        input.declarativeLocalizedLambdaSpiroSpatialFrame_subsingleton
                          assignment.center
                          ((input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff
                            assignment.center sourceFrame).mp frameEq) frameJudged
                      subst judgedFrame
                      have judgedSpatialEq : judgedSpatial = spatial :=
                        Option.some.inj (sourceSpatial.symm.trans spatialEq)
                      subst judgedSpatial
                      rw [candidateEq] at publicEq descriptorEq
                      have uniquePublic : judgedPublic = publicAssignment := by
                        have produced :=
                          (supportedLambdaSpiroCoordinateAssignment?_eq_some_iff certified.result
                            spatial assignment.center.val ligands assignment.carrier.coordination
                            judgedPublic).mpr (by simpa [ligands] using publicJudged)
                        rw [publicEq] at produced
                        exact Option.some.inj produced.symm
                      subst judgedPublic
                      have descriptorSome :=
                        (exactSpiroPolyhedralACDescriptor?_eq_some_iff assignment.center.val
                          assignment.carrier.coordination publicAssignment
                          assignment.descriptor).mpr ⟨unitEq, outcomeEq, descriptorJudged⟩
                      rw [descriptorEq] at descriptorSome
                      have descriptorIdentity : assignment.descriptor = descriptor :=
                        (Option.some.inj descriptorSome).symm
                      have assignmentIdentity :
                          ({ center := assignment.center, carrier := assignment.carrier,
                              descriptor } :
                            input.LocalizedLambdaSpiroSupportedACAssignment) = assignment := by
                        cases assignment with
                        | mk assignmentCenter assignmentCarrier assignmentDescriptor =>
                            dsimp at descriptorIdentity ⊢
                            cases descriptorIdentity
                            rfl
                      simpa [agreement, frameEq, spatialEq, ligands, publicEq, descriptorEq,
                        candidateEq] using congrArg some assignmentIdentity
  · constructor
    · simp [agreement]
    · rintro ⟨_, judged⟩
      exact False.elim (agreement judged.1)

/-- Exhaustive refusal for one center in the represented coordinate-geometry domain. -/
theorem localizedLambdaSpiroSupportedACAssignmentAt?_eq_none_iff
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom) :
    input.localizedLambdaSpiroSupportedACAssignmentAt? certified center = none ↔
      ∀ assignment,
        assignment.center = center →
        ¬input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified assignment := by
  constructor
  · intro absent assignment centerEq judged
    have produced :=
      (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff certified center
        assignment).mpr ⟨centerEq, judged⟩
    rw [absent] at produced
    contradiction
  · intro noJudgment
    cases produced : input.localizedLambdaSpiroSupportedACAssignmentAt? certified center with
    | none => rfl
    | some assignment =>
        have judged :=
          (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff certified center
            assignment).mp produced
        exact False.elim (noJudgment assignment judged.1 judged.2)

/-- Every emitted descriptor is a P-93 polyhedral A/C descriptor with exactly the perceived
lambda coordination number. -/
theorem localizedLambdaSpiroSupportedACAssignmentAt?_sound_P93
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom)
    (assignment : input.LocalizedLambdaSpiroSupportedACAssignment)
    (produced : input.localizedLambdaSpiroSupportedACAssignmentAt? certified center =
      some assignment) :
    assignment.center = center ∧
      SpiroPolyhedralACDescriptorJudgment assignment.carrier.coordination
        assignment.descriptor := by
  have judged :=
    (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff certified center
      assignment).mp produced
  rcases judged with ⟨centerEq, _agreement, sourceFrame, spatial, publicAssignment,
    frameJudged, candidateEq, spatialEq, publicJudged, unitEq, outcomeEq,
    descriptorJudged⟩
  exact ⟨centerEq, descriptorJudged⟩

/-- The independent final judgment at a fixed center is functional. -/
theorem localizedLambdaSpiroSupportedACAssignmentJudgment_subsingleton
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) (center : input.Atom)
    {left right : input.LocalizedLambdaSpiroSupportedACAssignment}
    (leftCenter : left.center = center) (rightCenter : right.center = center)
    (leftJudged : input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified left)
    (rightJudged : input.LocalizedLambdaSpiroSupportedACAssignmentJudgment certified right) :
    left = right := by
  have leftEq :=
    (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff certified center left).mpr
      ⟨leftCenter, leftJudged⟩
  have rightEq :=
    (input.localizedLambdaSpiroSupportedACAssignmentAt?_eq_some_iff certified center right).mpr
      ⟨rightCenter, rightJudged⟩
  rw [leftEq] at rightEq
  exact Option.some.inj rightEq

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
