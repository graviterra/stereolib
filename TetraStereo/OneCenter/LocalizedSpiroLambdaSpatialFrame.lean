import TetraStereo.OneCenter.LocalizedSpiroLambdaCoordinationPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Exact source-derived spatial frames for lambda spiro centers

This is the representation seam between source-level P-93 spiro perception and the IR-9
coordinate analyzers.  Neither the donor atoms nor their coordinates are supplied independently:
the donors are the complete graph neighbourhood of the perceived center and every point is read
from the same authoritative spatial configuration.
-/

/-- Complete coordinate package for one perceived lambda-4, lambda-5, or lambda-6 spiro atom. -/
structure LocalizedLambdaSpiroSpatialFrame
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) where
  candidate : input.LocalizedLambdaSpiroCenter center
  centerPoint : CartesianPoint3
  donorPoints : List CartesianPoint3
  deriving DecidableEq

/-- Independent meaning of a source-derived lambda-spiro spatial frame. -/
def DeclarativeLocalizedLambdaSpiroSpatialFrame
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (frame : input.LocalizedLambdaSpiroSpatialFrame center) : Prop :=
  input.DeclarativeLocalizedLambdaSpiroCenter center frame.candidate ∧
    input.SemanticSpatialPointAt center frame.centerPoint ∧
    List.Forall₂ input.SemanticSpatialPointAt
      (input.localizedLambdaSpiroDonors center) frame.donorPoints

/-- Source-level frame construction.  It first proves the lambda-spiro carrier, then reads the
center and every graph-derived donor from the authoritative coordinate channel. -/
noncomputable def localizedLambdaSpiroSpatialFrameAt?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    Option (input.LocalizedLambdaSpiroSpatialFrame center) := do
  let candidate ← input.localizedLambdaSpiroCenterAt? center
  let centerPoint ← input.spatialPointAt? center
  let donorPoints ←
    (input.localizedLambdaSpiroDonors center).mapM input.spatialPointAt?
  some { candidate, centerPoint, donorPoints }

private theorem mapM_spatialPointAt?_eq_some_iff_forall₂
    (input : CertifiedLocalizedCIPInput) :
    ∀ (atoms : List input.Atom) (points : List CartesianPoint3),
      atoms.mapM input.spatialPointAt? = some points ↔
        List.Forall₂ input.SemanticSpatialPointAt atoms points
  | [], points => by
      constructor
      · intro computed
        simp at computed
        subst points
        exact .nil
      · intro related
        cases related
        rfl
  | atom :: atoms, points => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases pointEq : input.spatialPointAt? atom with
        | none => simp [pointEq] at computed
        | some point =>
            cases pointsEq : atoms.mapM input.spatialPointAt? with
            | none => simp [pointEq, pointsEq] at computed
            | some tail =>
                simp [pointEq, pointsEq] at computed
                subst points
                exact .cons
                  ((input.spatialPointAt?_eq_some_iff atom point).mp pointEq)
                  ((mapM_spatialPointAt?_eq_some_iff_forall₂ input atoms tail).mp pointsEq)
      · intro related
        cases related with
        | cons head tail =>
            rw [List.mapM_cons,
              (input.spatialPointAt?_eq_some_iff atom _).mpr head,
              (mapM_spatialPointAt?_eq_some_iff_forall₂ input atoms _).mpr tail]
            rfl

/-- Frame construction is exact against the independent carrier and coordinate relations. -/
theorem localizedLambdaSpiroSpatialFrameAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (frame : input.LocalizedLambdaSpiroSpatialFrame center) :
    input.localizedLambdaSpiroSpatialFrameAt? center = some frame ↔
      input.DeclarativeLocalizedLambdaSpiroSpatialFrame center frame := by
  constructor
  · intro computed
    unfold localizedLambdaSpiroSpatialFrameAt? at computed
    cases candidateEq : input.localizedLambdaSpiroCenterAt? center with
    | none => simp [candidateEq] at computed
    | some candidate =>
        cases centerEq : input.spatialPointAt? center with
        | none => simp [candidateEq, centerEq] at computed
        | some centerPoint =>
            cases pointsEq : (input.localizedLambdaSpiroDonors center).mapM
                input.spatialPointAt? with
            | none => simp [candidateEq, centerEq, pointsEq] at computed
            | some donorPoints =>
                have frameEq :
                    frame = ({ candidate, centerPoint, donorPoints } :
                      input.LocalizedLambdaSpiroSpatialFrame center) := by
                  simpa [candidateEq, centerEq, pointsEq] using computed.symm
                subst frame
                exact ⟨
                  (input.localizedLambdaSpiroCenterAt?_eq_some_iff center candidate).mp
                    candidateEq,
                  (input.spatialPointAt?_eq_some_iff center centerPoint).mp centerEq,
                  (mapM_spatialPointAt?_eq_some_iff_forall₂ input _ donorPoints).mp
                    pointsEq⟩
  · rintro ⟨candidateJudged, centerJudged, pointsJudged⟩
    have candidateEq :=
      (input.localizedLambdaSpiroCenterAt?_eq_some_iff center frame.candidate).mpr
        candidateJudged
    have centerEq :=
      (input.spatialPointAt?_eq_some_iff center frame.centerPoint).mpr centerJudged
    have pointsEq :=
      (mapM_spatialPointAt?_eq_some_iff_forall₂ input
        (input.localizedLambdaSpiroDonors center) frame.donorPoints).mpr pointsJudged
    simp [localizedLambdaSpiroSpatialFrameAt?, candidateEq, centerEq, pointsEq]

/-- Spatial refusal is exhaustive: it is exactly the absence of a declaratively valid frame. -/
theorem localizedLambdaSpiroSpatialFrameAt?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    input.localizedLambdaSpiroSpatialFrameAt? center = none ↔
      ∀ frame, ¬input.DeclarativeLocalizedLambdaSpiroSpatialFrame center frame := by
  constructor
  · intro none frame judged
    have someEq :=
      (input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff center frame).mpr judged
    rw [none] at someEq
    contradiction
  · intro absent
    cases computed : input.localizedLambdaSpiroSpatialFrameAt? center with
    | none => rfl
    | some frame =>
        exact False.elim (absent frame
          ((input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff center frame).mp computed))

/-- The independently valid spatial frame at a fixed center is unique. -/
theorem declarativeLocalizedLambdaSpiroSpatialFrame_subsingleton
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    {left right : input.LocalizedLambdaSpiroSpatialFrame center}
    (leftJudged : input.DeclarativeLocalizedLambdaSpiroSpatialFrame center left)
    (rightJudged : input.DeclarativeLocalizedLambdaSpiroSpatialFrame center right) :
    left = right := by
  have leftEq :=
    (input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff center left).mpr leftJudged
  have rightEq :=
    (input.localizedLambdaSpiroSpatialFrameAt?_eq_some_iff center right).mpr rightJudged
  rw [leftEq] at rightEq
  exact Option.some.inj rightEq

/-- The coordinate vector has exactly the perceived coordination number: four, five, or six. -/
theorem DeclarativeLocalizedLambdaSpiroSpatialFrame.donorPoints_length
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (frame : input.LocalizedLambdaSpiroSpatialFrame center)
    (judged : input.DeclarativeLocalizedLambdaSpiroSpatialFrame center frame) :
    frame.donorPoints.length = frame.candidate.coordination.number := by
  exact judged.2.2.length_eq.symm.trans
    (judged.1.donor_length input center frame.candidate)

private theorem forall₂_semanticSpatialPointAt_same_configuration
    (input : CertifiedLocalizedCIPInput) (spatial : SpatialConfiguration)
    (sourceEq : input.certified.input.spatial? = some spatial) :
    ∀ {atoms : List input.Atom} {points : List CartesianPoint3},
      List.Forall₂ input.SemanticSpatialPointAt atoms points →
        List.Forall₂
          (fun atom point => spatial.positions[atom.val]? = some point) atoms points
  | [], [], .nil => .nil
  | atom :: atoms, point :: points, .cons head tail => by
      rcases head with ⟨observed, observedEq, pointEq⟩
      have spatialEq : observed = spatial := by
        exact Option.some.inj (observedEq.symm.trans sourceEq)
      subst observed
      exact .cons pointEq
        (forall₂_semanticSpatialPointAt_same_configuration input spatial sourceEq tail)

/-- Every point in the frame comes from one and the same authoritative spatial configuration;
there is no possibility of mixing conformers across donor lookups. -/
theorem DeclarativeLocalizedLambdaSpiroSpatialFrame.exists_shared_configuration
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (frame : input.LocalizedLambdaSpiroSpatialFrame center)
    (judged : input.DeclarativeLocalizedLambdaSpiroSpatialFrame center frame) :
    ∃ spatial,
      input.certified.input.spatial? = some spatial ∧
      spatial.positions[center.val]? = some frame.centerPoint ∧
      List.Forall₂
        (fun donor point => spatial.positions[donor.val]? = some point)
        (input.localizedLambdaSpiroDonors center) frame.donorPoints := by
  rcases judged.2.1 with ⟨spatial, spatialEq, centerEq⟩
  exact ⟨spatial, spatialEq, centerEq,
    forall₂_semanticSpatialPointAt_same_configuration input spatial spatialEq judged.2.2⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
