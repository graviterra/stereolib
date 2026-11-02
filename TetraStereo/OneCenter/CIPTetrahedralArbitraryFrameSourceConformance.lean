import TetraStereo.OneCenter.CIPTetrahedralViewingCalibration
import TetraStereo.OneCenter.CIPTetrahedralAffineViewingNormalization
import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CIPTetrahedralArbitraryFrameSourceConformance

/-!
# Source conformance of arbitrary-frame tetrahedral evidence

`CIPTetrahedralViewingCalibration` proves the local four-point viewing calibration only for
points already in a normal form (`first`, `second`, `third` on a common plane `z = h` and the
fourth at `z = k < h`).  `CIPTetrahedralAffineViewingNormalization` constructs, for an arbitrary
ordered rational quadruple of nonzero oriented volume, an explicit orientation-preserving rational
affine map `T` putting that quadruple into the required normal form.  This module composes the two
results, first as a geometric core, then with the production descriptor pipeline.

## What is proved

For every ordered quadruple `first second third fourth` with nonzero oriented volume and every
descriptor `raw`,

`descriptorOfPriorityOrderedPoints? [first, second, third, fourth] = some raw`

is equivalent to

`SourceCalibratedDescriptor ([first, second, third, fourth].map T.applyPoint) raw`,

where `T = normalizationT first second third fourth` is the explicit transform of the
normalization module (`viewingTransform`).  The list-level form
`descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_points` states the same fact for an
arbitrary list known to equal a four-element literal.  The existential form
`exists_normalizationT_sourceConformance` exposes the constructive transform and its positive
determinant.

The proof composes three facts:

* the priority-ordered executable descriptor is invariant under every affine map with positive
  determinant (`descriptorOfPriorityOrderedPoints?_positiveAffine`), so the raw descriptor equals
  the descriptor computed after normalization;
* the normalization map is orientation preserving on nonzero-volume input
  (`viewingTransform_determinant_pos`), exposes `z = 0` for the first three points and
  `z = -(V ^ 2) < 0` for the fourth (`viewingTransform_applyPoint_*`), and keeps the volume
  nonzero (`viewingTransform_orientedVolume_ne_zero`);
* the local calibration
  `descriptorOfPriorityOrderedPoints?_eq_some_iff_source` applies to the normalized quadruple.

## Pipeline composition

`descriptorAt?_sound` and `universalDescriptor?_sound` already relate a successful production
outcome to the independent declarative meaning, retaining the actual `tracked.highestFirst`
coordinate correspondence and the emitted pseudo label
`classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons`.  The predicate
`ArbitraryFrameSourceConformance` and the theorems
`declarativeLocalizedOccurrenceUniversalDescriptor_sourceCalibrated`,
`descriptorAt?_sourceCalibrated` and `universalDescriptor?_sourceCalibrated` add the arbitrary-frame
geometric calibration to that meaning: the same actual points, at the same `highestFirst`
positions, become source-calibrated after the explicit normalization, while the emitted pseudo
label is unchanged.

## What is *not* claimed

* `T` is a general rational affine map; it may shear and scale.  This is **not** a Euclidean
  motion, a rigid rotation, or a physical distance-preserving viewing change, and no Euclidean
  or metric claim is made.
* The results concern the geometric calibration of the `R/S` reading and of the executable
  descriptor tail `descriptorOfPriorityOrderedPoints?`.  They do **not** claim correctness of CIP
  priority ranking, of the tracked insertion order, or of the pseudoasymmetric chemistry behind
  `classifyTetrahedralRSPseudo`; those remain separate obligations supplied by the production
  pipeline's own soundness theorems.
* No claim is made when the executable descriptor refuses (`none`); only the positive
  `= some raw` reading is interpreted, and the universal lift is conditional on success.
-/

/-- The explicit normalization transform for the ordered quadruple `first second third fourth`.
This is the constructive transform of `TetrahedralAffineViewingNormalization`. -/
def normalizationT (first second third fourth : CartesianPoint3) :
    RationalAffineFrameTransform :=
  TetrahedralAffineViewingNormalization.viewingTransform first second third fourth

/-! ## Positive-determinant invariance of the executable descriptor tail

The local lemmas below give the sign-cancellation fact used by the geometric core.  They are
stated directly so that this module depends only on the calibration and normalization modules;
the same list-level fact is also available publicly as
`CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_orientationPreservingAffine`. -/

/-- Multiplication by a strictly positive rational does not change the exact descriptor reading. -/
private theorem descriptorOfOrientedVolume?_positive_mul
    (factor volume : ℚ) (factorPositive : 0 < factor) :
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? (factor * volume) =
      CertifiedLocalizedCIPInput.descriptorOfOrientedVolume? volume := by
  unfold CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
  by_cases volumePositive : 0 < volume
  · have mappedPositive : 0 < factor * volume := mul_pos factorPositive volumePositive
    simp [volumePositive, mappedPositive, not_lt_of_ge volumePositive.le,
      not_lt_of_ge mappedPositive.le]
  · by_cases volumeNegative : volume < 0
    · have mappedNegative : factor * volume < 0 :=
        mul_neg_of_pos_of_neg factorPositive volumeNegative
      simp [volumeNegative, mappedNegative]
    · have volumeZero : volume = 0 :=
        le_antisymm (not_lt.mp volumePositive) (not_lt.mp volumeNegative)
      simp [volumeZero]

/-- The priority-ordered executable descriptor is invariant under every positive-determinant
rational affine coordinate change, including every refusal branch. -/
private theorem descriptorOfPriorityOrderedPoints?_positiveAffine
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    ∀ points : List CartesianPoint3,
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
          (points.map transform.applyPoint) =
        CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? points
  | [] => rfl
  | first :: rest => by
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              cases rest with
              | nil => rfl
              | cons fourth rest =>
                  cases rest with
                  | cons fifth rest => rfl
                  | nil =>
                      simp only [List.map_cons, List.map_nil,
                        CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?]
                      rw [RationalAffineFrameTransform.orientedVolume_applyPoint,
                        descriptorOfOrientedVolume?_positive_mul
                          transform.determinant _ orientationPreserving]

/-! ## Geometric core: arbitrary nonzero-volume quadruples -/

/-- **Arbitrary-frame source conformance of the exact tetrahedral descriptor.**

For an ordered quadruple of rational points with nonzero oriented volume, the executable
descriptor of the raw priority-ordered quadruple is `some raw` exactly when the source-calibrated
reading of the *normalized* quadruple (all four points mapped by the explicit transform
`normalizationT`) is `raw`.  The normalization is orientation preserving, so the raw descriptor is
unchanged; the normalized quadruple has the first three points on `z = 0` and the fourth at
`z = -(V ^ 2) < 0`, so the local viewing calibration applies. -/
theorem descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_normalized
    (first second third fourth : CartesianPoint3) (descriptor : RS)
    (volumeNonzero :
      TetrahedralAffineViewingNormalization.frameVolume first second third fourth ≠ 0) :
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
        [first, second, third, fourth] = some descriptor ↔
      CIPTetrahedralViewingCalibration.SourceCalibratedDescriptor
        ([first, second, third, fourth].map
          (normalizationT first second third fourth).applyPoint) descriptor := by
  have orientationPreserving :
      0 < (normalizationT first second third fourth).determinant :=
    TetrahedralAffineViewingNormalization.viewingTransform_determinant_pos
      first second third fourth volumeNonzero
  have affineInvariance :
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
          ([first, second, third, fourth].map
            (normalizationT first second third fourth).applyPoint) =
        CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
          [first, second, third, fourth] :=
    descriptorOfPriorityOrderedPoints?_positiveAffine
      (normalizationT first second third fourth) orientationPreserving
      [first, second, third, fourth]
  have firstHeight :
      ((normalizationT first second third fourth).applyPoint first).z = 0 := by
    rw [normalizationT,
      TetrahedralAffineViewingNormalization.viewingTransform_applyPoint_first]
    rfl
  have secondHeight :
      ((normalizationT first second third fourth).applyPoint second).z = 0 := by
    rw [normalizationT]
    exact TetrahedralAffineViewingNormalization.viewingTransform_applyPoint_second_z
      first second third fourth
  have thirdHeight :
      ((normalizationT first second third fourth).applyPoint third).z = 0 := by
    rw [normalizationT]
    exact TetrahedralAffineViewingNormalization.viewingTransform_applyPoint_third_z
      first second third fourth
  have fourthDepth :
      ((normalizationT first second third fourth).applyPoint fourth).z =
        -(TetrahedralAffineViewingNormalization.frameVolume
          first second third fourth) ^ 2 := by
    rw [normalizationT]
    exact TetrahedralAffineViewingNormalization.viewingTransform_applyPoint_fourth_z
      first second third fourth
  have behind :
      -(TetrahedralAffineViewingNormalization.frameVolume
        first second third fourth) ^ 2 < 0 := by
    have volumeSquaredPositive :
        0 < (TetrahedralAffineViewingNormalization.frameVolume
          first second third fourth) ^ 2 :=
      sq_pos_of_ne_zero volumeNonzero
    linarith
  have calibrated :=
    CIPTetrahedralViewingCalibration.descriptorOfPriorityOrderedPoints?_eq_some_iff_source
      ((normalizationT first second third fourth).applyPoint first)
      ((normalizationT first second third fourth).applyPoint second)
      ((normalizationT first second third fourth).applyPoint third)
      ((normalizationT first second third fourth).applyPoint fourth)
      0 (-(TetrahedralAffineViewingNormalization.frameVolume
        first second third fourth) ^ 2)
      firstHeight secondHeight thirdHeight fourthDepth behind descriptor
  rw [← affineInvariance]
  simpa only [List.map_cons, List.map_nil] using calibrated

/-- List-facing form of arbitrary-frame source conformance.  If `points` is the four-element
list `[first, second, third, fourth]` and the oriented volume of that quadruple is nonzero, the
raw executable descriptor is `some raw` exactly when the normalized list is source-calibrated. -/
theorem descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_points
    (points : List CartesianPoint3) (descriptor : RS)
    (first second third fourth : CartesianPoint3)
    (pointsEq : points = [first, second, third, fourth])
    (volumeNonzero :
      TetrahedralAffineViewingNormalization.frameVolume first second third fourth ≠ 0) :
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? points = some descriptor ↔
      CIPTetrahedralViewingCalibration.SourceCalibratedDescriptor
        (points.map (normalizationT first second third fourth).applyPoint) descriptor := by
  rw [pointsEq]
  exact descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_normalized
    first second third fourth descriptor volumeNonzero

/-- **Existential form of arbitrary-frame source conformance.**  Every nonzero-volume ordered
quadruple has an explicit orientation-preserving rational affine normalization `T` — namely
`normalizationT` — for which the raw executable descriptor is `some raw` exactly when the
normalized list is source-calibrated as `raw`.  The witness is the constructive transform, not a
choice-selected one. -/
theorem exists_normalizationT_sourceConformance
    (first second third fourth : CartesianPoint3) (descriptor : RS)
    (volumeNonzero :
      TetrahedralAffineViewingNormalization.frameVolume first second third fourth ≠ 0) :
    ∃ transform : RationalAffineFrameTransform,
      0 < transform.determinant ∧
        transform = normalizationT first second third fourth ∧
        (CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?
            [first, second, third, fourth] = some descriptor ↔
          CIPTetrahedralViewingCalibration.SourceCalibratedDescriptor
            ([first, second, third, fourth].map transform.applyPoint) descriptor) := by
  refine ⟨normalizationT first second third fourth,
    TetrahedralAffineViewingNormalization.viewingTransform_determinant_pos
      first second third fourth volumeNonzero, rfl, ?_⟩
  exact descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_normalized
    first second third fourth descriptor volumeNonzero

/-! ## Composition with the production descriptor pipeline -/

/-- The arbitrary-frame geometric conclusion extracted from a declarative universal-descriptor
meaning at a fixed Rule-3 evaluation budget.

It retains the evidence record produced by the production pipeline (so the actual
`tracked.highestFirst` coordinate correspondence is available), the raw `R/S` sense, the four
actual coordinate points, their nonzero oriented volume, the emitted pseudo-classifier equality
`descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons`, and the
source-calibrated reading of the same points after the explicit normalization.

This predicate says nothing about priority ranking or pseudoasymmetric chemistry; it only adds
the geometric calibration to an already-derived declarative meaning. -/
def ArbitraryFrameSourceConformance
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel) : Prop :=
  ∃ (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (raw : RS) (first second third fourth : CartesianPoint3),
    input.DeclarativeLocalizedOccurrenceUniversalSpatialEvidence target view evaluationBudget
        evidence ∧
      evidence.points = [first, second, third, fourth] ∧
      TetrahedralAffineViewingNormalization.frameVolume first second third fourth ≠ 0 ∧
      List.Forall₂
        (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
          (evidence.base.cursorAt index) point)
        evidence.tracked.highestFirst evidence.points ∧
      descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons ∧
      CIPTetrahedralViewingCalibration.SourceCalibratedDescriptor
        (evidence.points.map
          (normalizationT first second third fourth).applyPoint) raw

/-- Every declarative universal-descriptor meaning at a Rule-3 budget carries arbitrary-frame
source conformance.  The proof only decomposes the declarative meaning, reads the nonzero volume
from the rational `R/S` sign, extracts the actual `highestFirst` correspondence, and applies the
geometric core theorem to the actual evidence points. -/
theorem declarativeLocalizedOccurrenceUniversalDescriptor_sourceCalibrated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (declarative : input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor) :
    ArbitraryFrameSourceConformance input target view evaluationBudget descriptor := by
  unfold CertifiedLocalizedCIPInput.DeclarativeLocalizedOccurrenceUniversalDescriptor
    at declarative
  obtain ⟨evidence, raw, spatialEvidence, rational, descriptorEq⟩ := declarative
  unfold CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor at rational
  obtain ⟨first, second, third, fourth, pointsEq, sign⟩ := rational
  have volumeNonzero :
      TetrahedralAffineViewingNormalization.frameVolume first second third fourth ≠ 0 := by
    unfold TetrahedralAffineViewingNormalization.frameVolume
    cases raw with
    | R => exact ne_of_lt sign
    | S => exact ne_of_gt sign
  have executable :
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? evidence.points =
        some raw := by
    rw [pointsEq]
    have rationalLiteral : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        [first, second, third, fourth] raw := by
      exact ⟨first, second, third, fourth, rfl, sign⟩
    have orientedSign :=
      (CIPTetrahedralViewingCalibration.rationalTetrahedralDescriptor_iff_descriptorOfOrientedVolume
        first second third fourth raw).mp rationalLiteral
    change CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?
      (CartesianPoint3.orientedVolume first second third fourth) = some raw
    exact orientedSign
  have spatialEvidenceUnfolded :
      input.RealTetrahedralCenterNode target.1.node evidence.center ∧
        input.DeclarativeLocalizedOccurrenceFourLigandFrame target evidence.base ∧
        input.DeclarativeLocalizedOccurrenceUniversalKeyFrame target view evidence.base
          evaluationBudget evidence.keys ∧
        input.DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder
          evidence.keys evidence.tracked ∧
        List.Forall₂
          (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
            (evidence.base.cursorAt index) point)
          evidence.tracked.highestFirst evidence.points := spatialEvidence
  have highestFirstCorrespondence :
      List.Forall₂
        (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
          (evidence.base.cursorAt index) point)
        evidence.tracked.highestFirst evidence.points :=
    spatialEvidenceUnfolded.2.2.2.2
  have sourceConformance :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_points
      evidence.points raw first second third fourth pointsEq volumeNonzero).mp executable
  exact ⟨evidence, raw, first, second, third, fourth, spatialEvidence, pointsEq,
    volumeNonzero, highestFirstCorrespondence, descriptorEq, sourceConformance⟩

/-- **Source conformance of the parameterized production descriptor at every Rule-3 budget.**

If `descriptorAt?` succeeds, the actual declarative meaning holds at that budget
(`descriptorAt?_sound`), and its evidence points are source-calibrated after the explicit
orientation-preserving normalization.  The conclusion retains the evidence record, the actual
`tracked.highestFirst` coordinate correspondence, and the unchanged emitted pseudo label
`classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons`. -/
theorem descriptorAt?_sourceCalibrated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat)
    (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (computed : input.descriptorAt? target view evaluationBudget = some descriptor) :
    ArbitraryFrameSourceConformance input target view evaluationBudget descriptor :=
  declarativeLocalizedOccurrenceUniversalDescriptor_sourceCalibrated input target view
    evaluationBudget descriptor
    (input.descriptorAt?_sound target view evaluationBudget descriptor computed)

/-- **Source conformance of the universal production descriptor, lifted through its existing
success theorem.**

If `universalDescriptor?` succeeds, there is a four-ligand base actually returned by the
executable reader such that the same arbitrary-frame source conformance holds at the Rule-3
budget computed by `prepareUniversalRule3EvaluationOutcome` from that base.  The refusal branch is
not reinterpreted: the theorem is conditional on success. -/
theorem universalDescriptor?_sourceCalibrated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (computed : input.universalDescriptor? target view = some descriptor) :
    ∃ (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel),
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        ArbitraryFrameSourceConformance input target view
          (CertifiedLocalizedCIPInput.prepareUniversalRule3EvaluationOutcome
            input base.cursors target view).1
          descriptor := by
  obtain ⟨base, baseComputed, declarative⟩ :=
    input.universalDescriptor?_sound target view descriptor computed
  refine ⟨base, baseComputed, ?_⟩
  exact declarativeLocalizedOccurrenceUniversalDescriptor_sourceCalibrated input target view
    (CertifiedLocalizedCIPInput.prepareUniversalRule3EvaluationOutcome
      input base.cursors target view).1 descriptor
    declarative

end CIPTetrahedralArbitraryFrameSourceConformance
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The geometric core, its list-facing and existential forms, and the three pipeline compositions
are checked to use only the standard kernel principles (`propext`, `Classical.choice`,
`Quot.sound`). -/

assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralArbitraryFrameSourceConformance.descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_normalized
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralArbitraryFrameSourceConformance.descriptorOfPriorityOrderedPoints?_eq_some_iff_source_of_points
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralArbitraryFrameSourceConformance.exists_normalizationT_sourceConformance
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralArbitraryFrameSourceConformance.declarativeLocalizedOccurrenceUniversalDescriptor_sourceCalibrated
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralArbitraryFrameSourceConformance.descriptorAt?_sourceCalibrated
assert_kernel_only TetraStereo.OneCenter.CIPTetrahedralArbitraryFrameSourceConformance.universalDescriptor?_sourceCalibrated
