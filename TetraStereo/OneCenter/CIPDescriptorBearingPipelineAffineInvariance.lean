import TetraStereo.OneCenter.CIPDescriptorBearingRule3Through5FrameAffineInvariance
import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5Exact

set_option autoImplicit false

/-!
# Affine invariance of the descriptor-bearing tetrahedral pipeline

This file transports the production Rules-1a--5 key frame through strict ligand ordering and
exact coordinate collection to the emitted tetrahedral descriptor.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

@[simp] theorem LocalizedOccurrenceFourLigandFrame.cursorAt_mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) (index : Fin 4) :
    (frame.mapSpatialPoints mapPoint).cursorAt index =
      (frame.cursorAt index).mapSpatialPoints mapPoint := by
  unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    LocalizedOccurrenceFourLigandFrame.mapSpatialPoints
  simp

@[simp] theorem LocalizedOccurrenceRule3Through5KeyFrame.keyAt_mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) (index : Fin 4) :
    (frame.mapSpatialPoints mapPoint).keyAt index =
      (frame.keyAt index).mapSpatialPoints mapPoint := by
  unfold LocalizedOccurrenceRule3Through5KeyFrame.keyAt
    LocalizedOccurrenceRule3Through5KeyFrame.mapSpatialPoints
  simp [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints,
    LocalizedOccurrenceRule3Through5Key.mapSpatialPoints]

@[simp] theorem compareLocalizedRerootCompoundThroughRule5_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedRerootCompoundRule45Key) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootCompoundThroughRule5
        (left.mapSpatialPoints mapPoint) (right.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootCompoundThroughRule5 left right := by
  unfold compareLocalizedRerootCompoundThroughRule5
  simp only [LocalizedRerootCompoundRule45Key.mapSpatialPoints,
    compareLocalizedRerootCompoundRule4bcKeys_mapSpatialPoints,
    compareLocalizedRerootCompoundRule5Readings_mapSpatialPoints]

@[simp] theorem compareLocalizedOccurrenceRule3Through5At_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) (left right : Fin 4) :
    (input.mapSpatialPoints mapPoint).compareLocalizedOccurrenceRule3Through5At
        (frame.mapSpatialPoints mapPoint) left right =
      input.compareLocalizedOccurrenceRule3Through5At frame left right := by
  unfold compareLocalizedOccurrenceRule3Through5At
  simp only [LocalizedOccurrenceRule3Through5KeyFrame.keyAt_mapSpatialPoints,
    LocalizedOccurrenceRule3Through5Key.mapSpatialPoints,
    compareLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints]
  cases input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 <;>
    simp [localizedOccurrenceRule45ComparisonRecord,
      compareLocalizedRerootCompoundThroughRule5_mapSpatialPoints]

@[simp] theorem compareLocalizedOccurrenceRule3Through5At?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) (left right : Fin 4) :
    (input.mapSpatialPoints mapPoint).compareLocalizedOccurrenceRule3Through5At?
        (frame.mapSpatialPoints mapPoint) left right =
      input.compareLocalizedOccurrenceRule3Through5At? frame left right := by
  simp [compareLocalizedOccurrenceRule3Through5At?,
    compareLocalizedOccurrenceRule3Through5At_mapSpatialPoints]

@[simp] theorem localizedOccurrenceRule3Through5TrackedOrder?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedOccurrenceRule3Through5TrackedOrder?
        (frame.mapSpatialPoints mapPoint) =
      input.localizedOccurrenceRule3Through5TrackedOrder? frame := by
  unfold localizedOccurrenceRule3Through5TrackedOrder?
  congr 1
  funext left right
  exact compareLocalizedOccurrenceRule3Through5At?_mapSpatialPoints
    input frame mapPoint left right

@[simp] theorem localizedOccurrenceRule3Through5OrderPairStrict_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) (left right : Fin 4) :
    (input.mapSpatialPoints mapPoint).localizedOccurrenceRule3Through5OrderPairStrict
        (frame.mapSpatialPoints mapPoint) left right =
      input.localizedOccurrenceRule3Through5OrderPairStrict frame left right := by
  unfold localizedOccurrenceRule3Through5OrderPairStrict
  rw [compareLocalizedOccurrenceRule3Through5At_mapSpatialPoints]

@[simp] theorem localizedOccurrenceRule3Through5OrderCoherent_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ order,
    (input.mapSpatialPoints mapPoint).localizedOccurrenceRule3Through5OrderCoherent
        (frame.mapSpatialPoints mapPoint) order =
      input.localizedOccurrenceRule3Through5OrderCoherent frame order
  | [] => rfl
  | left :: rest => by
      unfold localizedOccurrenceRule3Through5OrderCoherent
      have predicateEq :
          (fun right =>
            (input.mapSpatialPoints mapPoint).localizedOccurrenceRule3Through5OrderPairStrict
              (frame.mapSpatialPoints mapPoint) left right) =
            (fun right =>
              input.localizedOccurrenceRule3Through5OrderPairStrict frame left right) := by
        funext right
        exact localizedOccurrenceRule3Through5OrderPairStrict_mapSpatialPoints
          input frame mapPoint left right
      have allEq :
          rest.all
              (localizedOccurrenceRule3Through5OrderPairStrict
                  (input.mapSpatialPoints mapPoint)
                  (frame.mapSpatialPoints mapPoint) left) =
            rest.all (input.localizedOccurrenceRule3Through5OrderPairStrict frame left) :=
        congrArg (fun predicate => rest.all predicate) predicateEq
      rw [allEq, localizedOccurrenceRule3Through5OrderCoherent_mapSpatialPoints]

@[simp] theorem safeLocalizedOccurrenceRule3Through5TrackedOrder?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).safeLocalizedOccurrenceRule3Through5TrackedOrder?
        (frame.mapSpatialPoints mapPoint) =
      input.safeLocalizedOccurrenceRule3Through5TrackedOrder? frame := by
  unfold safeLocalizedOccurrenceRule3Through5TrackedOrder?
  rw [localizedOccurrenceRule3Through5TrackedOrder?_mapSpatialPoints]
  cases input.localizedOccurrenceRule3Through5TrackedOrder? frame with
  | none => rfl
  | some tracked =>
      simp

@[simp] theorem localizedOccurrenceDescriptorCenter?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedOccurrenceDescriptorCenter?
        (target.mapSpatialPoints mapPoint) =
      input.localizedOccurrenceDescriptorCenter? target := by
  unfold localizedOccurrenceDescriptorCenter? realTetrahedralCenterAtNode?
  have nodeEq :
      (target.mapSpatialPoints mapPoint).1.node = target.1.node := rfl
  rw [nodeEq]
  by_cases real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · simp only [if_pos real]
    cases currentEq : target.1.node.current? with
    | none => rfl
    | some atom =>
        unfold tetrahedralCenterAt? tetrahedralCenterSet
        have centerSetEq :
            (input.mapSpatialPoints mapPoint).moleculeGraph.tetrahedralCenterSet =
              input.moleculeGraph.tetrahedralCenterSet := by
          rw [moleculeGraph_mapSpatialPoints]
        by_cases detected : atom ∈ input.moleculeGraph.tetrahedralCenterSet
        · have mappedDetected :
              atom ∈ (input.mapSpatialPoints mapPoint).moleculeGraph.tetrahedralCenterSet := by
            simpa [centerSetEq] using detected
          simp only [dif_pos detected, dif_pos mappedDetected]
        · simp [detected]
  · simp [real]

@[simp] theorem localizedOccurrenceLigandFrame?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedOccurrenceLigandFrame?
        (target.mapSpatialPoints mapPoint) =
      (input.localizedOccurrenceLigandFrame? target).map
        (List.map fun cursor => cursor.mapSpatialPoints mapPoint) := by
  unfold localizedOccurrenceLigandFrame?
  exact localizedRerootChildren?_mapSpatialPoints input mapPoint
    { occurrence := target, previous? := none }

@[simp] theorem localizedOccurrenceFourLigandFrame?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedOccurrenceFourLigandFrame?
        (target.mapSpatialPoints mapPoint) =
      (input.localizedOccurrenceFourLigandFrame? target).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold localizedOccurrenceFourLigandFrame?
  rw [localizedOccurrenceLigandFrame?_mapSpatialPoints]
  cases input.localizedOccurrenceLigandFrame? target with
  | none => rfl
  | some cursors =>
      by_cases lengthEq : cursors.length = 4
      · have mappedLength :
            (cursors.map fun cursor => cursor.mapSpatialPoints mapPoint).length = 4 := by
          simpa using lengthEq
        simp [lengthEq, mappedLength, LocalizedOccurrenceFourLigandFrame.mapSpatialPoints]
      · simp [lengthEq]

@[simp] theorem localizedRerootCursorSpatialPoint?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRerootCursorSpatialPoint?
        (cursor.mapSpatialPoints mapPoint) =
      (input.localizedRerootCursorSpatialPoint? cursor).map mapPoint := by
  unfold localizedRerootCursorSpatialPoint?
  have nodeCurrentEq :
      (cursor.mapSpatialPoints mapPoint).occurrence.1.node.current? =
        cursor.occurrence.1.node.current? := rfl
  rw [nodeCurrentEq]
  cases cursor.occurrence.1.node.current? with
  | none => rfl
  | some atom => exact spatialPointAt?_mapSpatialPoints input mapPoint atom

private theorem mapM_localizedRerootCursorSpatialPoint_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    ∀ order : List (Fin 4),
      order.mapM (fun index =>
        (input.mapSpatialPoints mapPoint).localizedRerootCursorSpatialPoint?
          ((base.mapSpatialPoints mapPoint).cursorAt index)) =
        (order.mapM (fun index =>
          input.localizedRerootCursorSpatialPoint? (base.cursorAt index))).map
            (List.map mapPoint)
  | order => by
      exact listMapM_map_of_natural
        (fun index : Fin 4 => index) mapPoint
        (fun index => input.localizedRerootCursorSpatialPoint? (base.cursorAt index))
        (fun index =>
          (input.mapSpatialPoints mapPoint).localizedRerootCursorSpatialPoint?
            ((base.mapSpatialPoints mapPoint).cursorAt index))
        (by
          intro index
          dsimp
          rw [LocalizedOccurrenceFourLigandFrame.cursorAt_mapSpatialPoints,
            localizedRerootCursorSpatialPoint?_mapSpatialPoints])
        order

def LocalizedOccurrenceRule3Through5SpatialEvidence.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedOccurrenceRule3Through5SpatialEvidence
      carrierFuel :=
  { center := evidence.center
    base := evidence.base.mapSpatialPoints mapPoint
    keys := evidence.keys.mapSpatialPoints mapPoint
    tracked := evidence.tracked
    points := evidence.points.map mapPoint }

theorem localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?
          (input.mapSpatialPoints transform.applyPoint)
          (target.mapSpatialPoints transform.applyPoint)
          (view.mapSpatialPoints transform.applyPoint) =
      (input.localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?
        target view).map
          (fun evidence => evidence.mapSpatialPoints transform.applyPoint) := by
  unfold localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?
  rw [localizedOccurrenceDescriptorCenter?_mapSpatialPoints,
    localizedOccurrenceFourLigandFrame?_mapSpatialPoints]
  cases input.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center =>
      cases input.localizedOccurrenceFourLigandFrame? target with
      | none => rfl
      | some base =>
          simp
          rw [buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?_affine
            input target view base transform determinantNonzero]
          cases input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?
              target view base with
          | none => rfl
          | some keys =>
              simp only [Option.map_some, Option.bind_some]
              rw [safeLocalizedOccurrenceRule3Through5TrackedOrder?_mapSpatialPoints]
              cases input.safeLocalizedOccurrenceRule3Through5TrackedOrder? keys with
              | none => rfl
              | some tracked =>
                  simp only [Option.bind_some]
                  have pointsNatural :
                      tracked.highestFirst.mapM (fun index =>
                          (input.localizedRerootCursorSpatialPoint?
                            (base.cursorAt index)).map transform.applyPoint) =
                        (tracked.highestFirst.mapM (fun index =>
                          input.localizedRerootCursorSpatialPoint?
                            (base.cursorAt index))).map
                              (List.map transform.applyPoint) :=
                    listMapM_map_of_natural
                      (fun index : Fin 4 => index) transform.applyPoint
                      (fun index => input.localizedRerootCursorSpatialPoint?
                        (base.cursorAt index))
                      (fun index => (input.localizedRerootCursorSpatialPoint?
                        (base.cursorAt index)).map transform.applyPoint)
                      (fun index => rfl) tracked.highestFirst
                  rw [pointsNatural]
                  cases tracked.highestFirst.mapM (fun index =>
                      input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) <;>
                    simp [LocalizedOccurrenceRule3Through5SpatialEvidence.mapSpatialPoints]

private theorem descriptorOfOrientedVolume?_positive_mul
    (factor volume : ℚ) (factorPositive : 0 < factor) :
    descriptorOfOrientedVolume? (factor * volume) =
      descriptorOfOrientedVolume? volume := by
  unfold descriptorOfOrientedVolume?
  by_cases volumeNegative : volume < 0
  · have mappedNegative : factor * volume < 0 :=
      mul_neg_of_pos_of_neg factorPositive volumeNegative
    simp [volumeNegative, mappedNegative]
  · by_cases volumePositive : 0 < volume
    · have mappedPositive : 0 < factor * volume := mul_pos factorPositive volumePositive
      have mappedNotNegative : ¬ factor * volume < 0 := not_lt_of_ge mappedPositive.le
      simp [volumeNegative, volumePositive, mappedPositive, mappedNotNegative]
    · have volumeZero : volume = 0 :=
        le_antisymm (not_lt.mp volumePositive) (not_lt.mp volumeNegative)
      simp [volumeZero]

/-- A negative exact affine determinant reverses the tetrahedral descriptor, including the
degenerate `none` case. -/
theorem descriptorOfOrientedVolume?_negative_mul
    (factor volume : ℚ) (factorNegative : factor < 0) :
    descriptorOfOrientedVolume? (factor * volume) =
      (descriptorOfOrientedVolume? volume).map RS.swap := by
  unfold descriptorOfOrientedVolume?
  by_cases volumeNegative : volume < 0
  · have mappedPositive : 0 < factor * volume :=
      mul_pos_of_neg_of_neg factorNegative volumeNegative
    have mappedNotNegative : ¬ factor * volume < 0 := not_lt_of_ge mappedPositive.le
    simp [volumeNegative, mappedPositive, mappedNotNegative, RS.swap]
  · by_cases volumePositive : 0 < volume
    · have mappedNegative : factor * volume < 0 :=
        mul_neg_of_neg_of_pos factorNegative volumePositive
      simp [volumeNegative, volumePositive, mappedNegative, RS.swap]
    · have volumeZero : volume = 0 :=
        le_antisymm (not_lt.mp volumePositive) (not_lt.mp volumeNegative)
      simp [volumeZero]

theorem descriptorOfPriorityOrderedPoints?_orientationPreservingAffine
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    ∀ points : List CartesianPoint3,
      descriptorOfPriorityOrderedPoints?
          (points.map transform.applyPoint) =
        descriptorOfPriorityOrderedPoints? points
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
                        descriptorOfPriorityOrderedPoints?]
                      rw [RationalAffineFrameTransform.orientedVolume_applyPoint,
                        descriptorOfOrientedVolume?_positive_mul
                          transform.determinant _ orientationPreserving]

/-- Exact orientation-reversing affine naturality of tetrahedral descriptors. -/
theorem descriptorOfPriorityOrderedPoints?_orientationReversingAffine
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0) :
    ∀ points : List CartesianPoint3,
      descriptorOfPriorityOrderedPoints? (points.map transform.applyPoint) =
        (descriptorOfPriorityOrderedPoints? points).map RS.swap
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
                        descriptorOfPriorityOrderedPoints?]
                      rw [RationalAffineFrameTransform.orientedVolume_applyPoint,
                        descriptorOfOrientedVolume?_negative_mul
                          transform.determinant _ orientationReversing]

/-- The final descriptor-bearing `R/S` or `r/s` result is independent of every exact rational
orientation-preserving affine coordinate-frame choice.  All success and refusal branches are
included. -/
theorem localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_orientationPreservingAffine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
          (input.mapSpatialPoints transform.applyPoint)
          (target.mapSpatialPoints transform.applyPoint)
          (view.mapSpatialPoints transform.applyPoint) =
      input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? target view := by
  unfold localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
  have determinantNonzero : transform.determinant ≠ 0 := ne_of_gt orientationPreserving
  rw [localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?_affine
    input target view transform determinantNonzero]
  cases evidenceEq :
      input.localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence? target view with
  | none => rfl
  | some evidence =>
      simp
      change
        (descriptorOfPriorityOrderedPoints?
            (evidence.points.map transform.applyPoint)).bind
              (fun raw => some (classifyTetrahedralRSPseudo raw
                evidence.tracked.pseudoComparisons)) =
          (descriptorOfPriorityOrderedPoints? evidence.points).bind
              (fun raw => some (classifyTetrahedralRSPseudo raw
                evidence.tracked.pseudoComparisons))
      rw [descriptorOfPriorityOrderedPoints?_orientationPreservingAffine
        transform orientationPreserving]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
