import TetraStereo.OneCenter.CIPRule3AffineInvariance

set_option autoImplicit false

/-!
# Affine naturality of descriptor-bearing Rules-3--5 endpoint keys

This module transports an already compiled occurrence-local Rules-3--5 endpoint key across a
coordinate-only input change. Rule-3 spatial observations retain the same geometry by the exact
affine theorem; the cumulative Rules-4b, 4c, and 5 data are coordinate-independent. The transport
is proved to preserve every nested comparator and therefore the selected endpoint priority. This
discharges the remaining hypothesis of the descriptor-bearing Rule-3 spatial theorem.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def LocalizedRule3SpatialNodeResult.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (result : input.LocalizedRule3SpatialNodeResult)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3SpatialNodeResult :=
  { left := result.left
    right := result.right
    unit := result.unit.mapSpatialPoints mapPoint }

/-- Reading Rule-3 geometry at an arbitrary provenance node commutes with every invertible affine
coordinate change, including the outer unresolved-unit refusal and inner structural-nonunit case. -/
theorem localizedRule3SpatialNode?_affine
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3SpatialNode? node =
      (input.localizedRule3SpatialNode? node).map
        (Option.map fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedRule3SpatialNode?
  rw [moleculeGraph_mapSpatialPoints]
  by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
  · simp only [if_pos real]
    cases currentEq : node.current? with
    | none => rfl
    | some current =>
        cases parentEq : node.parent? with
        | none => rfl
        | some parent =>
            by_cases doubleBond : input.moleculeGraph.bond parent current = 2
            · simp only [if_pos doubleBond]
              rw [input.localizedRule3SpatialUnit?_affine parent current transform
                determinantNonzero]
              cases input.localizedRule3SpatialUnit? parent current <;>
                simp [LocalizedRule3SpatialNodeResult.mapSpatialPoints]
            · simp [doubleBond]
  · simp [real]

def LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRerootRecursiveRule3SpatialKey :=
  { constitutional := key.constitutional
    observations := key.observations.map fun layer =>
      layer.map fun entry => (entry.1, entry.2.mapSpatialPoints mapPoint)
    rule3 := key.rule3 }

def LocalizedRerootCumulativeRule45Key.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCumulativeRule45Key)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRerootCumulativeRule45Key :=
  { constitutional := key.constitutional
    descriptor := key.descriptor
    labels := key.labels
    rankedLabels := key.rankedLabels }

def LocalizedRerootRule4bcReading.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (reading : input.LocalizedRerootRule4bcReading)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRerootRule4bcReading :=
  { reference? := reading.reference?
    rule4bKey := reading.rule4bKey.mapSpatialPoints mapPoint
    rule4cKey := reading.rule4cKey.mapSpatialPoints mapPoint }

def LocalizedRerootCompoundRule4bcKey.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRerootCompoundRule4bcKey :=
  { rule4aKey := key.rule4aKey.mapSpatialPoints mapPoint
    references := key.references
    referenceCountPriority := key.referenceCountPriority
    readings := key.readings.map fun reading => reading.mapSpatialPoints mapPoint }

def LocalizedRerootRule5Reading.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (reading : input.LocalizedRerootRule5Reading)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRerootRule5Reading :=
  { prior := reading.prior.mapSpatialPoints mapPoint
    commonR := reading.commonR.mapSpatialPoints mapPoint
    commonS := reading.commonS.mapSpatialPoints mapPoint }

def LocalizedRerootCompoundRule45Key.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCompoundRule45Key)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRerootCompoundRule45Key :=
  { prior := key.prior.mapSpatialPoints mapPoint
    rule5Readings := key.rule5Readings.map fun reading =>
      reading.mapSpatialPoints mapPoint }

def LocalizedOccurrenceRule3Through5Key.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedOccurrenceRule3Through5Key)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedOccurrenceRule3Through5Key :=
  { rule3 := key.rule3.mapSpatialPoints mapPoint
    rule45 := key.rule45.mapSpatialPoints mapPoint }

def LocalizedRule3EndpointKeyFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3EndpointKeyFrame :=
  { first := frame.first
    second := frame.second
    firstKey := frame.firstKey.mapSpatialPoints mapPoint
    secondKey := frame.secondKey.mapSpatialPoints mapPoint }

/-- Mapping two lists pointwise through a comparison-preserving function preserves lexicographic
comparison. -/
theorem listCompareLex_map_invariant {α β : Type*}
    (mapValue : α → β) (compareSource : α → α → Ordering)
    (compareTarget : β → β → Ordering)
    (same : ∀ left right,
      compareTarget (mapValue left) (mapValue right) = compareSource left right) :
    ∀ left right,
      List.compareLex compareTarget (left.map mapValue) (right.map mapValue) =
        List.compareLex compareSource left right := by
  intro left
  induction left with
  | nil => intro right; cases right <;> rfl
  | cons head tail ih =>
      intro right
      cases right with
      | nil => rfl
      | cons other others =>
          simp only [List.map_cons, List.compareLex]
          rw [same]
          cases compareSource head other <;> simp [ih]

@[simp] theorem compareLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootRecursiveRule3SpatialKeys
        (left.mapSpatialPoints mapPoint) (right.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootRecursiveRule3SpatialKeys left right := by
  rfl

@[simp] theorem compareLocalizedRerootRule4bcReadingsByRule4b_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedRerootRule4bcReading) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootRule4bcReadingsByRule4b
        (left.mapSpatialPoints mapPoint) (right.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootRule4bcReadingsByRule4b left right := by
  rfl

@[simp] theorem compareLocalizedRerootCompoundRule4bReadings_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : List input.LocalizedRerootRule4bcReading) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootCompoundRule4bReadings
        (left.map fun reading => reading.mapSpatialPoints mapPoint)
        (right.map fun reading => reading.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootCompoundRule4bReadings left right := by
  exact listCompareLex_map_invariant _ _ _
    (compareLocalizedRerootRule4bcReadingsByRule4b_mapSpatialPoints input mapPoint) left right

@[simp] theorem compareLocalizedRerootCompoundRule4cReadings_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : List input.LocalizedRerootRule4bcReading) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootCompoundRule4cReadings
        (left.map fun reading => reading.mapSpatialPoints mapPoint)
        (right.map fun reading => reading.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootCompoundRule4cReadings left right := by
  exact listCompareLex_map_invariant _ _ _ (by intro first second; rfl) left right

/-- The cumulative Rules-4a--5 key comparator is coordinate-independent: transport leaves the
constitutional rule projections and the cumulative descriptor unchanged.  Kept private to avoid
importing `CIPRule45DependencyViewAffineInvariance`, which would close an import cycle through the
descriptor-bearing Rule-3 builder modules. -/
private theorem cumulativeRule45Keys_mapSpatialPoints_local
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootCumulativeRule45Keys
        (left.mapSpatialPoints mapPoint) (right.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootCumulativeRule45Keys left right :=
  rfl

/-- Coordinate transport preserves the complete compound Rules-4b/4c comparator.  The repaired
comparator observes the complete Rule-4a key first, so the transport of that gate is supplied by
`cumulativeRule45Keys_mapSpatialPoints_local`; the reference count and reading gates are the same
coordinate-independent data as before. -/
@[simp] theorem compareLocalizedRerootCompoundRule4bcKeys_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedRerootCompoundRule4bcKey) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootCompoundRule4bcKeys
        (left.mapSpatialPoints mapPoint) (right.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootCompoundRule4bcKeys left right := by
  unfold compareLocalizedRerootCompoundRule4bcKeys
  simp only [LocalizedRerootCompoundRule4bcKey.mapSpatialPoints,
    compareLex, Ordering.byKey,
    cumulativeRule45Keys_mapSpatialPoints_local,
    compareLocalizedRerootCompoundRule4bReadings_mapSpatialPoints,
    compareLocalizedRerootCompoundRule4cReadings_mapSpatialPoints]

@[simp] theorem compareLocalizedRerootCompoundRule5Readings_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (reference : RS) (left right : List input.LocalizedRerootRule5Reading) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootCompoundRule5Readings reference
        (left.map fun reading => reading.mapSpatialPoints mapPoint)
        (right.map fun reading => reading.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootCompoundRule5Readings reference left right := by
  apply listCompareLex_map_invariant
  intro first second
  cases reference <;> rfl

@[simp] theorem compareLocalizedRerootCompoundRule45Keys_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedRerootCompoundRule45Key) :
    (input.mapSpatialPoints mapPoint).compareLocalizedRerootCompoundRule45Keys
        (left.mapSpatialPoints mapPoint) (right.mapSpatialPoints mapPoint) =
      input.compareLocalizedRerootCompoundRule45Keys left right := by
  unfold compareLocalizedRerootCompoundRule45Keys
  simp only [LocalizedRerootCompoundRule45Key.mapSpatialPoints,
    compareLex, Ordering.byKey,
    compareLocalizedRerootCompoundRule4bcKeys_mapSpatialPoints,
    compareLocalizedRerootCompoundRule5Readings_mapSpatialPoints]

@[simp] theorem compareLocalizedOccurrenceRule3Through5Keys_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedOccurrenceRule3Through5Key) :
    (input.mapSpatialPoints mapPoint).compareLocalizedOccurrenceRule3Through5Keys
        (left.mapSpatialPoints mapPoint) (right.mapSpatialPoints mapPoint) =
      input.compareLocalizedOccurrenceRule3Through5Keys left right := by
  unfold compareLocalizedOccurrenceRule3Through5Keys
  simp only [LocalizedOccurrenceRule3Through5Key.mapSpatialPoints,
    compareLex, Ordering.byKey,
    compareLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints,
    compareLocalizedRerootCompoundRule45Keys_mapSpatialPoints]

@[simp] theorem localizedRule3EndpointPriority_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    (input.mapSpatialPoints mapPoint).localizedRule3EndpointPriority
        (frame.mapSpatialPoints mapPoint) =
      (input.localizedRule3EndpointPriority frame).mapSpatialPoints mapPoint := by
  unfold localizedRule3EndpointPriority
  simp only [LocalizedRule3EndpointKeyFrame.mapSpatialPoints]
  rw [compareLocalizedOccurrenceRule3Through5Keys_mapSpatialPoints]
  cases input.compareLocalizedOccurrenceRule3Through5Keys
      frame.firstKey frame.secondKey <;>
    rfl

/-- Unconditional affine naturality of the descriptor-bearing Rule-3 endpoint evaluator for an
already compiled occurrence-key frame. The nested Rules-3--5 comparator, nonstereogenic endpoint
outcomes, coordinate failures, and successful `seqCis/seqTrans` result all commute with transport. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_affine
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3DescriptorBearingSpatialUnit?
        left right
          (leftFrame.mapSpatialPoints transform.applyPoint)
          (rightFrame.mapSpatialPoints transform.applyPoint) =
      (input.localizedRule3DescriptorBearingSpatialUnit?
          left right leftFrame rightFrame).map
        (fun result => result.mapSpatialPoints transform.applyPoint) := by
  exact input.localizedRule3DescriptorBearingSpatialUnit?_affine_of_priorities
    left right leftFrame rightFrame transform
    (leftFrame.mapSpatialPoints transform.applyPoint)
    (rightFrame.mapSpatialPoints transform.applyPoint)
    (input.localizedRule3EndpointPriority_mapSpatialPoints
      transform.applyPoint leftFrame)
    (input.localizedRule3EndpointPriority_mapSpatialPoints
      transform.applyPoint rightFrame)
    determinantNonzero

/-- The generic two-candidate endpoint-frame compiler commutes with coordinate transport whenever
its occurrence-key callback does. This isolates the remaining deep-builder obligation at exactly
the callback that constructs one occurrence-local Rules-1a--5 key. -/
theorem buildLocalizedRule3EndpointKeyFrame?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (endpoint partner : input.Atom)
    (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keyOf : input.Atom → Option input.LocalizedOccurrenceRule3Through5Key)
    (mappedKeyOf : (input.mapSpatialPoints mapPoint).Atom →
      Option (input.mapSpatialPoints mapPoint).LocalizedOccurrenceRule3Through5Key)
    (keyNatural : ∀ reference,
      mappedKeyOf reference =
        (keyOf reference).map (fun key => key.mapSpatialPoints mapPoint)) :
    (input.mapSpatialPoints mapPoint).buildLocalizedRule3EndpointKeyFrame?
        endpoint partner mappedKeyOf =
      (input.buildLocalizedRule3EndpointKeyFrame? endpoint partner keyOf).map
        (fun frame => frame.mapSpatialPoints mapPoint) := by
  unfold buildLocalizedRule3EndpointKeyFrame?
  rw [localizedRule3ExplicitSubstituents_mapSpatialPoints]
  generalize candidatesEq : input.localizedRule3ExplicitSubstituents endpoint partner = candidates
  cases candidates with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          cases tail with
          | cons third tail => rfl
          | nil =>
              simp only
              rw [keyNatural first, keyNatural second]
              cases keyOf first <;> cases keyOf second <;>
                rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
