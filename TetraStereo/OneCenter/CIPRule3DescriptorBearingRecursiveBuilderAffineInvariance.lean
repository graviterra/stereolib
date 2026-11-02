import TetraStereo.OneCenter.CIPRule3CyclicDescriptorAffineInvariance
import TetraStereo.OneCenter.CIPRule3CoupledTopologyAffineInvariance
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3Key

set_option autoImplicit false

/-!
# Affine invariance of the production descriptor-bearing Rule-3 builder

The descriptor-bearing node reader and its mutually recursive key/frame compiler are the
production bridge from molecule-backed Rule-3 geometry to emitted recursive CIP keys.  This
module proves that the bridge depends on the represented molecule and its oriented geometry, not
on the choice of rational Cartesian frame.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

@[simp] theorem localizedRule3DescriptorBearingObservation_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (result : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3DescriptorBearingObservation
        (result.mapSpatialPoints mapPoint) =
      (input.localizedRule3DescriptorBearingObservation result).mapSpatialPoints mapPoint := by
  unfold localizedRule3DescriptorBearingObservation
  simp only [LocalizedRule3OccurrenceDescriptorBearingSpatialResult.mapSpatialPoints,
    LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints,
    LocalizedRule3EndpointPriority.mapSpatialPoints,
    LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
    LocalizedRule3EndpointKeyFrame.mapSpatialPoints]
  cases result.unit.leftPriority <;> cases result.unit.rightPriority <;> rfl

@[simp] theorem localizedRule3OddCumuleneDescriptorBearingObservation_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (result : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3OddCumuleneDescriptorBearingObservation
        (result.mapSpatialPoints mapPoint) =
      (input.localizedRule3OddCumuleneDescriptorBearingObservation result).mapSpatialPoints
        mapPoint := by
  unfold localizedRule3OddCumuleneDescriptorBearingObservation
  simp only [LocalizedRule3OddCumuleneDescriptorBearingSpatialResult.mapSpatialPoints,
    LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints,
    LocalizedRule3EndpointPriority.mapSpatialPoints,
    LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
    LocalizedRule3EndpointKeyFrame.mapSpatialPoints,
    LocalizedRule3OddCumuleneEndpointCursorFrame.mapSpatialPoints,
    LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
  cases result.unit.leftPriority <;> cases result.unit.rightPriority <;> rfl

@[simp] theorem localizedOccurrenceHasRule3DoubleBondEdge_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedOccurrenceHasRule3DoubleBondEdge
        (occurrence.mapSpatialPoints mapPoint) ↔
      input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  unfold LocalizedOccurrenceHasRule3DoubleBondEdge
  simp only [LocalizedCIPOccurrence.mapSpatialPoints,
    LocalizedCIPOccurrenceFrame.mapSpatialPoints, moleculeGraph_mapSpatialPoints]
  exact Iff.rfl

theorem localizedDescriptorBearingRule3StructuralNode?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedDescriptorBearingRule3StructuralNode?
        (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedDescriptorBearingRule3StructuralNode? occurrence).map
        (Option.map fun result => result.mapSpatialPoints mapPoint) := by
  unfold localizedDescriptorBearingRule3StructuralNode?
  rw [show (input.mapSpatialPoints mapPoint).LocalizedOccurrenceHasRule3DoubleBondEdge
      (occurrence.mapSpatialPoints mapPoint) ↔
        input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence by simp]
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence <;> simp [edge]

theorem localizedDescriptorBearingRule3NodeWith?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (transform : RationalAffineFrameTransform)
    (mappedRule3FrameOf :
      List ((input.mapSpatialPoints transform.applyPoint).LocalizedRerootCursor carrierFuel) →
        Option (input.mapSpatialPoints transform.applyPoint).LocalizedRule3CanonicalKeyFrame)
    (rule3FrameNatural : ∀ cursors,
      mappedRule3FrameOf
          (cursors.map fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
        (rule3FrameOf cursors).map
          (fun frame => frame.mapSpatialPoints transform.applyPoint))
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedDescriptorBearingRule3NodeWith?
        (target.mapSpatialPoints transform.applyPoint)
        (occurrence.mapSpatialPoints transform.applyPoint)
        (view.mapSpatialPoints transform.applyPoint) mappedRule3FrameOf
        (excluded.map fun unit => unit.mapSpatialPoints transform.applyPoint) =
      (input.localizedDescriptorBearingRule3NodeWith?
        target occurrence view rule3FrameOf excluded).map
          (Option.map fun result => result.mapSpatialPoints transform.applyPoint) := by
  classical
  unfold localizedDescriptorBearingRule3NodeWith?
  have edgeNatural := localizedOccurrenceHasRule3DoubleBondEdge_mapSpatialPoints
    input occurrence transform.applyPoint
  have excludedNatural (unit : input.LocalizedRule3PhysicalUnitId) :
      (excluded.map (fun value : input.LocalizedRule3PhysicalUnitId =>
          value.mapSpatialPoints transform.applyPoint)).contains
            (unit.mapSpatialPoints transform.applyPoint) =
        excluded.contains unit :=
    listContains_map_injective
      (fun value : input.LocalizedRule3PhysicalUnitId =>
        value.mapSpatialPoints transform.applyPoint)
      (LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input transform.applyPoint)
      unit excluded
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · have mappedEdge := edgeNatural.mpr edge
    simp only [dif_pos edge, dif_pos mappedEdge]
    rw [localizedRule3CumulatedAxisEntry?_mapSpatialPoints]
    cases entryEq : input.localizedRule3CumulatedAxisEntry? occurrence with
    | none => simp
    | some entry =>
        simp only [Option.map_some]
        cases entry with
        | internal initial previous => rfl
        | ringClosure initial closure =>
            simp only [LocalizedRule3CumulatedAxisEntry.mapSpatialPoints]
            rw [localizedRule3RequiredMonocyclicEZWith?_affine input target occurrence view
              rule3FrameOf transform mappedRule3FrameOf rule3FrameNatural determinantNonzero]
            cases resultEq : input.localizedRule3RequiredMonocyclicEZWith?
                target occurrence view rule3FrameOf with
            | some result =>
                simp only [Option.map_some, localizedRule3RequiredMonocyclicEZObservation_mapSpatialPoints,
                  physicalUnitId_mapSpatialPoints]
                rw [excludedNatural]
                split <;> rfl
            | none =>
                simp only [Option.map_none]
                rw [localizedRule3CyclicAuthorityRoute?_mapSpatialPoints]
                cases routeEq : input.localizedRule3CyclicAuthorityRoute? occurrence with
                | none => simp
                | some route =>
                    simp only [Option.map_some]
                    cases route with
                    | fullyCyclicCumulene initial closure component => rfl
                    | ordinaryMonocyclicPolicy initial closure policyResult =>
                        simp only [LocalizedRule3CyclicAuthorityRoute.mapSpatialPoints,
                          LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints,
                          LocalizedMonocyclicDoubleBondPolicyResult.mapSpatialPoints]
                        cases policyResult.policy <;> rfl
                    | ordinaryMonocyclicPolicyGap initial closure carrier doubleBondCount => rfl
                    | ordinaryNonmonocyclic initial closure => rfl
        | branched initial first second rest =>
            simp only [LocalizedRule3CumulatedAxisEntry.mapSpatialPoints]
            rw [localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_affine
              input target occurrence view rule3FrameOf transform mappedRule3FrameOf
                rule3FrameNatural determinantNonzero]
            cases resultEq : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                target occurrence view rule3FrameOf with
            | none => rfl
            | some result =>
                simp only [Option.map_some,
                  localizedRule3DescriptorBearingObservation_mapSpatialPoints,
                  physicalUnitId_mapSpatialPoints]
                rw [excludedNatural]
                split <;> rfl
        | terminalStart initial =>
            simp only [LocalizedRule3CumulatedAxisEntry.mapSpatialPoints]
            simp only [localizedRule3CumulatedTraversalFuel]
            rw [localizedRule3CumulatedEndpointCursorFrame?_mapSpatialPoints]
            cases axisEq : input.localizedRule3CumulatedEndpointCursorFrame?
                (localizedOccurrenceRerootEvaluationFuel carrierFuel) occurrence with
            | none => simp
            | some axis =>
                simp only [Option.map_some]
                have doubleBondCountNatural :
                    (axis.mapSpatialPoints transform.applyPoint).doubleBondCount =
                      axis.doubleBondCount := by
                  unfold LocalizedRule3CumulatedEndpointCursorFrame.doubleBondCount
                  simp [LocalizedRule3CumulatedEndpointCursorFrame.mapSpatialPoints]
                simp only [doubleBondCountNatural]
                by_cases ordinary : axis.doubleBondCount = 1
                · simp only [dif_pos ordinary]
                  rw [localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_affine
                    input target occurrence view rule3FrameOf transform mappedRule3FrameOf
                      rule3FrameNatural determinantNonzero]
                  cases resultEq : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                      target occurrence view rule3FrameOf with
                  | none => rfl
                  | some result =>
                      simp only [Option.map_some,
                        localizedRule3DescriptorBearingObservation_mapSpatialPoints,
                        physicalUnitId_mapSpatialPoints]
                      rw [excludedNatural]
                      split <;> rfl
                · simp only [dif_neg ordinary]
                  by_cases planar : Odd axis.doubleBondCount
                  · simp only [dif_pos planar]
                    rw [localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_affine
                      input target occurrence view rule3FrameOf transform mappedRule3FrameOf
                        rule3FrameNatural determinantNonzero]
                    cases resultEq :
                        input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
                          target occurrence view rule3FrameOf with
                    | none => rfl
                    | some result =>
                        simp only [Option.map_some,
                          localizedRule3OddCumuleneDescriptorBearingObservation_mapSpatialPoints,
                          physicalUnitId_mapSpatialPoints]
                        rw [excludedNatural]
                        split <;> rfl
                  · simp only [dif_neg planar]
                    rfl
  · have notMappedEdge :
        ¬ (input.mapSpatialPoints transform.applyPoint).LocalizedOccurrenceHasRule3DoubleBondEdge
          (occurrence.mapSpatialPoints transform.applyPoint) :=
      fun mappedEdge => edge (edgeNatural.mp mappedEdge)
    simp [edge, notMappedEdge]

private theorem descriptorBearingRule3BuilderAffineMutual
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    ∀ fuel : Nat,
      (∀ (excluded : List input.LocalizedRule3PhysicalUnitId)
          (cursor : input.LocalizedRerootCursor carrierFuel),
        buildLocalizedRerootDescriptorBearingRule3Key?
              (input.mapSpatialPoints transform.applyPoint)
              (target.mapSpatialPoints transform.applyPoint)
              (view.mapSpatialPoints transform.applyPoint) fuel
              (excluded.map fun unit => unit.mapSpatialPoints transform.applyPoint)
              (cursor.mapSpatialPoints transform.applyPoint) =
          (input.buildLocalizedRerootDescriptorBearingRule3Key?
            target view fuel excluded cursor).map
              (fun key => key.mapSpatialPoints transform.applyPoint)) ∧
      (∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
        (input.mapSpatialPoints transform.applyPoint).buildLocalizedDescriptorBearingRule3Frame?
            (target.mapSpatialPoints transform.applyPoint)
            (view.mapSpatialPoints transform.applyPoint) fuel
            (cursors.map fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
          (input.buildLocalizedDescriptorBearingRule3Frame?
            target view fuel cursors).map
              (fun frame => frame.mapSpatialPoints transform.applyPoint)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro excluded cursor
        unfold buildLocalizedRerootDescriptorBearingRule3Key?
        have nodeEq :
            (cursor.occurrence.mapSpatialPoints transform.applyPoint).1.node =
              cursor.occurrence.1.node := rfl
        rw [localizedRerootChildren?_mapSpatialPoints,
          show (cursor.mapSpatialPoints transform.applyPoint).occurrence =
              cursor.occurrence.mapSpatialPoints transform.applyPoint from rfl,
          localizedDescriptorBearingRule3StructuralNode?_mapSpatialPoints]
        cases childrenEq : input.localizedRerootChildren? cursor with
        | none => rfl
        | some children =>
            cases observationEq : input.localizedDescriptorBearingRule3StructuralNode?
                cursor.occurrence with
            | none => rfl
            | some observation =>
                by_cases terminal : children = []
                · simp [terminal, moleculeGraph_mapSpatialPoints,
                    nodeEq,
                    localizedRule3SpatialRootObservations_mapSpatialPoints,
                    localizedRule3SpatialRootPriorities_mapSpatialPoints,
                    LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
                · simp [terminal]
      · intro cursors
        rfl
  | succ fuel ih =>
      constructor
      · intro excluded cursor
        unfold buildLocalizedRerootDescriptorBearingRule3Key?
        have nodeEq :
            (cursor.occurrence.mapSpatialPoints transform.applyPoint).1.node =
              cursor.occurrence.1.node := rfl
        rw [localizedRerootChildren?_mapSpatialPoints]
        rw [show (cursor.mapSpatialPoints transform.applyPoint).occurrence =
          cursor.occurrence.mapSpatialPoints transform.applyPoint from rfl]
        rw [localizedDescriptorBearingRule3NodeWith?_affine
          input target cursor.occurrence view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
          transform
          (buildLocalizedDescriptorBearingRule3Frame?
              (input.mapSpatialPoints transform.applyPoint)
              (target.mapSpatialPoints transform.applyPoint)
              (view.mapSpatialPoints transform.applyPoint) fuel)
          ih.2 excluded determinantNonzero]
        cases childrenEq : input.localizedRerootChildren? cursor with
        | none => rfl
        | some children =>
            cases observationEq : input.localizedDescriptorBearingRule3NodeWith?
                target cursor.occurrence view
                (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) excluded with
            | none => rfl
            | some observation =>
                by_cases terminal : children = []
                · simp [terminal, moleculeGraph_mapSpatialPoints,
                    nodeEq,
                    localizedRule3SpatialRootObservations_mapSpatialPoints,
                    localizedRule3SpatialRootPriorities_mapSpatialPoints,
                    LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
                · simp [terminal]
                  have mapMNatural :
                      children.mapM
                          (buildLocalizedRerootDescriptorBearingRule3Key?
                              (input.mapSpatialPoints transform.applyPoint)
                                (target.mapSpatialPoints transform.applyPoint)
                                (view.mapSpatialPoints transform.applyPoint) fuel
                                (excluded.map fun unit =>
                                  unit.mapSpatialPoints transform.applyPoint) ∘
                            fun child => child.mapSpatialPoints transform.applyPoint) =
                        (children.mapM
                          (input.buildLocalizedRerootDescriptorBearingRule3Key?
                            target view fuel excluded)).map
                          (fun keys => keys.map fun key =>
                            key.mapSpatialPoints transform.applyPoint) :=
                    listMapM_map_of_natural
                      (fun child => child.mapSpatialPoints transform.applyPoint)
                      (fun key => key.mapSpatialPoints transform.applyPoint)
                      (input.buildLocalizedRerootDescriptorBearingRule3Key?
                        target view fuel excluded)
                      (buildLocalizedRerootDescriptorBearingRule3Key?
                          (input.mapSpatialPoints transform.applyPoint)
                          (target.mapSpatialPoints transform.applyPoint)
                          (view.mapSpatialPoints transform.applyPoint) fuel
                          (excluded.map fun unit =>
                            unit.mapSpatialPoints transform.applyPoint))
                      (ih.1 excluded) children
                  rw [mapMNatural]
                  cases childKeysEq : children.mapM
                      (input.buildLocalizedRerootDescriptorBearingRule3Key?
                        target view fuel excluded) with
                  | none => rfl
                  | some childKeys =>
                      simp only [Option.map_some, Option.bind_some]
                      rw [sortLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints,
                        mergeLocalizedRerootRule3ObservationChildren_mapSpatialPoints,
                        mergeLocalizedRerootRule3PriorityChildren_mapSpatialPoints]
                      simp only [LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints,
                        List.map_append, List.map_map]
                      rfl
      · intro cursors
        unfold buildLocalizedDescriptorBearingRule3Frame?
        rw [List.mapM_map]
        have rawNatural :
            cursors.mapM
                (buildLocalizedRerootDescriptorBearingRule3Key?
                    (input.mapSpatialPoints transform.applyPoint)
                      (target.mapSpatialPoints transform.applyPoint)
                      (view.mapSpatialPoints transform.applyPoint) fuel [] ∘
                  fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
              (cursors.mapM
                (input.buildLocalizedRerootDescriptorBearingRule3Key?
                  target view fuel [])).map
                (fun keys => keys.map fun key => key.mapSpatialPoints transform.applyPoint) :=
          listMapM_map_of_natural
            (fun cursor => cursor.mapSpatialPoints transform.applyPoint)
            (fun key => key.mapSpatialPoints transform.applyPoint)
            (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel [])
            (buildLocalizedRerootDescriptorBearingRule3Key?
                (input.mapSpatialPoints transform.applyPoint)
                (target.mapSpatialPoints transform.applyPoint)
                (view.mapSpatialPoints transform.applyPoint) fuel [])
            (by
              intro cursor
              simpa using ih.1 [] cursor)
            cursors
        rw [rawNatural]
        cases rawKeysEq : cursors.mapM
            (input.buildLocalizedRerootDescriptorBearingRule3Key? target view fuel []) with
        | none => rfl
        | some rawKeys =>
            simp
            cases topologyEq : input.localizedRule3CoupledTopologyResolution? rawKeys with
            | none => rfl
            | some topology =>
                simp only [Option.map_some, Option.bind_some,
                  localizedRule3CoupledTopologyResolution_isCoupled_mapSpatialPoints,
                  localizedRule3CoupledExcludedPhysicalUnits_mapSpatialPoints]
                let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
                have keysNatural :
                    cursors.mapM
                        (buildLocalizedRerootDescriptorBearingRule3Key?
                            (input.mapSpatialPoints transform.applyPoint)
                              (target.mapSpatialPoints transform.applyPoint)
                              (view.mapSpatialPoints transform.applyPoint) fuel
                              (excluded.map fun unit =>
                                unit.mapSpatialPoints transform.applyPoint) ∘
                          fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
                      (cursors.mapM
                        (input.buildLocalizedRerootDescriptorBearingRule3Key?
                          target view fuel excluded)).map
                        (fun keys => keys.map fun key =>
                          key.mapSpatialPoints transform.applyPoint) :=
                  listMapM_map_of_natural
                    (fun cursor => cursor.mapSpatialPoints transform.applyPoint)
                    (fun key => key.mapSpatialPoints transform.applyPoint)
                    (input.buildLocalizedRerootDescriptorBearingRule3Key?
                      target view fuel excluded)
                    (buildLocalizedRerootDescriptorBearingRule3Key?
                        (input.mapSpatialPoints transform.applyPoint)
                        (target.mapSpatialPoints transform.applyPoint)
                        (view.mapSpatialPoints transform.applyPoint) fuel
                        (excluded.map fun unit =>
                          unit.mapSpatialPoints transform.applyPoint))
                    (ih.1 excluded) cursors
                rw [keysNatural]
                cases keysEq : cursors.mapM
                    (input.buildLocalizedRerootDescriptorBearingRule3Key?
                      target view fuel excluded) <;>
                  simp [LocalizedRule3CanonicalKeyFrame.mapSpatialPoints]

theorem buildLocalizedRerootDescriptorBearingRule3Key?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    buildLocalizedRerootDescriptorBearingRule3Key?
          (input.mapSpatialPoints transform.applyPoint)
          (target.mapSpatialPoints transform.applyPoint)
          (view.mapSpatialPoints transform.applyPoint) fuel
          (excluded.map fun unit => unit.mapSpatialPoints transform.applyPoint)
          (cursor.mapSpatialPoints transform.applyPoint) =
      (input.buildLocalizedRerootDescriptorBearingRule3Key?
        target view fuel excluded cursor).map
          (fun key => key.mapSpatialPoints transform.applyPoint) :=
  (descriptorBearingRule3BuilderAffineMutual input target view transform
    determinantNonzero fuel).1 excluded cursor

theorem buildLocalizedDescriptorBearingRule3Frame?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).buildLocalizedDescriptorBearingRule3Frame?
        (target.mapSpatialPoints transform.applyPoint)
        (view.mapSpatialPoints transform.applyPoint) fuel
        (cursors.map fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
      (input.buildLocalizedDescriptorBearingRule3Frame?
        target view fuel cursors).map
          (fun frame => frame.mapSpatialPoints transform.applyPoint) :=
  (descriptorBearingRule3BuilderAffineMutual input target view transform
    determinantNonzero fuel).2 cursors

theorem localizedDescriptorBearingRule3Node?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedDescriptorBearingRule3Node?
        (target.mapSpatialPoints transform.applyPoint)
        (occurrence.mapSpatialPoints transform.applyPoint)
        (view.mapSpatialPoints transform.applyPoint) fuel
        (excluded.map fun unit => unit.mapSpatialPoints transform.applyPoint) =
      (input.localizedDescriptorBearingRule3Node?
        target occurrence view fuel excluded).map
          (Option.map fun result => result.mapSpatialPoints transform.applyPoint) := by
  cases fuel with
  | zero =>
      exact localizedDescriptorBearingRule3StructuralNode?_mapSpatialPoints
        input occurrence transform.applyPoint
  | succ fuel =>
      unfold localizedDescriptorBearingRule3Node?
      exact localizedDescriptorBearingRule3NodeWith?_affine
        input target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
        transform
        (buildLocalizedDescriptorBearingRule3Frame?
            (input.mapSpatialPoints transform.applyPoint)
            (target.mapSpatialPoints transform.applyPoint)
            (view.mapSpatialPoints transform.applyPoint) fuel)
        (fun cursors => buildLocalizedDescriptorBearingRule3Frame?_affine
          input target view fuel cursors transform determinantNonzero)
        excluded determinantNonzero

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
