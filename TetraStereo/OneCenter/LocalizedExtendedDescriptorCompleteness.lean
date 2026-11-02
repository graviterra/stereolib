import TetraStereo.OneCenter.LocalizedExtendedShortCircuitDescriptor
import TetraStereo.OneCenter.LocalizedAutomaticComparisonRank
import TetraStereo.OneCenter.LocalizedTetrahedralPermutationExistence

set_option autoImplicit false
namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Descriptor-level completeness above extended key-frame construction

`LocalizedExtendedShortCircuitDescriptor` proves soundness of

`localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?`:
every emitted label has the independent declarative meaning
`DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor`.
The converse direction -- successful emission under independently meaningful data -- was absent.

This module closes the descriptor level itself.  Given

* a tetrahedral center with its declarative meaning,
* an independently meaningful four-ligand base frame,
* a compiled cumulative Rules-1a--5 key frame `keys` (see the residual premise below),
* a strict total order on the four compiled ligand keys (no tied comparison),
* four coordinate readings with declarative meaning and nonzero oriented volume,

the executable descriptor is proved to return `some descriptor`, and that descriptor is
additionally proved to carry the independent declarative meaning via the existing soundness
theorem.  The tracked order, its permutation of `List.finRange 4`, the rational descriptor of
the ordered points and the point list itself are all constructed inside the proof:

* `trackedOrder_total_of_separated` turns the finite twelve-pair non-tie condition into a
  successful tracked sort history;
* `rationalTetrahedralDescriptor_exists_of_permutation` turns nonzero volume plus the
  permutation into a rational `R`/`S` reading;
* the point list is obtained from the declarative coordinate readings through
  `localizedRerootCursorSpatialPoint?_eq_some_iff` and a `mapM` induction.

## Residual premise

`keyFrameCompiled` states that the cumulative Rules-1a--5 key-frame compiler

`buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?`

returns `some keys` for this base and dependency view.  This is the *frame compilation* step,
strictly below the descriptor: it is not the desired descriptor execution, and it does not
supply a tracked order, a point list, a parity reading, or a label.  It is kept as an explicit
premise because the extended node evaluator legitimately refuses (terminal ties, degenerate
geometry, unresolvable coupled topology, exhausted callbacks), so frame compilation is not
derivable from the declarative key meaning alone.  Proving this premise from structural,
node-level success conditions is the lower-level completeness obligation and is *not* claimed
here.

No hypothesis below mentions `localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?`,
`localizedNoDoubleTrackedOrderExec?`, `descriptorOfPriorityOrderedPoints?` or any other part of
the descriptor computation.
-/

/-- **Descriptor-level completeness above key-frame construction.**

Under independent center, base, order and geometry data, and with the lower-level cumulative
key-frame *compilation* isolated as a premise, the extended occurrence descriptor succeeds. -/
theorem extendedDescriptor_total_of_keyFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (centerMeaning : input.RealTetrahedralCenterNode target.1.node center)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (keyFrameCompiled : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      target view base = some keys)
    (strictOrder : input.FullComparisonSeparated keys)
    (point : Fin 4 → CartesianPoint3)
    (pointsMeaning : ∀ index, input.DeclarativeLocalizedRerootCursorSpatialPoint
      (base.cursorAt index) (point index))
    (nonzero : CartesianPoint3.orientedVolume
      (point 0) (point 1) (point 2) (point 3) ≠ 0) :
    ∃ descriptor,
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        target view = some descriptor := by
  -- A strict total order on four keys yields the production tracked order and its permutation.
  obtain ⟨tracked, trackedComputed, permutation, _⟩ :=
    input.trackedOrder_total_of_separated keys strictOrder
  -- Nonzero volume turns the permuted point list into a rational tetrahedral reading.
  obtain ⟨raw, geometry⟩ :=
    rationalTetrahedralDescriptor_exists_of_permutation point tracked.highestFirst
      permutation nonzero
  -- Every queried cursor has exactly the declaratively specified coordinate.
  have pointComputed : ∀ index, input.localizedRerootCursorSpatialPoint?
      (base.cursorAt index) = some (point index) := fun index =>
    (input.localizedRerootCursorSpatialPoint?_eq_some_iff (base.cursorAt index)
      (point index)).mpr (pointsMeaning index)
  have pointsComputed : tracked.highestFirst.mapM (fun index =>
      input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) =
        some (tracked.highestFirst.map point) := by
    induction tracked.highestFirst with
    | nil => rfl
    | cons index rest ih =>
        simp only [List.mapM_cons, pointComputed index, ih, List.map_cons]
        rfl
  have centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mpr centerMeaning
  have baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base := by
    rw [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target base).mpr baseMeaning
  let evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel :=
    { center := center, base := base, keys := keys, tracked := tracked,
      points := tracked.highestFirst.map point }
  have evidenceComputed :
      input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
        target view = some evidence := by
    simp [localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?,
      centerComputed, baseComputed, keyFrameCompiled, trackedComputed, pointsComputed,
      evidence]
  have geometryComputed :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff _ raw).mpr geometry
  refine ⟨classifyTetrahedralRSPseudo raw tracked.pseudoComparisons, ?_⟩
  simp [localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?,
    evidenceComputed, evidence, geometryComputed]

/-- **Exact refusal boundary above key-frame construction.**

If some pair of the four compiled ligand keys is tied, the extended descriptor refuses: the
tracked order fails, so the spatial evidence stage is `none` and no label is emitted.  Geometry
is not needed for this direction.  Together with `extendedDescriptor_total_of_keyFrame` this
identifies `FullComparisonSeparated` as the exact order-side success condition at the descriptor
level. -/
theorem extendedDescriptor_none_of_not_strictOrder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (keyFrameCompiled : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      target view base = some keys)
    (notStrict : ¬ input.FullComparisonSeparated keys) :
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view = none := by
  -- A tied pair makes the tracked-order stage refuse.
  have trackedComputed : input.localizedNoDoubleTrackedOrderExec? keys = none :=
    input.trackedOrder_none_of_not_separated keys notStrict
  have baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base := by
    rw [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target base).mpr baseMeaning
  -- The evidence stage therefore has no result at all, independently of the center reading.
  have evidenceNone :
      input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
        target view = none := by
    unfold localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
    cases input.localizedOccurrenceDescriptorCenter? target with
    | none => simp
    | some found =>
        simp [baseComputed, keyFrameCompiled, trackedComputed]
  unfold localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
  simp [evidenceNone]

/-- Independent sufficient data for the extended descriptor, with the cumulative key-frame
compilation as the only executable premise.  `strictOrder` is the finite non-tie condition on
the four compiled ligand keys; `pointsMeaning` and `nonzero` are molecule-backed geometry. -/
structure LocalizedExtendedDescriptorReadiness
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) where
  center : input.TetrahedralCenter
  centerMeaning : input.RealTetrahedralCenterNode target.1.node center
  base : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base
  keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel
  /-- Residual lower-level premise: the cumulative key frame compiles.  This is strictly below
  the descriptor and constructs no order, coordinate, parity reading or label. -/
  keyFrameCompiled : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
    target view base = some keys
  /-- Valid strict order: no two of the four compiled ligand keys compare equal. -/
  strictOrder : input.FullComparisonSeparated keys
  point : Fin 4 → CartesianPoint3
  pointsMeaning : ∀ index, input.DeclarativeLocalizedRerootCursorSpatialPoint
    (base.cursorAt index) (point index)
  nonzero : CartesianPoint3.orientedVolume
    (point 0) (point 1) (point 2) (point 3) ≠ 0

/-- **Universal descriptor-level total correctness above key-frame construction.**

For every carrier, target and dependency view, independent center/base/order/geometry data force
the extended descriptor to emit a label, and that label carries the independent declarative
descriptor meaning of `LocalizedExtendedShortCircuitDescriptor`. -/
theorem extendedDescriptor_total
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (ready : input.LocalizedExtendedDescriptorReadiness target view) :
    ∃ descriptor,
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        target view = some descriptor ∧
      input.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
        target view descriptor := by
  obtain ⟨descriptor, computed⟩ := input.extendedDescriptor_total_of_keyFrame
    target view ready.center ready.centerMeaning ready.base ready.baseMeaning
    ready.keys ready.keyFrameCompiled ready.strictOrder ready.point ready.pointsMeaning
    ready.nonzero
  exact ⟨descriptor, computed,
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_sound
      target view descriptor computed⟩

/-- The extended descriptor is a total successful computation on the readiness domain. -/
theorem extendedDescriptor_isSome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (ready : input.LocalizedExtendedDescriptorReadiness target view) :
    (input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view).isSome = true := by
  obtain ⟨descriptor, computed, _⟩ := input.extendedDescriptor_total target view ready
  simp [computed]

/-- **Exact descriptor-level success condition above key-frame construction.**

With the cumulative key frame compiled, the extended descriptor emits a label if and only if the
four compiled keys are strictly ordered.  This is an iff of the actual executable result and the
finite non-tie condition; it is not a restatement of descriptor execution. -/
theorem extendedDescriptor_isSome_iff_strictOrder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (centerMeaning : input.RealTetrahedralCenterNode target.1.node center)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (keyFrameCompiled : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      target view base = some keys)
    (point : Fin 4 → CartesianPoint3)
    (pointsMeaning : ∀ index, input.DeclarativeLocalizedRerootCursorSpatialPoint
      (base.cursorAt index) (point index))
    (nonzero : CartesianPoint3.orientedVolume
      (point 0) (point 1) (point 2) (point 3) ≠ 0) :
    (input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view).isSome = true ↔
      input.FullComparisonSeparated keys := by
  constructor
  · intro emitted
    by_contra notStrict
    have refused := input.extendedDescriptor_none_of_not_strictOrder
      target view base baseMeaning keys keyFrameCompiled notStrict
    rw [refused] at emitted
    simp at emitted
  · intro strict
    obtain ⟨descriptor, computed⟩ := input.extendedDescriptor_total_of_keyFrame
      target view center centerMeaning base baseMeaning keys keyFrameCompiled strict
      point pointsMeaning nonzero
    simp [computed]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
