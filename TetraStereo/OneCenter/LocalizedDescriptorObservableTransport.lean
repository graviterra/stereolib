import TetraStereo.OneCenter.LocalizedOccurrenceRule3Through5Descriptor
import TetraStereo.OneCenter.LocalizedExtendedFrameCompleteness
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Observable transport of the descriptor-facing Rule-3-through-5 key comparison

This module proves the local transport step needed by the derived-frame completeness programme: the
descriptor-facing comparison, the tracked stable order, and the resulting geometry/classification do
not depend on the *literal* data of a four-ligand Rule-3 key frame.  They depend only on

* the aligned `rule45Keys` list, which the Rules-4a/4b/4c/5 fallthrough comparator reads verbatim,
  and
* the Rule-3 numeric observable projection of `rule3Frame.keys`, i.e. the addressed Rules 1a/1b/2
  entries together with the Rule-3 priority projection.

The `rawKeys`, `coupled`, and `excluded` fields of `LocalizedRule3CanonicalKeyFrame` do not occur in
`compareLocalizedOccurrenceRule3Through5At` at all, and the `observations` payload of a recursive
Rule-3 spatial key is deliberately absent from `localizedRerootRule3SpatialKeyObservable` because
`compareLocalizedRerootRecursiveRule3SpatialKeys` never reads it.  Hence two independently compiled
frames may disagree on all of those and still compare identically.

Everything below is a consequence of the existing observable-comparison factorization
`compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable` and the existing total
tracked-sort law `sortFourLocalizedLigandsTracked`; no new well-formedness or "ready" predicate is
introduced.  This is a local transport core for later derived-frame completeness, not a standalone
whole-chemistry completeness proof: constructing the executable frame is a separate obligation.
-/

/-! ## Pointwise access to the shared numeric projections -/

/-- Equal Rule-3 observable lists of two four-element key lists induce equal observables at every
`Fin 4` position.  Only the comparison-visible projection is transported; the `observations`
payloads of the underlying keys are not inspected. -/
theorem localizedRerootRule3SpatialKeyObservable_get_eq_of_map_eq
    (input : CertifiedLocalizedCIPInput)
    (first second : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstLength : first.length = 4) (secondLength : second.length = 4)
    (observations : first.map (input.localizedRerootRule3SpatialKeyObservable) =
      second.map (input.localizedRerootRule3SpatialKeyObservable))
    (index : Fin 4) :
    input.localizedRerootRule3SpatialKeyObservable
        (first.get (Fin.cast firstLength.symm index)) =
      input.localizedRerootRule3SpatialKeyObservable
        (second.get (Fin.cast secondLength.symm index)) := by
  have pointwise := congrArg (fun keys => keys[index.1]?) observations
  simp only [List.getElem?_map] at pointwise
  rw [List.getElem?_eq_getElem (by omega : index.1 < first.length),
    List.getElem?_eq_getElem (by omega : index.1 < second.length)] at pointwise
  simpa [List.get_eq_getElem] using pointwise

/-- Equal aligned Rule-4/5 key lists give equal Rule-4/5 keys at every `Fin 4` position. -/
theorem rule45Keys_get_eq_of_eq
    (input : CertifiedLocalizedCIPInput)
    (first second : List input.LocalizedRerootCompoundRule45Key)
    (keysEq : first = second)
    (firstLength : first.length = 4) (secondLength : second.length = 4)
    (index : Fin 4) :
    first.get (Fin.cast firstLength.symm index) =
      second.get (Fin.cast secondLength.symm index) := by
  have pointwise := congrArg (fun keys => keys[index.1]?) keysEq
  dsimp only at pointwise
  rw [List.getElem?_eq_getElem (by omega : index.1 < first.length),
    List.getElem?_eq_getElem (by omega : index.1 < second.length)] at pointwise
  simp only [Option.some.injEq] at pointwise
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact pointwise

/-- The aligned Rule-4/5 component of `keyAt` transports across equal `rule45Keys` lists. -/
theorem keyAt_rule45_eq_of_rule45Keys_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (keysEq : first.rule45Keys = second.rule45Keys)
    (index : Fin 4) :
    (first.keyAt index).rule45 = (second.keyAt index).rule45 := by
  have firstLength : first.rule45Keys.length = 4 := first.rule45Length
  have secondLength : second.rule45Keys.length = 4 := second.rule45Length
  have pointwise := input.rule45Keys_get_eq_of_eq
    first.rule45Keys second.rule45Keys keysEq firstLength secondLength index
  simpa [LocalizedOccurrenceRule3Through5KeyFrame.keyAt] using pointwise

/-! ## The actual `Fin 4` comparison records are identical -/

/-- Two four-ligand key frames that agree on the aligned Rule-4/5 key list and on the comparison
visible Rule-3 observable projection produce exactly the same comparison record at every pair of
ligand positions.  The record includes the ordering, the decisive-rule field, and the
pseudoasymmetric flag, so both the Rule-3 branch and the Rules-4/5 fallthrough branch agree
including their pseudoasymmetric counters.  Literal `rawKeys`, `observations`, and `excluded` data
are never required to match. -/
theorem compareLocalizedOccurrenceRule3Through5At_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable))
    (left right : Fin 4) :
    input.compareLocalizedOccurrenceRule3Through5At first left right =
      input.compareLocalizedOccurrenceRule3Through5At second left right := by
  have observableLeft :=
    input.localizedRerootRule3SpatialKeyObservable_get_eq_of_map_eq
      first.rule3Frame.keys second.rule3Frame.keys
      first.rule3Length second.rule3Length rule3Observable_eq left
  have observableRight :=
    input.localizedRerootRule3SpatialKeyObservable_get_eq_of_map_eq
      first.rule3Frame.keys second.rule3Frame.keys
      first.rule3Length second.rule3Length rule3Observable_eq right
  have rule45Left :=
    input.keyAt_rule45_eq_of_rule45Keys_eq first second rule45Keys_eq left
  have rule45Right :=
    input.keyAt_rule45_eq_of_rule45Keys_eq first second rule45Keys_eq right
  have rule3Compare :
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
          (first.keyAt left).rule3 (first.keyAt right).rule3 =
        input.compareLocalizedRerootRecursiveRule3SpatialKeys
          (second.keyAt left).rule3 (second.keyAt right).rule3 := by
    rw [input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable,
      input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable]
    rw [show input.localizedRerootRule3SpatialKeyObservable (first.keyAt left).rule3 =
          input.localizedRerootRule3SpatialKeyObservable (second.keyAt left).rule3
        from observableLeft,
      show input.localizedRerootRule3SpatialKeyObservable (first.keyAt right).rule3 =
          input.localizedRerootRule3SpatialKeyObservable (second.keyAt right).rule3
        from observableRight]
  unfold compareLocalizedOccurrenceRule3Through5At
  dsimp only
  rw [rule3Compare]
  cases decisive : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (second.keyAt left).rule3 (second.keyAt right).rule3 <;>
    simp [rule45Left, rule45Right]

/-- The ordering component of the comparison record is transported. -/
theorem compareLocalizedOccurrenceRule3Through5At_ordering_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable))
    (left right : Fin 4) :
    (input.compareLocalizedOccurrenceRule3Through5At first left right).ordering =
      (input.compareLocalizedOccurrenceRule3Through5At second left right).ordering := by
  rw [input.compareLocalizedOccurrenceRule3Through5At_eq_of_keyObservables
    first second rule45Keys_eq rule3Observable_eq left right]

/-- The decisive-rule component of the comparison record is transported. -/
theorem compareLocalizedOccurrenceRule3Through5At_decisiveRule?_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable))
    (left right : Fin 4) :
    (input.compareLocalizedOccurrenceRule3Through5At first left right).decisiveRule? =
      (input.compareLocalizedOccurrenceRule3Through5At second left right).decisiveRule? := by
  rw [input.compareLocalizedOccurrenceRule3Through5At_eq_of_keyObservables
    first second rule45Keys_eq rule3Observable_eq left right]

/-- The pseudoasymmetric component of the comparison record is transported, including the
Rules-4/5 fallthrough `±2` signal. -/
theorem compareLocalizedOccurrenceRule3Through5At_pseudo_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable))
    (left right : Fin 4) :
    (input.compareLocalizedOccurrenceRule3Through5At first left right).pseudo =
      (input.compareLocalizedOccurrenceRule3Through5At second left right).pseudo := by
  rw [input.compareLocalizedOccurrenceRule3Through5At_eq_of_keyObservables
    first second rule45Keys_eq rule3Observable_eq left right]

/-! ## The executable tracked order is identical -/

/-- Pointwise-equal comparison records give equal all-pairs coherence checks. -/
theorem localizedOccurrenceRule3Through5OrderCoherent_eq_of_comparisons
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (comparisons : ∀ left right : Fin 4,
      input.compareLocalizedOccurrenceRule3Through5At first left right =
        input.compareLocalizedOccurrenceRule3Through5At second left right) :
    ∀ order, input.localizedOccurrenceRule3Through5OrderCoherent first order =
      input.localizedOccurrenceRule3Through5OrderCoherent second order
  | [] => rfl
  | head :: tail => by
      have tailEq :=
        input.localizedOccurrenceRule3Through5OrderCoherent_eq_of_comparisons
          first second comparisons tail
      have headEq :
          (fun position =>
              input.localizedOccurrenceRule3Through5OrderPairStrict first head position) =
            (fun position =>
              input.localizedOccurrenceRule3Through5OrderPairStrict second head position) := by
        funext position
        simp only [localizedOccurrenceRule3Through5OrderPairStrict]
        rw [comparisons head position]
      change (tail.all (fun position =>
            input.localizedOccurrenceRule3Through5OrderPairStrict first head position) &&
          input.localizedOccurrenceRule3Through5OrderCoherent first tail) =
        (tail.all (fun position =>
            input.localizedOccurrenceRule3Through5OrderPairStrict second head position) &&
          input.localizedOccurrenceRule3Through5OrderCoherent second tail)
      rw [tailEq, headEq]

/-- The executable tracked stable order is identical for two key frames that agree on the aligned
Rule-4/5 key list and on the Rule-3 observable projection.  In particular the resulting
`highestFirst` ligand order and the accumulated `pseudoComparisons` counter are identical. -/
theorem localizedNoDoubleTrackedOrderExec?_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable)) :
    input.localizedNoDoubleTrackedOrderExec? first =
      input.localizedNoDoubleTrackedOrderExec? second := by
  have comparisons : ∀ left right : Fin 4,
      input.compareLocalizedOccurrenceRule3Through5At first left right =
        input.compareLocalizedOccurrenceRule3Through5At second left right :=
    fun left right =>
      input.compareLocalizedOccurrenceRule3Through5At_eq_of_keyObservables
        first second rule45Keys_eq rule3Observable_eq left right
  have compareFunctions : input.compareLocalizedOccurrenceRule3Through5At? first =
      input.compareLocalizedOccurrenceRule3Through5At? second := by
    funext left right
    simp only [compareLocalizedOccurrenceRule3Through5At?]
    rw [comparisons left right]
  unfold localizedNoDoubleTrackedOrderExec?
  rw [compareFunctions]
  cases sorted : sortFourLocalizedLigandsTracked
      (input.compareLocalizedOccurrenceRule3Through5At? second) with
  | none => rfl
  | some tracked =>
      change (if input.localizedOccurrenceRule3Through5OrderCoherent first
            tracked.highestFirst then some tracked else none) =
        (if input.localizedOccurrenceRule3Through5OrderCoherent second
            tracked.highestFirst then some tracked else none)
      rw [input.localizedOccurrenceRule3Through5OrderCoherent_eq_of_comparisons
        first second comparisons tracked.highestFirst]

/-- Component form of the tracked-order transport: the descriptor-facing `highestFirst` list and
the `pseudoComparisons` counter agree whenever the executable order succeeds on both frames. -/
theorem localizedNoDoubleTrackedOrderExec?_components_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable))
    {firstOrder secondOrder : TrackedLocalizedLigandOrder}
    (firstComputed : input.localizedNoDoubleTrackedOrderExec? first = some firstOrder)
    (secondComputed : input.localizedNoDoubleTrackedOrderExec? second = some secondOrder) :
    firstOrder.highestFirst = secondOrder.highestFirst ∧
      firstOrder.pseudoComparisons = secondOrder.pseudoComparisons := by
  have equalOrders := input.localizedNoDoubleTrackedOrderExec?_eq_of_keyObservables
    first second rule45Keys_eq rule3Observable_eq
  rw [firstComputed, secondComputed] at equalOrders
  simp only [Option.some.injEq] at equalOrders
  cases equalOrders
  exact ⟨rfl, rfl⟩

/-! ## Fixed-base geometry and the priority-order classification -/

/-- The exact priority-ordered spatial-point computation of the executable evidence path is
identical over one common base frame.  This is the `highestFirst.mapM` line of
`localizedNoDoubleSpatialEvidenceExec?`, stated without any additional structure. -/
theorem localizedNoDoubleSpatialPoints_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable)) :
    (do
      let tracked ← input.localizedNoDoubleTrackedOrderExec? first
      tracked.highestFirst.mapM fun index =>
        input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) =
    (do
      let tracked ← input.localizedNoDoubleTrackedOrderExec? second
      tracked.highestFirst.mapM fun index =>
        input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) := by
  rw [input.localizedNoDoubleTrackedOrderExec?_eq_of_keyObservables
    first second rule45Keys_eq rule3Observable_eq]

/-- A key frame's tracked order together with its base-relative priority-ordered spatial points. -/
noncomputable def localizedNoDoubleTrackedPointsAtBase?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option (TrackedLocalizedLigandOrder × List CartesianPoint3) := do
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some (tracked, points)

/-- Over one common four-ligand base frame, the tracked order and the priority-ordered spatial
points are identical for key frames that agree on the Rule-3 observable projection and the aligned
Rule-4/5 key list.  Only the same base's cursors are read, so nothing about the geometry itself is
assumed. -/
theorem localizedNoDoubleTrackedPointsAtBase?_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable)) :
    input.localizedNoDoubleTrackedPointsAtBase? base first =
      input.localizedNoDoubleTrackedPointsAtBase? base second := by
  unfold localizedNoDoubleTrackedPointsAtBase?
  rw [input.localizedNoDoubleTrackedOrderExec?_eq_of_keyObservables
    first second rule45Keys_eq rule3Observable_eq]

/-- The priority-ordered geometry classification computed over one common base frame is identical
for key frames that agree on the comparator-visible projections.  The raw `R/S` reading comes from
the shared point list and the pseudoasymmetric case from the shared `pseudoComparisons` counter, so
no comparator, order, or descriptor equality is assumed. -/
theorem localizedNoDoubleDescriptorAtBase?_eq_of_keyObservables
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (first second : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (rule45Keys_eq : first.rule45Keys = second.rule45Keys)
    (rule3Observable_eq :
      first.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
        second.rule3Frame.keys.map (input.localizedRerootRule3SpatialKeyObservable)) :
    (do
      let state ← input.localizedNoDoubleTrackedPointsAtBase? base first
      let raw ← descriptorOfPriorityOrderedPoints? state.2
      some (classifyTetrahedralRSPseudo raw state.1.pseudoComparisons)) =
    (do
      let state ← input.localizedNoDoubleTrackedPointsAtBase? base second
      let raw ← descriptorOfPriorityOrderedPoints? state.2
      some (classifyTetrahedralRSPseudo raw state.1.pseudoComparisons)) := by
  rw [input.localizedNoDoubleTrackedPointsAtBase?_eq_of_keyObservables
    base first second rule45Keys_eq rule3Observable_eq]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
