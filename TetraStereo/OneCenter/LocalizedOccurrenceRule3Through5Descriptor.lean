import TetraStereo.OneCenter.LocalizedRerootRule3PhysicalUnit
import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Occurrence-local descriptor through Rules 1a--5

This module inserts the physical-unit-aware recursive Rule-3 stage ahead of the existing compound
Rules-4a--5 stage.  All four ligands are compiled once into one center-wide frame.  A cumulative
key compares complete Rules 1a--2, then Rule 3, and only a tie reaches Rules 4a--5.  The resulting
pair comparator is a pullback of one lawful unary key order, so the tracked tetrahedral sort no
longer depends on opponent-specific Rule-3 cancellation.

The positive descriptor path is proved sound here.  Exact positive/refusal correspondence and
the replacement auxiliary fixed point are separate next obligations.
-/

namespace CertifiedLocalizedCIPInput

/-- One ligand's cumulative Rules-1a--5 data. -/
structure LocalizedOccurrenceRule3Through5Key
    (input : CertifiedLocalizedCIPInput) where
  rule3 : input.LocalizedRerootRecursiveRule3SpatialKey
  rule45 : input.LocalizedRerootCompoundRule45Key

/-- Complete cumulative rule order for one occurrence ligand. -/
def compareLocalizedOccurrenceRule3Through5Keys
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedOccurrenceRule3Through5Key →
      input.LocalizedOccurrenceRule3Through5Key → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.rule3)
      input.compareLocalizedRerootRecursiveRule3SpatialKeys)
    (Ordering.byKey (fun key => key.rule45)
      input.compareLocalizedRerootCompoundRule45Keys)

/-- The cumulative Rules-1a--5 key comparator is oriented and transitive. -/
theorem compareLocalizedOccurrenceRule3Through5Keys_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedOccurrenceRule3Through5Keys := by
  letI : Std.TransCmp input.compareLocalizedRerootRecursiveRule3SpatialKeys :=
    input.compareLocalizedRerootRecursiveRule3SpatialKeys_transCmp
  letI : Std.TransCmp input.compareLocalizedRerootCompoundRule45Keys :=
    input.compareLocalizedRerootCompoundRule45Keys_transCmp
  unfold compareLocalizedOccurrenceRule3Through5Keys
  infer_instance

/-- One common center-wide Rule-3 frame and position-aligned Rule-4/5 keys. -/
structure LocalizedOccurrenceRule3Through5KeyFrame
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  rule3Frame : input.LocalizedRule3CanonicalKeyFrame
  rule3Length : rule3Frame.keys.length = 4
  rule45Keys : List input.LocalizedRerootCompoundRule45Key
  rule45Length : rule45Keys.length = 4

/-- Compile all four ligand keys once under one physical-unit policy and one dependency view. -/
noncomputable def buildLocalizedOccurrenceRule3Through5KeyFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let rule3Frame ← input.buildLocalizedRule3CanonicalKeyFrame? fuel frame.cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← frame.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45Key? target view fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame := rule3Frame
          rule3Length := rule3Length
          rule45Keys := rule45Keys
          rule45Length := rule45Length }
    else none
  else none

private theorem mapM_buildLocalizedRerootCompoundRule45Key?_sound_for_rule3Through5
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) :
    ∀ cursors keys,
      (cursors : List (input.LocalizedRerootCursor carrierFuel)).mapM
          (input.buildLocalizedRerootCompoundRule45Key? target view fuel) =
        some (keys : List input.LocalizedRerootCompoundRule45Key) →
      List.Forall₂
        (input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel)
        cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact List.Forall₂.nil
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootCompoundRule45Key?
          target view fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootCompoundRule45Key? target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact List.Forall₂.cons
                (input.buildLocalizedRerootCompoundRule45Key?_sound
                  target view fuel cursor head headComputed)
                (input.mapM_buildLocalizedRerootCompoundRule45Key?_sound_for_rule3Through5
                  target view fuel cursors tail tailComputed)

/-- Independent meaning of both aligned compilation passes. -/
def DeclarativeLocalizedOccurrenceRule3Through5KeyFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3CanonicalKeyFrame
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      base.cursors frame.rule3Frame ∧
    frame.rule3Frame.keys.length = 4 ∧
    List.Forall₂
      (input.DeclarativeLocalizedRerootCompoundRule45Key target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      base.cursors frame.rule45Keys ∧
    frame.rule45Keys.length = 4

/-- Successful four-ligand compilation accounts for both exact aligned key families. -/
theorem buildLocalizedOccurrenceRule3Through5KeyFrame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : input.buildLocalizedOccurrenceRule3Through5KeyFrame?
      target view base = some frame) :
    input.DeclarativeLocalizedOccurrenceRule3Through5KeyFrame
      target view base frame := by
  unfold buildLocalizedOccurrenceRule3Through5KeyFrame? at computed
  let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  cases rule3Computed : input.buildLocalizedRule3CanonicalKeyFrame?
      fuel base.cursors with
  | none => simp [rule3Computed, fuel] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : base.cursors.mapM
            (input.buildLocalizedRerootCompoundRule45Key? target view fuel) with
        | none =>
            simp [rule3Computed, rule45Computed, fuel] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length,
                fuel] at computed
              subst frame
              exact ⟨
                input.buildLocalizedRule3CanonicalKeyFrame?_sound
                  fuel base.cursors rule3Frame rule3Computed,
                rule3Length,
                input.mapM_buildLocalizedRerootCompoundRule45Key?_sound_for_rule3Through5
                  target view fuel base.cursors rule45Keys rule45Computed,
                rule45Length⟩
            · simp [rule3Computed, rule45Computed, rule45Length,
                fuel] at computed
      · simp [rule3Computed, rule3Length, fuel] at computed

/-- Aligned access to one cumulative ligand key. -/
def LocalizedOccurrenceRule3Through5KeyFrame.keyAt
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (index : Fin 4) : input.LocalizedOccurrenceRule3Through5Key :=
  { rule3 := frame.rule3Frame.keys.get (Fin.cast frame.rule3Length.symm index)
    rule45 := frame.rule45Keys.get (Fin.cast frame.rule45Length.symm index) }

/-- Descriptor-facing result: Rule-3 decisions are ordinary; only a Rules-4/5 tie path can be
pseudoasymmetric. -/
def compareLocalizedOccurrenceRule3Through5At
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : ConstitutionalDescriptorHierarchyComparison :=
  let leftKey := frame.keyAt left
  let rightKey := frame.keyAt right
  match input.compareLocalizedRerootRecursiveRule3SpatialKeys
      leftKey.rule3 rightKey.rule3 with
  | .lt => { ordering := .lt, pseudo := false }
  | .gt => { ordering := .gt, pseudo := false }
  | .eq => localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5
        leftKey.rule45 rightKey.rule45)

/-- The comparison record's order is exactly the cumulative unary key comparator. -/
theorem compareLocalizedOccurrenceRule3Through5At_ordering
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) :
    (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering =
      input.compareLocalizedOccurrenceRule3Through5Keys
        (frame.keyAt left) (frame.keyAt right) := by
  unfold compareLocalizedOccurrenceRule3Through5At
    compareLocalizedOccurrenceRule3Through5Keys
  generalize rule3Comparison :
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (frame.keyAt left).rule3 (frame.keyAt right).rule3 = outcome
  cases outcome <;>
    simp [compareLex, Ordering.byKey, rule3Comparison,
      localizedOccurrenceRule45ComparisonRecord,
      input.compareLocalizedRerootCompoundThroughRule5_ordering]

/-- A decisive Rule-3 comparison cannot fall through or create pseudoasymmetry. -/
theorem compareLocalizedOccurrenceRule3Through5At_of_rule3_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (strict : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.gt) :
    input.compareLocalizedOccurrenceRule3Through5At frame left right =
      { ordering := Ordering.gt, pseudo := false } := by
  simp [compareLocalizedOccurrenceRule3Through5At, strict]

/-- Only an exhaustive Rule-3 tie exposes the compound Rules-4a--5 result. -/
theorem compareLocalizedOccurrenceRule3Through5At_of_rule3_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (tied : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.eq) :
    input.compareLocalizedOccurrenceRule3Through5At frame left right =
      localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5
          (frame.keyAt left).rule45 (frame.keyAt right).rule45) := by
  simp [compareLocalizedOccurrenceRule3Through5At, tied]

/-- A pseudoasymmetric comparison record can arise only after Rule 3 ties. -/
theorem compareLocalizedOccurrenceRule3Through5At_pseudo_implies_rule3_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (pseudo : (input.compareLocalizedOccurrenceRule3Through5At
      frame left right).pseudo = true) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.eq := by
  unfold compareLocalizedOccurrenceRule3Through5At at pseudo
  generalize compared : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = outcome at pseudo
  cases outcome <;> simp_all

/-- The actual center-indexed ordering inherited from one fixed key frame is lawful. -/
theorem compareLocalizedOccurrenceRule3Through5At_transCmp
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    Std.TransCmp (fun left right =>
      (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering) := by
  letI : Std.TransCmp input.compareLocalizedOccurrenceRule3Through5Keys :=
    input.compareLocalizedOccurrenceRule3Through5Keys_transCmp
  have same : (fun left right =>
      (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering) =
      Ordering.byKey frame.keyAt input.compareLocalizedOccurrenceRule3Through5Keys := by
    funext left right
    exact input.compareLocalizedOccurrenceRule3Through5At_ordering frame left right
  rw [same]
  infer_instance

/-- A total optional wrapper for the generic tracked-sort interface. -/
def compareLocalizedOccurrenceRule3Through5At?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : Option ConstitutionalDescriptorHierarchyComparison :=
  some (input.compareLocalizedOccurrenceRule3Through5At frame left right)

/-- Proposed stable four-ligand order under the cumulative comparator. -/
noncomputable def localizedOccurrenceRule3Through5TrackedOrder?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder :=
  sortFourLocalizedLigandsTracked
    (input.compareLocalizedOccurrenceRule3Through5At? frame)

/-- Strict earlier/later check under the same fixed cumulative key frame. -/
def localizedOccurrenceRule3Through5OrderPairStrict
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : Bool :=
  (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering == Ordering.gt

def localizedOccurrenceRule3Through5OrderCoherent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    List (Fin 4) → Bool
  | [] => true
  | left :: rest =>
      rest.all (input.localizedOccurrenceRule3Through5OrderPairStrict frame left) &&
      input.localizedOccurrenceRule3Through5OrderCoherent frame rest

theorem localizedOccurrenceRule3Through5OrderCoherent_eq_true_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    ∀ order,
      input.localizedOccurrenceRule3Through5OrderCoherent frame order = true ↔
        order.Pairwise fun left right =>
          (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering =
            Ordering.gt
  | [] => by simp [localizedOccurrenceRule3Through5OrderCoherent]
  | left :: rest => by
      rw [localizedOccurrenceRule3Through5OrderCoherent, Bool.and_eq_true,
        List.all_eq_true, List.pairwise_cons,
        localizedOccurrenceRule3Through5OrderCoherent_eq_true_iff]
      simp [localizedOccurrenceRule3Through5OrderPairStrict]

/-- Stable tracked order after an all-pairs strictness check. -/
noncomputable def safeLocalizedOccurrenceRule3Through5TrackedOrder?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder := do
  let tracked ← input.localizedOccurrenceRule3Through5TrackedOrder? frame
  if input.localizedOccurrenceRule3Through5OrderCoherent
      frame tracked.highestFirst then some tracked else none

/-- Independent successful sort history and all-pairs strict order under one key frame. -/
def DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder) : Prop :=
  DeclarativeTrackedLocalizedLigandSort
      (input.compareLocalizedOccurrenceRule3Through5At? frame)
      (List.finRange 4) [] 0 tracked ∧
    tracked.highestFirst.Perm (List.finRange 4) ∧
    tracked.highestFirst.Pairwise fun left right =>
      (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering =
        Ordering.gt

theorem safeLocalizedOccurrenceRule3Through5TrackedOrder?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : input.safeLocalizedOccurrenceRule3Through5TrackedOrder? frame =
      some tracked) :
    input.DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder frame tracked := by
  unfold safeLocalizedOccurrenceRule3Through5TrackedOrder? at computed
  cases trackedComputed : input.localizedOccurrenceRule3Through5TrackedOrder? frame with
  | none => simp [trackedComputed] at computed
  | some observed =>
      cases coherent : input.localizedOccurrenceRule3Through5OrderCoherent
          frame observed.highestFirst with
      | false => simp [trackedComputed, coherent] at computed
      | true =>
          simp [trackedComputed, coherent] at computed
          subst tracked
          exact ⟨
            sortFourLocalizedLigandsTracked_sound
              (input.compareLocalizedOccurrenceRule3Through5At? frame)
              observed trackedComputed,
            sortFourLocalizedLigandsTracked_perm
              (input.compareLocalizedOccurrenceRule3Through5At? frame)
              observed trackedComputed,
            (input.localizedOccurrenceRule3Through5OrderCoherent_eq_true_iff
              frame observed.highestFirst).mp coherent⟩

/-- Geometry evidence ranked by the new cumulative Rules-1a--5 frame. -/
structure LocalizedOccurrenceRule3Through5SpatialEvidence
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  center : input.TetrahedralCenter
  base : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel
  tracked : TrackedLocalizedLigandOrder
  points : List CartesianPoint3

noncomputable def localizedOccurrenceRule3Through5SpatialEvidence?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← input.localizedOccurrenceFourLigandFrame? target
  let keys ← input.buildLocalizedOccurrenceRule3Through5KeyFrame? target view base
  let tracked ← input.safeLocalizedOccurrenceRule3Through5TrackedOrder? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center := center, base := base, keys := keys, tracked := tracked, points := points }

private theorem mapM_localizedRerootCursorSpatialPoint?_sound_for_rule3Through5
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points,
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
        (base.cursorAt index)) = some points →
      List.Forall₂
        (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
          (base.cursorAt index) point) order points
  | [], points, computed => by
      simp at computed
      subst points
      exact List.Forall₂.nil
  | index :: order, points, computed => by
      rw [List.mapM_cons] at computed
      cases pointComputed : input.localizedRerootCursorSpatialPoint?
          (base.cursorAt index) with
      | none => simp [pointComputed] at computed
      | some point =>
          cases tailComputed : order.mapM fun next =>
              input.localizedRerootCursorSpatialPoint? (base.cursorAt next) with
          | none => simp [pointComputed, tailComputed] at computed
          | some tail =>
              simp [pointComputed, tailComputed] at computed
              subst points
              exact List.Forall₂.cons
                ((input.localizedRerootCursorSpatialPoint?_eq_some_iff
                  (base.cursorAt index) point).mp pointComputed)
                (input.mapM_localizedRerootCursorSpatialPoint?_sound_for_rule3Through5
                  base order tail tailComputed)

def DeclarativeLocalizedOccurrenceRule3Through5SpatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) : Prop :=
  input.RealTetrahedralCenterNode target.1.node evidence.center ∧
    input.DeclarativeLocalizedOccurrenceFourLigandFrame target evidence.base ∧
    input.DeclarativeLocalizedOccurrenceRule3Through5KeyFrame
      target view evidence.base evidence.keys ∧
    input.DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder
      evidence.keys evidence.tracked ∧
    List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (evidence.base.cursorAt index) point)
      evidence.tracked.highestFirst evidence.points

theorem localizedOccurrenceRule3Through5SpatialEvidence?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (computed : input.localizedOccurrenceRule3Through5SpatialEvidence?
      target view = some evidence) :
    input.DeclarativeLocalizedOccurrenceRule3Through5SpatialEvidence
      target view evidence := by
  unfold localizedOccurrenceRule3Through5SpatialEvidence? at computed
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases baseComputed : input.localizedOccurrenceFourLigandFrame? target with
      | none => simp [centerComputed, baseComputed] at computed
      | some base =>
          cases keysComputed : input.buildLocalizedOccurrenceRule3Through5KeyFrame?
              target view base with
          | none => simp [centerComputed, baseComputed, keysComputed] at computed
          | some keys =>
              cases trackedComputed : input.safeLocalizedOccurrenceRule3Through5TrackedOrder?
                  keys with
              | none =>
                  simp [centerComputed, baseComputed, keysComputed,
                    trackedComputed] at computed
              | some tracked =>
                  cases pointsComputed : tracked.highestFirst.mapM fun index =>
                      input.localizedRerootCursorSpatialPoint? (base.cursorAt index) with
                  | none =>
                      simp [centerComputed, baseComputed, keysComputed,
                        trackedComputed, pointsComputed] at computed
                  | some points =>
                      simp [centerComputed, baseComputed, keysComputed,
                        trackedComputed, pointsComputed] at computed
                      subst evidence
                      exact ⟨
                        (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
                          target center).mp centerComputed,
                        input.localizedOccurrenceFourLigandFrame?_sound
                          target base baseComputed,
                        input.buildLocalizedOccurrenceRule3Through5KeyFrame?_sound
                          target view base keys keysComputed,
                        input.safeLocalizedOccurrenceRule3Through5TrackedOrder?_sound
                          keys tracked trackedComputed,
                        input.mapM_localizedRerootCursorSpatialPoint?_sound_for_rule3Through5
                          base tracked.highestFirst points pointsComputed⟩

/-- State-relative tetrahedral descriptor through the current Rules-1a--5 implementation. -/
noncomputable def localizedOccurrenceRule3Through5Descriptor?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.localizedOccurrenceRule3Through5SpatialEvidence? target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- Independent positive meaning of the cumulative occurrence descriptor. -/
def DeclarativeLocalizedOccurrenceRule3Through5Descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    input.DeclarativeLocalizedOccurrenceRule3Through5SpatialEvidence
      target view evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

theorem localizedOccurrenceRule3Through5Descriptor?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceRule3Through5Descriptor?
      target view = some descriptor) :
    input.DeclarativeLocalizedOccurrenceRule3Through5Descriptor
      target view descriptor := by
  unfold localizedOccurrenceRule3Through5Descriptor? at computed
  cases evidenceComputed : input.localizedOccurrenceRule3Through5SpatialEvidence?
      target view with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
      | none => simp [evidenceComputed, rawComputed] at computed
      | some raw =>
          simp [evidenceComputed, rawComputed] at computed
          subst descriptor
          exact ⟨evidence, raw,
            input.localizedOccurrenceRule3Through5SpatialEvidence?_sound
              target view evidence evidenceComputed,
            (descriptorOfPriorityOrderedPoints?_eq_some_iff
              evidence.points raw).mp rawComputed,
            rfl⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
