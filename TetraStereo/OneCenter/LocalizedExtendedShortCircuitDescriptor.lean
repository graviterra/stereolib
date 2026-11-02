import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedDescriptorExecutable

set_option autoImplicit false
namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-! Tetrahedral descriptor using independently justified demand-driven Rule3 keys.
All Rules4a–5, strict ordering, pseudo classification, and rational spatial checks are unchanged.
Positive soundness targets the successor declarative relation; equality with original refusals
and independent chemical completeness are not asserted. -/

/-- Compile all four cumulative Rules-1a--5 keys with descriptor-bearing Rule 3. -/
def buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let descriptorFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let rule3Frame ← input.buildLocalizedExtendedShortCircuitRule3FrameExec?
    target view descriptorFuel base.cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45KeyExec? target view rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame
          rule3Length
          rule45Keys
          rule45Length }
    else none
  else none

private theorem mapM_rule45_sound_for_extendedShortCircuitRule3
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
                (input.mapM_rule45_sound_for_extendedShortCircuitRule3
                  target view fuel cursors tail tailComputed)

/-- Independent meaning of the descriptor-bearing four-ligand compilation. -/
def DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) : Prop :=
  input.DeclarativeLocalizedExtendedShortCircuitRule3Frame
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      base.cursors frame.rule3Frame ∧
    frame.rule3Frame.keys.length = 4 ∧
    List.Forall₂
      (input.DeclarativeLocalizedRerootCompoundRule45Key target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel))
      base.cursors frame.rule45Keys ∧
    frame.rule45Keys.length = 4

/-- Successful descriptor-bearing four-ligand compilation accounts for both complete aligned key
families. -/
theorem buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      target view base = some frame) :
    input.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame
      target view base frame := by
  unfold buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? at computed
  have rule45Eq := funext fun cursor =>
    input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor
  simp only [← rule45Eq] at computed
  let descriptorFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  cases rule3Computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view descriptorFuel base.cursors with
  | none => simp [rule3Computed, descriptorFuel] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : base.cursors.mapM
            (input.buildLocalizedRerootCompoundRule45Key?
              target view rule45Fuel) with
        | none =>
            simp [rule3Computed, rule45Computed,
              descriptorFuel, rule45Fuel] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length,
                descriptorFuel, rule45Fuel] at computed
              subst frame
              exact ⟨
                input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound
                  target view descriptorFuel base.cursors rule3Frame rule3Computed,
                rule3Length,
                input.mapM_rule45_sound_for_extendedShortCircuitRule3
                  target view rule45Fuel base.cursors rule45Keys rule45Computed,
                rule45Length⟩
            · simp [rule3Computed, rule45Computed, rule45Length,
                descriptorFuel, rule45Fuel] at computed
      · simp [rule3Computed, rule3Length, descriptorFuel] at computed

/-- Geometry evidence ranked by the descriptor-bearing cumulative Rules-1a--5 frame. -/
def localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← input.localizedNoDoubleFourLigandFrameExec? target
  let keys ← input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
    target view base
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

private theorem mapM_spatial_sound_for_extendedShortCircuitRule3
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
                (input.mapM_spatial_sound_for_extendedShortCircuitRule3
                  base order tail tailComputed)

/-- Independent meaning of descriptor-bearing ranked spatial evidence. -/
def DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) : Prop :=
  input.RealTetrahedralCenterNode target.1.node evidence.center ∧
    input.DeclarativeLocalizedOccurrenceFourLigandFrame target evidence.base ∧
    input.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame
      target view evidence.base evidence.keys ∧
    input.DeclarativeSafeLocalizedOccurrenceRule3Through5TrackedOrder
      evidence.keys evidence.tracked ∧
    List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (evidence.base.cursorAt index) point)
      evidence.tracked.highestFirst evidence.points

/-- Every successful evidence object has the independent descriptor-bearing key, order, and
coordinate meaning. -/
theorem localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (computed : input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
      target view = some evidence) :
    input.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence
      target view evidence := by
  unfold localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence? at computed
  simp only [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?,
    localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?] at computed
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases baseComputed : input.localizedOccurrenceFourLigandFrame? target with
      | none => simp [centerComputed, baseComputed] at computed
      | some base =>
          cases keysComputed :
              input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
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
                        input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_sound
                          target view base keys keysComputed,
                        input.safeLocalizedOccurrenceRule3Through5TrackedOrder?_sound
                          keys tracked trackedComputed,
                        input.mapM_spatial_sound_for_extendedShortCircuitRule3
                          base tracked.highestFirst points pointsComputed⟩

/-- State-relative tetrahedral descriptor using descriptor-bearing Rule 3. -/
def localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
    target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- Independent positive meaning of the descriptor-bearing cumulative occurrence descriptor. -/
def DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    input.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence
      target view evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

/-- Every emitted final tetrahedral descriptor is justified by the descriptor-bearing recursive
Rule-3 construction, complete Rules 4a--5 keys, strict total order, and exact spatial relation. -/
theorem localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view = some descriptor) :
    input.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
      target view descriptor := by
  unfold localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? at computed
  cases evidenceComputed :
      input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
        target view with
  | none => simp [evidenceComputed] at computed
  | some evidence =>
      cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
      | none => simp [evidenceComputed, rawComputed] at computed
      | some raw =>
          simp [evidenceComputed, rawComputed] at computed
          subst descriptor
          exact ⟨evidence, raw,
            input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?_sound
              target view evidence evidenceComputed,
            (descriptorOfPriorityOrderedPoints?_eq_some_iff
              evidence.points raw).mp rawComputed,
            rfl⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
