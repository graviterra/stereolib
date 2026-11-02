import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5FixedPoint
import TetraStereo.OneCenter.CIPDescriptorBearingPipelineAffineInvariance

set_option autoImplicit false

/-!
# Naturality of the authoritative occurrence Rule 3--5 fixed point

This module isolates reusable transport arguments for occurrence evaluators. Five source-level
producer laws transport the complete spatial-evidence pipeline; exact affine orientation reversal
then complements the local descriptor. When one uniform label action is valid over the entire
occurrence carrier, well-founded uniqueness transports the scheduled auxiliary state. Molecular
automorphisms with occurrence-dependent pseudoasymmetric parity must use a local transport instead.
-/

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.DeclarativeCIP.OccurrenceSystem

/-- General descriptor transport for a nontrivial source automorphism.  The transported evidence
may have different center, reroot, key, and tracked-order fields; only the descriptor-visible
point order and pseudo-comparison count must be natural. -/
theorem aromaticCanonicalOccurrenceRule3Through5Descriptor?_reflection_of_evidenceTransport
    (source : AuthoritativeChemicalInput) {carrierFuel : ℕ} (ruleFuel : ℕ)
    (permutation : Equiv.Perm (source.AromaticCanonicalOccurrence carrierFuel))
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0)
    (transportEvidence :
      source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel →
        source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (pointsNatural : ∀ evidence,
      (transportEvidence evidence).points = evidence.points.map transform.applyPoint)
    (pseudoComparisonsNatural : ∀ evidence,
      (transportEvidence evidence).tracked.pseudoComparisons =
        evidence.tracked.pseudoComparisons)
    (candidate : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (evidenceNatural :
      source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
          (permutation target)
          (source.aromaticCanonicalDependencyView
            (transportState permutation LocalizedTetrahedralRSPseudoDescriptor.swap candidate)
            (permutation target)) ruleFuel =
        (source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
          target (source.aromaticCanonicalDependencyView candidate target) ruleFuel).map
            transportEvidence) :
    source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        (permutation target)
        (source.aromaticCanonicalDependencyView
          (transportState permutation LocalizedTetrahedralRSPseudoDescriptor.swap candidate)
          (permutation target)) ruleFuel =
      (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target (source.aromaticCanonicalDependencyView candidate target) ruleFuel).map
          LocalizedTetrahedralRSPseudoDescriptor.swap := by
  unfold aromaticCanonicalOccurrenceRule3Through5Descriptor?
  rw [evidenceNatural]
  cases evidenceComputed :
      source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence? target
        (source.aromaticCanonicalDependencyView candidate target) ruleFuel with
  | none => simp
  | some evidence =>
      simp only [Option.map_some]
      change
        (descriptorOfPriorityOrderedPoints? (transportEvidence evidence).points).bind
              (fun raw => some (classifyTetrahedralRSPseudo raw
                (transportEvidence evidence).tracked.pseudoComparisons)) =
          ((descriptorOfPriorityOrderedPoints? evidence.points).bind
              (fun raw => some (classifyTetrahedralRSPseudo raw
                evidence.tracked.pseudoComparisons))).map
            LocalizedTetrahedralRSPseudoDescriptor.swap
      rw [pointsNatural evidence, pseudoComparisonsNatural evidence,
        descriptorOfPriorityOrderedPoints?_orientationReversingAffine
          transform orientationReversing]
      cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
      | none => simp
      | some raw => simp [classifyTetrahedralRSPseudo_swap]

/-- Complete scheduled-state naturality from a structurally transported evidence producer. -/
theorem aromaticCanonicalScheduledAuxiliaryState_reflection_of_evidenceTransport
    (source : AuthoritativeChemicalInput) {carrierFuel : ℕ} (ruleFuel : ℕ)
    (permutation : Equiv.Perm (source.AromaticCanonicalOccurrence carrierFuel))
    (transform : RationalAffineFrameTransform)
    (orientationReversing : transform.determinant < 0)
    (transportEvidence :
      source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel →
        source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel)
    (pointsNatural : ∀ evidence,
      (transportEvidence evidence).points = evidence.points.map transform.applyPoint)
    (pseudoComparisonsNatural : ∀ evidence,
      (transportEvidence evidence).tracked.pseudoComparisons =
        evidence.tracked.pseudoComparisons)
    (evidenceNatural : ∀ candidate target,
      source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
          (permutation target)
          (source.aromaticCanonicalDependencyView
            (transportState permutation LocalizedTetrahedralRSPseudoDescriptor.swap candidate)
            (permutation target)) ruleFuel =
        (source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
          target (source.aromaticCanonicalDependencyView candidate target) ruleFuel).map
            transportEvidence) :
    let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel
    let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
    ∀ target,
      state (permutation target) =
        (state target).map LocalizedTetrahedralRSPseudoDescriptor.swap := by
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  apply cipModel_natural_of_executableStep_natural
    (source.aromaticCanonicalOccurrenceSystem semantics)
    (source.aromaticCanonicalDerivationStepCorrespondence semantics)
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (source.aromaticCanonicalDepthDependency_wellFounded carrierFuel)
    (source.aromaticCanonicalEvaluatorLocal semantics)
    permutation LocalizedTetrahedralRSPseudoDescriptor.swap
  · intro candidate target
    exact source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_reflection_of_evidenceTransport
      ruleFuel permutation transform orientationReversing transportEvidence
      pointsNatural pseudoComparisonsNatural candidate target
      (evidenceNatural candidate target)
  · exact source.aromaticCanonicalScheduledAuxiliaryState_cipModel semantics

private theorem mapM_map_natural
    {α β γ δ : Type*} (mapInput : α → β) (mapOutput : γ → δ)
    (right : β → Option δ) (left : α → Option γ)
    (natural : ∀ value, right (mapInput value) = (left value).map mapOutput) :
    ∀ values : List α,
      (values.map mapInput).mapM right = (values.mapM left).map (List.map mapOutput)
  | [] => rfl
  | value :: values => by
      rw [List.map_cons, List.mapM_cons, natural value]
      cases computed : left value with
      | none => simp [computed]
      | some output =>
          simp only [Option.map_some]
          rw [mapM_map_natural mapInput mapOutput right left natural values]
          cases tailComputed : values.mapM left with
          | none => simp [tailComputed]
          | some outputs => simp [List.mapM_cons, computed, tailComputed]

/-- Transport a complete Rule-3--5 key frame through independently supplied Rule-3 and compound
Rule-45 transports.  Both four-key cardinality witnesses are inherited structurally. -/
def mapAromaticCanonicalOccurrenceRule3Through5KeyFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (mapRule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame →
      source.AromaticCanonicalRule3CanonicalKeyFrame)
    (rule3LengthNatural : ∀ frame,
      (mapRule3Frame frame).keys.length = frame.keys.length)
    (mapRule45Key : source.AromaticCanonicalRerootCompoundRule45Key →
      source.AromaticCanonicalRerootCompoundRule45Key)
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel :=
  { rule3Frame := mapRule3Frame frame.rule3Frame
    rule3Length := (rule3LengthNatural frame.rule3Frame).trans frame.rule3Length
    rule45Keys := frame.rule45Keys.map mapRule45Key
    rule45Length := by simpa using frame.rule45Length }

/-- Naturality of the complete key-frame builder follows once from naturality of its two actual
producers; no recursive evaluator or concrete molecule is inspected here. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_natural_of_producers
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (leftTarget rightTarget : source.AromaticCanonicalOccurrence carrierFuel)
    (leftView : source.AromaticCanonicalDependencyView leftTarget)
    (rightView : source.AromaticCanonicalDependencyView rightTarget)
    (fuel : Nat)
    (mapCursor : source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalRerootCursor carrierFuel)
    (mapRule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame →
      source.AromaticCanonicalRule3CanonicalKeyFrame)
    (rule3LengthNatural : ∀ frame,
      (mapRule3Frame frame).keys.length = frame.keys.length)
    (mapRule45Key : source.AromaticCanonicalRerootCompoundRule45Key →
      source.AromaticCanonicalRerootCompoundRule45Key)
    (rule3Natural : ∀ cursors,
      source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel
          (cursors.map mapCursor) =
        (source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors).map
          mapRule3Frame)
    (rule45Natural : ∀ cursor,
      source.buildAromaticCanonicalRerootCompoundRule45Key?
          rightTarget rightView fuel (mapCursor cursor) =
        (source.buildAromaticCanonicalRerootCompoundRule45Key?
          leftTarget leftView fuel cursor).map mapRule45Key) :
    ∀ cursors,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          rightTarget rightView fuel (cursors.map mapCursor) =
        (source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          leftTarget leftView fuel cursors).map
            (mapAromaticCanonicalOccurrenceRule3Through5KeyFrame source
              mapRule3Frame rule3LengthNatural mapRule45Key) := by
  intro cursors
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
  rw [rule3Natural cursors]
  have rule45MapM := mapM_map_natural mapCursor mapRule45Key
    (source.buildAromaticCanonicalRerootCompoundRule45Key?
      rightTarget rightView fuel)
    (source.buildAromaticCanonicalRerootCompoundRule45Key?
      leftTarget leftView fuel) rule45Natural cursors
  rw [rule45MapM]
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      fuel cursors with
  | none => simp
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : cursors.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45Key?
              leftTarget leftView fuel) with
        | none => simp
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Length, rule3LengthNatural, rule45Length,
                mapAromaticCanonicalOccurrenceRule3Through5KeyFrame]
            · simp [rule45Length]
      · simp [rule3Length, rule3LengthNatural]

/-- A key-frame transport preserving the complete pair comparator preserves the tracked order and
its pseudo-comparison count in one step. -/
theorem safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_natural
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (mapKeys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel →
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (compareNatural : ∀ keys first second,
      source.compareAromaticCanonicalOccurrenceRule3Through5At
          (mapKeys keys) first second =
        source.compareAromaticCanonicalOccurrenceRule3Through5At keys first second)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? (mapKeys keys) =
      (source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys).map id := by
  simpa using source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_compare
    keys (mapKeys keys) (compareNatural keys)

/-- General transport of all five fields produced by the occurrence evidence pipeline. -/
def transportAromaticCanonicalOccurrenceSpatialEvidenceStages
    {source : AuthoritativeChemicalInput} {carrierFuel : ℕ}
    (transform : RationalAffineFrameTransform)
    (mapCenter : source.AromaticCanonicalTetrahedralCenter →
      source.AromaticCanonicalTetrahedralCenter)
    (mapBase : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel →
      source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (mapKeys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel →
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapTracked : TrackedLocalizedLigandOrder → TrackedLocalizedLigandOrder)
    (evidence : source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel) :
    source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel :=
  { center := mapCenter evidence.center
    base := mapBase evidence.base
    keys := mapKeys evidence.keys
    tracked := mapTracked evidence.tracked
    points := evidence.points.map transform.applyPoint }

/-- Monadic evidence naturality follows en masse from naturality of its five actual producers. -/
theorem aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?_natural_of_stages
    (source : AuthoritativeChemicalInput) {carrierFuel : ℕ} (ruleFuel : ℕ)
    (permutation : Equiv.Perm (source.AromaticCanonicalOccurrence carrierFuel))
    (transform : RationalAffineFrameTransform)
    (mapCenter : source.AromaticCanonicalTetrahedralCenter →
      source.AromaticCanonicalTetrahedralCenter)
    (mapBase : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel →
      source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (mapKeys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel →
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (mapTracked : TrackedLocalizedLigandOrder → TrackedLocalizedLigandOrder)
    (centerNatural : ∀ target,
      source.aromaticCanonicalOccurrenceTetrahedralCenter? (permutation target) =
        (source.aromaticCanonicalOccurrenceTetrahedralCenter? target).map mapCenter)
    (baseNatural : ∀ target,
      source.aromaticCanonicalOccurrenceFourLigandFrame? (permutation target) =
        (source.aromaticCanonicalOccurrenceFourLigandFrame? target).map mapBase)
    (keysNatural : ∀ candidate target base,
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          (permutation target)
          (source.aromaticCanonicalDependencyView
            (transportState permutation LocalizedTetrahedralRSPseudoDescriptor.swap candidate)
            (permutation target)) ruleFuel (mapBase base).roots =
        (source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
          target (source.aromaticCanonicalDependencyView candidate target)
          ruleFuel base.roots).map mapKeys)
    (trackedNatural : ∀ keys,
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? (mapKeys keys) =
        (source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys).map mapTracked)
    (pointsNatural : ∀ base tracked,
      (mapTracked tracked).highestFirst.mapM (fun index =>
          source.aromaticCanonicalRerootSpatialPoint? ((mapBase base).cursorAt index)) =
        (tracked.highestFirst.mapM (fun index =>
          source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index))).map
            (List.map transform.applyPoint)) :
    ∀ candidate target,
      source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
          (permutation target)
          (source.aromaticCanonicalDependencyView
            (transportState permutation LocalizedTetrahedralRSPseudoDescriptor.swap candidate)
            (permutation target)) ruleFuel =
        (source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
          target (source.aromaticCanonicalDependencyView candidate target) ruleFuel).map
            (transportAromaticCanonicalOccurrenceSpatialEvidenceStages
              transform mapCenter mapBase mapKeys mapTracked) := by
  intro candidate target
  unfold aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
  rw [centerNatural target]
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp
  | some center =>
      simp
      rw [baseNatural target]
      cases baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target with
      | none => simp
      | some base =>
          simp
          rw [keysNatural candidate target base]
          cases keysComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
              target (source.aromaticCanonicalDependencyView candidate target)
              ruleFuel base.roots with
          | none => simp
          | some keys =>
              simp
              rw [trackedNatural keys]
              cases trackedComputed :
                  source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys with
              | none => simp
              | some tracked =>
                  simp
                  rw [pointsNatural base tracked]
                  cases pointsComputed : tracked.highestFirst.mapM (fun index =>
                      source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)) with
                  | none => simp
                  | some points =>
                      simp [transportAromaticCanonicalOccurrenceSpatialEvidenceStages]

/-- Pointwise cursor-coordinate naturality lifts automatically to every priority-order `mapM`. -/
theorem mapM_aromaticCanonicalRerootSpatialPoint?_natural
    (source : AuthoritativeChemicalInput) {carrierFuel : ℕ}
    (transform : RationalAffineFrameTransform)
    (mapBase : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel →
      source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (pointNatural : ∀ base index,
      source.aromaticCanonicalRerootSpatialPoint? ((mapBase base).cursorAt index) =
        (source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)).map
          transform.applyPoint)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    ∀ order : List (Fin 4),
      order.mapM (fun index =>
          source.aromaticCanonicalRerootSpatialPoint? ((mapBase base).cursorAt index)) =
        (order.mapM (fun index =>
          source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index))).map
            (List.map transform.applyPoint)
  | [] => rfl
  | index :: order => by
      rw [List.mapM_cons, pointNatural base index,
        mapM_aromaticCanonicalRerootSpatialPoint?_natural
          source transform mapBase pointNatural base order]
      cases pointComputed :
          source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index) <;>
        cases tailComputed : order.mapM (fun next =>
          source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt next)) <;>
        simp [pointComputed, tailComputed]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
