import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey

/-!
Actual source-native planar observation instantiates the generic two-pass physical-unit frame.
Raw keys discover actual units, the unchanged topology resolver chooses the common exclusion
policy, and every cursor is compiled under that same policy. The exact frame judgment uses the
planar node relation, never the old source-spatial node judgment.

A separate Rules-3--5 builder retains the existing four-key record shape and unchanged compound
Rule-4/5 builder at the same original target, view, fuel and cursor positions. Its sound judgment
combines exact planar-frame meaning with the existing independent Rule-4/5 alignment relation.
No completeness converse is claimed for that weaker compound soundness relation. Pure key
comparison is reused: decisive Rule 3 is ordinary and pseudo comparison requires a Rule-3 tie.

This changes no existing production reader and supplies no closed successful four-key fixture.
Production descriptor integration, a closed tied constitutional planar frame, mixed geometry and
broader domains remain TECHNICAL_PROOF_REQUIRED. Planar scientific convention remains
HUMAN_REVIEW_REQUIRED and source adoption remains EXTERNAL_EVIDENCE_REQUIRED.
-/

noncomputable def planarObserver (source : AuthoritativeChemicalInput) : Rule3Observer source :=
  { observe := aromaticCanonicalPlanarRule3Node? source
    NodeOutcome := CanonicalAromaticCanonicalPlanarRule3NodeOutcome source
    nodeExact := aromaticCanonicalPlanarRule3Node?_eq_some_iff_canonical source }

noncomputable def buildAromaticCanonicalPlanarRule3Frame?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option source.AromaticCanonicalRule3CanonicalKeyFrame :=
  buildRule3ObserverFrame? (planarObserver source) fuel cursors

abbrev CanonicalAromaticCanonicalPlanarRule3Frame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :=
  CanonicalRule3ObserverFrame (carrierFuel := carrierFuel) (planarObserver source)

theorem buildAromaticCanonicalPlanarRule3Frame?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame) :
    buildAromaticCanonicalPlanarRule3Frame? source fuel cursors = some frame ↔
      CanonicalAromaticCanonicalPlanarRule3Frame source fuel cursors frame :=
  buildRule3ObserverFrame?_eq_some_iff (planarObserver source) fuel cursors frame

theorem buildAromaticCanonicalPlanarRule3Frame?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (computed : buildAromaticCanonicalPlanarRule3Frame? source fuel cursors = some frame) :
    CanonicalAromaticCanonicalPlanarRule3Frame source fuel cursors frame :=
  (buildAromaticCanonicalPlanarRule3Frame?_eq_some_iff source fuel cursors frame).mp computed

theorem buildAromaticCanonicalPlanarRule3Frame?_complete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (canonical : CanonicalAromaticCanonicalPlanarRule3Frame source fuel cursors frame) :
    buildAromaticCanonicalPlanarRule3Frame? source fuel cursors = some frame :=
  (buildAromaticCanonicalPlanarRule3Frame?_eq_some_iff source fuel cursors frame).mpr canonical

theorem buildAromaticCanonicalPlanarRule3Frame?_eq_none_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    buildAromaticCanonicalPlanarRule3Frame? source fuel cursors = none ↔
      ¬∃ frame, CanonicalAromaticCanonicalPlanarRule3Frame source fuel cursors frame :=
  buildRule3ObserverFrame?_eq_none_iff (planarObserver source) fuel cursors

theorem CanonicalAromaticCanonicalPlanarRule3Frame.keys_length
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (canonical : CanonicalAromaticCanonicalPlanarRule3Frame source fuel cursors frame) :
    frame.keys.length = cursors.length :=
  CanonicalRule3ObserverFrame.keys_length (planarObserver source) fuel cursors frame canonical

theorem CanonicalAromaticCanonicalPlanarRule3Frame.global_exclusion_policy
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (canonical : CanonicalAromaticCanonicalPlanarRule3Frame source fuel cursors frame) :
    frame.excluded = source.aromaticCanonicalRule3ExcludedPhysicalUnits
      frame.rawKeys frame.resolution :=
  CanonicalRule3ObserverFrame.global_exclusion_policy
    (planarObserver source) fuel cursors frame canonical

noncomputable def buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option (source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule3Frame ← buildAromaticCanonicalPlanarRule3Frame? source fuel cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← cursors.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel)
    if rule45Length : rule45Keys.length = 4 then
      some { rule3Frame, rule3Length, rule45Keys, rule45Length }
    else none
  else none

private theorem compoundKeyList_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat) :
    ∀ (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (keys : List source.AromaticCanonicalRerootCompoundRule45Key),
      cursors.mapM (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) =
        some keys →
      List.Forall₂ (source.DeclarativeAromaticCanonicalRerootCompoundRule45Key target view fuel)
        cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact .nil
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalRerootCompoundRule45Key?
          target view fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact .cons
                (source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
                  target view fuel cursor head headComputed)
                (compoundKeyList_sound source target view fuel cursors tail tailComputed)

def DeclarativeAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) : Prop :=
  CanonicalAromaticCanonicalPlanarRule3Frame source fuel cursors frame.rule3Frame ∧
    frame.rule3Frame.keys.length = 4 ∧
    List.Forall₂ (source.DeclarativeAromaticCanonicalRerootCompoundRule45Key target view fuel)
      cursors frame.rule45Keys ∧ frame.rule45Keys.length = 4

theorem buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view fuel cursors = some frame) :
    DeclarativeAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame
      source target view fuel cursors frame := by
  unfold buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame? at computed
  cases rule3Computed : buildAromaticCanonicalPlanarRule3Frame? source fuel cursors with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : cursors.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) with
        | none => simp [rule3Computed, rule45Computed] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed, rule45Length] at computed
              subst frame
              exact ⟨buildAromaticCanonicalPlanarRule3Frame?_sound source fuel cursors
                  rule3Frame rule3Computed, rule3Length,
                compoundKeyList_sound source target view fuel cursors rule45Keys rule45Computed,
                rule45Length⟩
            · simp [rule3Computed, rule45Computed, rule45Length] at computed
      · simp [rule3Computed, rule3Length] at computed

theorem buildPlanarRule3Through5Frame?_eq_none_of_wrong_cursor_count
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (wrong : cursors.length ≠ 4) :
    buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view fuel cursors = none := by
  cases computed : buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view fuel cursors with
  | none => rfl
  | some frame =>
      have meaning := buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?_sound
        source target view fuel cursors frame computed
      have lengths := CanonicalAromaticCanonicalPlanarRule3Frame.keys_length
        source fuel cursors frame.rule3Frame meaning.1
      exact False.elim (wrong (lengths.symm.trans frame.rule3Length))

theorem buildPlanarRule3Through5Frame?_eq_none_of_rule3_failure
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (failed : buildAromaticCanonicalPlanarRule3Frame? source fuel cursors = none) :
    buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view fuel cursors = none := by
  simp [buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?, failed]

theorem buildPlanarRule3Through5Frame?_eq_none_of_rule45_failure
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (firstPass : buildAromaticCanonicalPlanarRule3Frame? source fuel cursors = some rule3Frame)
    (failed : cursors.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) = none) :
    buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
      source target view fuel cursors = none := by
  unfold buildAromaticCanonicalPlanarOccurrenceRule3Through5KeyFrame?
  rw [firstPass]
  by_cases length : rule3Frame.keys.length = 4
  · simp [failed]
  · simp [length]

/-- Pure comparison uses the shared record only; these laws assert no old spatial provenance. -/
theorem planarFrame_rule3_gt_is_ordinary
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = .gt) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At frame left right =
      { ordering := .gt, pseudo := false } :=
  source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_gt frame left right strict

theorem planarFrame_rule3_tie_reaches_actual_rule45
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (tied : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = .eq) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At frame left right =
      source.compareAromaticCanonicalRerootCompoundThroughRule5
        (frame.keyAt left).rule45 (frame.keyAt right).rule45 :=
  source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq frame left right tied

theorem planarFrame_pseudo_requires_rule3_tie
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (pseudo : (source.compareAromaticCanonicalOccurrenceRule3Through5At frame left right).pseudo = true) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = .eq :=
  source.compareAromaticCanonicalOccurrenceRule3Through5At_pseudo_implies_rule3_eq
    frame left right pseudo

end TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3FrameAndComparison
