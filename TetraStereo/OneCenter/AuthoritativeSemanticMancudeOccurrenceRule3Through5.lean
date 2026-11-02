import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CanonicalFrame
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule45

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Source-canonical occurrence comparison through Rule 5

This is the missing pre-Rule-6 composition.  One common physical-unit-aware Rule-3 frame is aligned
with the already certified compound Rules-4a--5 keys.  The unary comparison order is exactly
Rules 1a, 1b, 2, 3, 4a, 4b, 4c, then 5.  A decisive Rule-3 comparison is always ordinary;
pseudoasymmetry can arise only after Rule 3 ties and Rule 5 is reached.
-/

/-- One source ligand's cumulative Rules-1a--5 data. -/
structure AromaticCanonicalOccurrenceRule3Through5Key
    (source : AuthoritativeChemicalInput) where
  rule3 : source.AromaticCanonicalUncancelledRule3SpatialKey
  rule45 : source.AromaticCanonicalRerootCompoundRule45Key

noncomputable def compareAromaticCanonicalOccurrenceRule3Through5Keys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalOccurrenceRule3Through5Key →
      source.AromaticCanonicalOccurrenceRule3Through5Key → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.rule3)
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys)
    (Ordering.byKey (fun key => key.rule45)
      source.compareAromaticCanonicalRerootCompoundRule45Keys)

theorem compareAromaticCanonicalOccurrenceRule3Through5Keys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalOccurrenceRule3Through5Keys := by
  letI : Std.TransCmp source.compareAromaticCanonicalUncancelledRule3SpatialKeys :=
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
  letI : Std.TransCmp source.compareAromaticCanonicalRerootCompoundRule45Keys :=
    source.compareAromaticCanonicalRerootCompoundRule45Keys_transCmp
  unfold compareAromaticCanonicalOccurrenceRule3Through5Keys
  infer_instance

/-- One common four-ligand Rule-3 policy and position-aligned Rules-4a--5 keys. -/
structure AromaticCanonicalOccurrenceRule3Through5KeyFrame
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame
  rule3Length : rule3Frame.keys.length = 4
  rule45Keys : List source.AromaticCanonicalRerootCompoundRule45Key
  rule45Length : rule45Keys.length = 4

noncomputable def buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option (source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let rule3Frame ← source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← cursors.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel)
    if rule45Length : rule45Keys.length = 4 then
      some { rule3Frame, rule3Length, rule45Keys, rule45Length }
    else none
  else none

private theorem mapM_buildAromaticCanonicalRerootCompoundRule45Key?_sound_for_rule3Through5
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) :
    ∀ (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (keys : List source.AromaticCanonicalRerootCompoundRule45Key),
      cursors.mapM
          (source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) =
        some keys →
      List.Forall₂
        (source.DeclarativeAromaticCanonicalRerootCompoundRule45Key target view fuel)
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
              (source.buildAromaticCanonicalRerootCompoundRule45Key?
                target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact .cons
                (source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
                  target view fuel cursor head headComputed)
                (mapM_buildAromaticCanonicalRerootCompoundRule45Key?_sound_for_rule3Through5
                  source target view fuel cursors tail tailComputed)

def DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) : Prop :=
  source.DeclarativeAromaticCanonicalRule3CanonicalKeyFrame
      fuel cursors frame.rule3Frame ∧
    frame.rule3Frame.keys.length = 4 ∧
    List.Forall₂
      (source.DeclarativeAromaticCanonicalRerootCompoundRule45Key target view fuel)
      cursors frame.rule45Keys ∧
    frame.rule45Keys.length = 4

theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel cursors = some frame) :
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyFrame
      target view fuel cursors frame := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? at computed
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      fuel cursors with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases rule3Length : rule3Frame.keys.length = 4
      · cases rule45Computed : cursors.mapM
            (source.buildAromaticCanonicalRerootCompoundRule45Key?
              target view fuel) with
        | none => simp [rule3Computed, rule45Computed] at computed
        | some rule45Keys =>
            by_cases rule45Length : rule45Keys.length = 4
            · simp [rule3Computed, rule3Length, rule45Computed,
                rule45Length] at computed
              subst frame
              exact ⟨
                source.buildAromaticCanonicalRule3CanonicalKeyFrame?_sound
                  fuel cursors rule3Frame rule3Computed,
                rule3Length,
                mapM_buildAromaticCanonicalRerootCompoundRule45Key?_sound_for_rule3Through5
                  source target view fuel cursors rule45Keys rule45Computed,
                rule45Length⟩
            · simp [rule3Computed, rule45Computed,
                rule45Length] at computed
      · simp [rule3Computed, rule3Length] at computed

def AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (index : Fin 4) : source.AromaticCanonicalOccurrenceRule3Through5Key :=
  { rule3 := frame.rule3Frame.keys.get (Fin.cast frame.rule3Length.symm index)
    rule45 := frame.rule45Keys.get (Fin.cast frame.rule45Length.symm index) }

/-- Descriptor-facing comparison with the Rule-5 pseudoasymmetry signal retained. -/
noncomputable def compareAromaticCanonicalOccurrenceRule3Through5At
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) : ConstitutionalRule5Comparison :=
  let leftKey := frame.keyAt left
  let rightKey := frame.keyAt right
  match source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      leftKey.rule3 rightKey.rule3 with
  | .lt => { ordering := .lt, pseudo := false }
  | .gt => { ordering := .gt, pseudo := false }
  | .eq => source.compareAromaticCanonicalRerootCompoundThroughRule5
      leftKey.rule45 rightKey.rule45

theorem compareAromaticCanonicalOccurrenceRule3Through5At_ordering
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4) :
    (source.compareAromaticCanonicalOccurrenceRule3Through5At
      frame left right).ordering =
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys
        (frame.keyAt left) (frame.keyAt right) := by
  unfold compareAromaticCanonicalOccurrenceRule3Through5At
    compareAromaticCanonicalOccurrenceRule3Through5Keys
  generalize rule3Comparison :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (frame.keyAt left).rule3 (frame.keyAt right).rule3 = outcome
  cases outcome <;>
    simp [compareLex, Ordering.byKey, rule3Comparison,
      source.compareAromaticCanonicalRerootCompoundThroughRule5_ordering]

theorem compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_gt
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.gt) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At frame left right =
      { ordering := Ordering.gt, pseudo := false } := by
  simp [compareAromaticCanonicalOccurrenceRule3Through5At, strict]

theorem compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (tied : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.eq) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At frame left right =
      source.compareAromaticCanonicalRerootCompoundThroughRule5
        (frame.keyAt left).rule45 (frame.keyAt right).rule45 := by
  simp [compareAromaticCanonicalOccurrenceRule3Through5At, tied]

theorem compareAromaticCanonicalOccurrenceRule3Through5At_pseudo_implies_rule3_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (pseudo : (source.compareAromaticCanonicalOccurrenceRule3Through5At
      frame left right).pseudo = true) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = Ordering.eq := by
  unfold compareAromaticCanonicalOccurrenceRule3Through5At at pseudo
  generalize compared : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (frame.keyAt left).rule3 (frame.keyAt right).rule3 = outcome at pseudo
  cases outcome <;> simp_all

theorem compareAromaticCanonicalOccurrenceRule3Through5At_transCmp
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Std.TransCmp (fun left right =>
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
        frame left right).ordering) := by
  letI : Std.TransCmp source.compareAromaticCanonicalOccurrenceRule3Through5Keys :=
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys_transCmp
  have same : (fun left right =>
      (source.compareAromaticCanonicalOccurrenceRule3Through5At
        frame left right).ordering) =
      Ordering.byKey frame.keyAt
        source.compareAromaticCanonicalOccurrenceRule3Through5Keys := by
    funext left right
    exact source.compareAromaticCanonicalOccurrenceRule3Through5At_ordering
      frame left right
  rw [same]
  infer_instance

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
