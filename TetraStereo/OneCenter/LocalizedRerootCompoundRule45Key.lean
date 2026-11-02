import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcKey

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Compound Rule-5 readings over occurrence reroot cursors

Rule 5 is reached only after the complete compound Rules-4b/4c key ties.  It compares the same
hierarchy twice, under common reflection-variant references R and S.  The R reading supplies the
priority direction; disagreement of the S reading with that direction is the `±2` signal used by
the tetrahedral uppercase/lowercase classifier.

Lowercase `r/s` observations remain in the cumulative prior-rule vector but contribute no Rule-5
bit: P-92.6 describes them as reflection-invariant.  Temporary uppercase auxiliary descriptors
are represented by the occurrence state's `.chiral R/S` cases and do contribute.
-/

namespace CertifiedLocalizedCIPInput

/-- Select the cumulative Rule-5 stage belonging to one ligand's own Rule-4b reference and one
common Rule-5 reference. -/
def localizedRule5StageFor
    (rule4bReference : Option RS) (commonReference : RS) :
    LocalizedCumulativeRule45Stage :=
  match rule4bReference with
  | none => .rule5NoRule4bReference commonReference
  | some reference => .rule5 reference commonReference

/-- One normatively sequenced Rule-4b/4c alternative plus both complete Rule-5 readings. -/
structure LocalizedRerootRule5Reading
    (input : CertifiedLocalizedCIPInput) where
  prior : input.LocalizedRerootRule4bcReading
  commonR : input.LocalizedRerootCumulativeRule45Key
  commonS : input.LocalizedRerootCumulativeRule45Key

/-- Compile both common-reference readings without changing the normative alternative sequence
fixed by the preceding compound Rules-4b/4c key. -/
noncomputable def buildLocalizedRerootRule5Reading?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    Option input.LocalizedRerootRule5Reading := do
  let commonR ← input.buildLocalizedRerootCumulativeRule45Key?
    (localizedRule5StageFor prior.reference? .R) target view fuel cursor
  let commonS ← input.buildLocalizedRerootCumulativeRule45Key?
    (localizedRule5StageFor prior.reference? .S) target view fuel cursor
  some { prior := prior, commonR := commonR, commonS := commonS }

/-- Independent meaning of one successful pair of common-reference readings. -/
def DeclarativeLocalizedRerootRule5Reading
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading) : Prop :=
  reading.prior = prior ∧
    input.DeclarativeLocalizedRerootCumulativeRule45Key
      (localizedRule5StageFor prior.reference? .R)
      target view fuel cursor reading.commonR ∧
    input.DeclarativeLocalizedRerootCumulativeRule45Key
      (localizedRule5StageFor prior.reference? .S)
      target view fuel cursor reading.commonS

theorem buildLocalizedRerootRule5Reading?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5Reading?
      target view fuel cursor prior = some reading) :
    input.DeclarativeLocalizedRerootRule5Reading
      target view fuel cursor prior reading := by
  unfold buildLocalizedRerootRule5Reading? at computed
  cases commonRComputed : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .R)
      target view fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      cases commonSComputed : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .S)
          target view fuel cursor with
      | none => simp [commonRComputed, commonSComputed] at computed
      | some commonS =>
          simp [commonRComputed, commonSComputed] at computed
          subst reading
          exact ⟨rfl,
            input.buildLocalizedRerootCumulativeRule45Key?_sound
              (localizedRule5StageFor prior.reference? .R)
              target view fuel cursor commonR commonRComputed,
            input.buildLocalizedRerootCumulativeRule45Key?_sound
              (localizedRule5StageFor prior.reference? .S)
              target view fuel cursor commonS commonSComputed⟩

/-- Pointwise Rule-5 derivations in the canonical prior-reading order. -/
inductive DeclarativeLocalizedRerootRule5Readings
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List input.LocalizedRerootRule4bcReading →
      List input.LocalizedRerootRule5Reading → Prop
  | nil : DeclarativeLocalizedRerootRule5Readings
      input target view fuel cursor [] []
  | cons {prior priors reading readings}
      (head : input.DeclarativeLocalizedRerootRule5Reading
        target view fuel cursor prior reading)
      (tail : input.DeclarativeLocalizedRerootRule5Readings
        target view fuel cursor priors readings) :
      DeclarativeLocalizedRerootRule5Readings input target view fuel cursor
        (prior :: priors) (reading :: readings)

noncomputable def buildLocalizedRerootRule5Readings?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List input.LocalizedRerootRule4bcReading →
      Option (List input.LocalizedRerootRule5Reading)
  | [] => some []
  | prior :: priors => do
      let reading ← input.buildLocalizedRerootRule5Reading?
        target view fuel cursor prior
      let readings ← input.buildLocalizedRerootRule5Readings?
        target view fuel cursor priors
      some (reading :: readings)

theorem buildLocalizedRerootRule5Readings?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ priors readings,
      input.buildLocalizedRerootRule5Readings?
        target view fuel cursor priors = some readings →
      input.DeclarativeLocalizedRerootRule5Readings
        target view fuel cursor priors readings
  | [], readings, computed => by
      simp [buildLocalizedRerootRule5Readings?] at computed
      subst readings
      exact DeclarativeLocalizedRerootRule5Readings.nil
  | prior :: priors, readings, computed => by
      unfold buildLocalizedRerootRule5Readings? at computed
      cases headComputed : input.buildLocalizedRerootRule5Reading?
          target view fuel cursor prior with
      | none => simp [headComputed] at computed
      | some reading =>
          cases tailComputed : input.buildLocalizedRerootRule5Readings?
              target view fuel cursor priors with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              exact DeclarativeLocalizedRerootRule5Readings.cons
                (input.buildLocalizedRerootRule5Reading?_sound
                  target view fuel cursor prior reading headComputed)
                (input.buildLocalizedRerootRule5Readings?_sound
                  target view fuel cursor priors tail tailComputed)

/-- Complete through-Rule-5 key. -/
structure LocalizedRerootCompoundRule45Key
    (input : CertifiedLocalizedCIPInput) where
  prior : input.LocalizedRerootCompoundRule4bcKey
  rule5Readings : List input.LocalizedRerootRule5Reading

noncomputable def buildLocalizedRerootCompoundRule45Key?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key := do
  let prior ← input.buildLocalizedRerootCompoundRule4bcKey?
    target view fuel cursor
  let readings ← input.buildLocalizedRerootRule5Readings?
    target view fuel cursor prior.readings
  some { prior := prior, rule5Readings := readings }

def DeclarativeLocalizedRerootCompoundRule45Key
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key) : Prop :=
  input.DeclarativeLocalizedRerootCompoundRule4bcKey
      target view fuel cursor key.prior ∧
    input.DeclarativeLocalizedRerootRule5Readings
      target view fuel cursor key.prior.readings key.rule5Readings

theorem buildLocalizedRerootCompoundRule45Key?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel cursor = some key) :
    input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel cursor key := by
  unfold buildLocalizedRerootCompoundRule45Key? at computed
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      cases readingsComputed : input.buildLocalizedRerootRule5Readings?
          target view fuel cursor prior.readings with
      | none => simp [priorComputed, readingsComputed] at computed
      | some readings =>
          simp [priorComputed, readingsComputed] at computed
          subst key
          exact ⟨
            input.buildLocalizedRerootCompoundRule4bcKey?_sound
              target view fuel cursor prior priorComputed,
            input.buildLocalizedRerootRule5Readings?_sound
              target view fuel cursor prior.readings readings readingsComputed⟩

/-- Descriptor projection chosen by one common Rule-5 reference. -/
def localizedRerootRule5Descriptor
    (input : CertifiedLocalizedCIPInput)
    (commonReference : RS) (reading : input.LocalizedRerootRule5Reading) :
    List (List (OfficialSparseEntry (List Nat))) :=
  match commonReference with
  | .R => reading.commonR.descriptor
  | .S => reading.commonS.descriptor

/-- Compare the canonical reading list under one common Rule-5 reference. -/
def compareLocalizedRerootCompoundRule5Readings
    (input : CertifiedLocalizedCIPInput) (commonReference : RS) :
    List input.LocalizedRerootRule5Reading →
      List input.LocalizedRerootRule5Reading → Ordering :=
  List.compareLex
    (Ordering.byKey (input.localizedRerootRule5Descriptor commonReference)
      (OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority))

theorem compareLocalizedRerootCompoundRule5Readings_transCmp
    (input : CertifiedLocalizedCIPInput) (commonReference : RS) :
    Std.TransCmp (input.compareLocalizedRerootCompoundRule5Readings commonReference) := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  cases commonReference <;>
    unfold compareLocalizedRerootCompoundRule5Readings
      localizedRerootRule5Descriptor
      compareLocalizedCumulativeRule45Priority
      OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer
      OfficialRuleMajorKey.compareSparseEntry <;>
    infer_instance

/-- Total through-Rule-5 ordering comparator.  The common-R reading refines only a complete prior
tie. -/
def compareLocalizedRerootCompoundRule45Keys
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedRerootCompoundRule45Key →
      input.LocalizedRerootCompoundRule45Key → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.prior)
      input.compareLocalizedRerootCompoundRule4bcKeys)
    (Ordering.byKey (fun key => key.rule5Readings)
      (input.compareLocalizedRerootCompoundRule5Readings .R))

theorem compareLocalizedRerootCompoundRule45Keys_transCmp
    (input : CertifiedLocalizedCIPInput) :
    Std.TransCmp input.compareLocalizedRerootCompoundRule45Keys := by
  letI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
    input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
  letI : Std.TransCmp (input.compareLocalizedRerootCompoundRule5Readings .R) :=
    input.compareLocalizedRerootCompoundRule5Readings_transCmp .R
  unfold compareLocalizedRerootCompoundRule45Keys
  infer_instance

/-- Pairwise result retaining the enantiomorphic `±2` signal.  A prior Rules-4b/4c decision is
never marked pseudo. -/
def compareLocalizedRerootCompoundThroughRule5
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key) :
    ConstitutionalRule5Comparison :=
  let prior := input.compareLocalizedRerootCompoundRule4bcKeys
    left.prior right.prior
  if prior != Ordering.eq then { ordering := prior, pseudo := false }
  else
    let cmpR := input.compareLocalizedRerootCompoundRule5Readings
      .R left.rule5Readings right.rule5Readings
    let cmpS := input.compareLocalizedRerootCompoundRule5Readings
      .S left.rule5Readings right.rule5Readings
    match cmpR with
    | .lt => { ordering := .lt, pseudo := cmpS != .lt }
    | .gt => { ordering := .gt, pseudo := cmpS != .gt }
    | .eq => { ordering := .eq, pseudo := false }

/-- The result ordering is exactly the lawful transitive through-Rule-5 key comparator. -/
theorem compareLocalizedRerootCompoundThroughRule5_ordering
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
      input.compareLocalizedRerootCompoundRule45Keys left right := by
  unfold compareLocalizedRerootCompoundThroughRule5
    compareLocalizedRerootCompoundRule45Keys
  generalize priorEq : input.compareLocalizedRerootCompoundRule4bcKeys
    left.prior right.prior = prior
  cases prior with
  | lt => simp [compareLex, Ordering.byKey, priorEq]
  | gt => simp [compareLex, Ordering.byKey, priorEq]
  | eq =>
      generalize cmpREq : input.compareLocalizedRerootCompoundRule5Readings
        .R left.rule5Readings right.rule5Readings = cmpR
      generalize cmpSEq : input.compareLocalizedRerootCompoundRule5Readings
        .S left.rule5Readings right.rule5Readings = cmpS
      cases cmpR <;> cases cmpS <;>
        simp [compareLex, Ordering.byKey, priorEq, cmpREq]

/-- Independent pairwise witness packages both complete ligand derivations and the pure Rule-5
assembly equation. -/
def DeclarativeLocalizedRerootCompoundThroughRule5
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (result : ConstitutionalRule5Comparison) : Prop :=
  input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel leftCursor left ∧
    input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel rightCursor right ∧
    result = input.compareLocalizedRerootCompoundThroughRule5 left right

theorem compareLocalizedRerootCompoundThroughRule5_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel leftCursor = some left)
    (rightComputed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel rightCursor = some right) :
    input.DeclarativeLocalizedRerootCompoundThroughRule5 target view fuel
      leftCursor rightCursor left right
      (input.compareLocalizedRerootCompoundThroughRule5 left right) := by
  exact ⟨
    input.buildLocalizedRerootCompoundRule45Key?_sound
      target view fuel leftCursor left leftComputed,
    input.buildLocalizedRerootCompoundRule45Key?_sound
      target view fuel rightCursor right rightComputed,
    rfl⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
