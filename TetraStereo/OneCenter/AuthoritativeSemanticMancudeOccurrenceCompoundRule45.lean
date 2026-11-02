import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule4bc

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical compound Rule 5

After the complete compound Rules-4b/4c key ties, Rule 5 reads the same hierarchy with common R
and S references.  This module constructs both readings for every normative Rule-4b alternative
and proves the executable construction against an independent inductive semantics.
-/

open CertifiedLocalizedCIPInput

/-- Cumulative Rule-5 stage belonging to a ligand's Rule-4b reference and a common reference. -/
def aromaticCanonicalRule5StageFor
    (rule4bReference : Option RS) (commonReference : RS) :
    LocalizedCumulativeRule45Stage :=
  match rule4bReference with
  | none => .rule5NoRule4bReference commonReference
  | some reference => .rule5 reference commonReference

/-- One Rules-4b/4c alternative plus its complete common-R and common-S readings. -/
structure AromaticCanonicalRerootRule5Reading
    (source : AuthoritativeChemicalInput) where
  prior : source.AromaticCanonicalRerootRule4bcReading
  commonR : source.AromaticCanonicalCumulativeRule45Key
  commonS : source.AromaticCanonicalCumulativeRule45Key

noncomputable def buildAromaticCanonicalRerootRule5Reading?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading) :
    Option source.AromaticCanonicalRerootRule5Reading := do
  let commonR ← source.buildAromaticCanonicalCumulativeRule45Key?
    (aromaticCanonicalRule5StageFor prior.reference? .R) target view fuel cursor
  let commonS ← source.buildAromaticCanonicalCumulativeRule45Key?
    (aromaticCanonicalRule5StageFor prior.reference? .S) target view fuel cursor
  some { prior := prior, commonR := commonR, commonS := commonS }

/-- Independent meaning of one successful pair of common-reference readings. -/
def DeclarativeAromaticCanonicalRerootRule5Reading
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading) : Prop :=
  reading.prior = prior ∧
    source.DeclarativeAromaticCanonicalCumulativeRule45Key
      (aromaticCanonicalRule5StageFor prior.reference? .R)
      target view fuel cursor reading.commonR ∧
    source.DeclarativeAromaticCanonicalCumulativeRule45Key
      (aromaticCanonicalRule5StageFor prior.reference? .S)
      target view fuel cursor reading.commonS

theorem buildAromaticCanonicalRerootRule5Reading?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (computed : source.buildAromaticCanonicalRerootRule5Reading?
      target view fuel cursor prior = some reading) :
    source.DeclarativeAromaticCanonicalRerootRule5Reading
      target view fuel cursor prior reading := by
  unfold buildAromaticCanonicalRerootRule5Reading? at computed
  cases commonRComputed : source.buildAromaticCanonicalCumulativeRule45Key?
      (aromaticCanonicalRule5StageFor prior.reference? .R)
      target view fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      cases commonSComputed : source.buildAromaticCanonicalCumulativeRule45Key?
          (aromaticCanonicalRule5StageFor prior.reference? .S)
          target view fuel cursor with
      | none => simp [commonRComputed, commonSComputed] at computed
      | some commonS =>
          simp [commonRComputed, commonSComputed] at computed
          subst reading
          exact ⟨rfl,
            source.buildAromaticCanonicalCumulativeRule45Key?_sound
              (aromaticCanonicalRule5StageFor prior.reference? .R)
              target view fuel cursor commonR commonRComputed,
            source.buildAromaticCanonicalCumulativeRule45Key?_sound
              (aromaticCanonicalRule5StageFor prior.reference? .S)
              target view fuel cursor commonS commonSComputed⟩

inductive DeclarativeAromaticCanonicalRerootRule5Readings
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    List source.AromaticCanonicalRerootRule4bcReading →
      List source.AromaticCanonicalRerootRule5Reading → Prop
  | nil : DeclarativeAromaticCanonicalRerootRule5Readings
      source target view fuel cursor [] []
  | cons {prior priors reading readings}
      (head : source.DeclarativeAromaticCanonicalRerootRule5Reading
        target view fuel cursor prior reading)
      (tail : source.DeclarativeAromaticCanonicalRerootRule5Readings
        target view fuel cursor priors readings) :
      DeclarativeAromaticCanonicalRerootRule5Readings
        source target view fuel cursor (prior :: priors) (reading :: readings)

noncomputable def buildAromaticCanonicalRerootRule5Readings?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    List source.AromaticCanonicalRerootRule4bcReading →
      Option (List source.AromaticCanonicalRerootRule5Reading)
  | [] => some []
  | prior :: priors => do
      let reading ← source.buildAromaticCanonicalRerootRule5Reading?
        target view fuel cursor prior
      let readings ← source.buildAromaticCanonicalRerootRule5Readings?
        target view fuel cursor priors
      some (reading :: readings)

theorem buildAromaticCanonicalRerootRule5Readings?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ priors readings,
      source.buildAromaticCanonicalRerootRule5Readings?
        target view fuel cursor priors = some readings →
      source.DeclarativeAromaticCanonicalRerootRule5Readings
        target view fuel cursor priors readings
  | [], readings, computed => by
      simp [buildAromaticCanonicalRerootRule5Readings?] at computed
      subst readings
      exact DeclarativeAromaticCanonicalRerootRule5Readings.nil
  | prior :: priors, readings, computed => by
      unfold buildAromaticCanonicalRerootRule5Readings? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule5Reading?
          target view fuel cursor prior with
      | none => simp [headComputed] at computed
      | some reading =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule5Readings?
              target view fuel cursor priors with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              exact DeclarativeAromaticCanonicalRerootRule5Readings.cons
                (source.buildAromaticCanonicalRerootRule5Reading?_sound
                  target view fuel cursor prior reading headComputed)
                (source.buildAromaticCanonicalRerootRule5Readings?_sound
                  target view fuel cursor priors tail tailComputed)

/-- Complete source-canonical key through Rule 5. -/
structure AromaticCanonicalRerootCompoundRule45Key
    (source : AuthoritativeChemicalInput) where
  prior : source.AromaticCanonicalRerootCompoundRule4bcKey
  rule5Readings : List source.AromaticCanonicalRerootRule5Reading

noncomputable def buildAromaticCanonicalRerootCompoundRule45Key?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option source.AromaticCanonicalRerootCompoundRule45Key := do
  let prior ← source.buildAromaticCanonicalRerootCompoundRule4bcKey?
    target view fuel cursor
  let readings ← source.buildAromaticCanonicalRerootRule5Readings?
    target view fuel cursor prior.readings
  some { prior := prior, rule5Readings := readings }

def DeclarativeAromaticCanonicalRerootCompoundRule45Key
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key) : Prop :=
  source.DeclarativeAromaticCanonicalRerootCompoundRule4bcKey
      target view fuel cursor key.prior ∧
    source.DeclarativeAromaticCanonicalRerootRule5Readings
      target view fuel cursor key.prior.readings key.rule5Readings

theorem buildAromaticCanonicalRerootCompoundRule45Key?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45Key?
      target view fuel cursor = some key) :
    source.DeclarativeAromaticCanonicalRerootCompoundRule45Key
      target view fuel cursor key := by
  unfold buildAromaticCanonicalRerootCompoundRule45Key? at computed
  cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKey?
      target view fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      cases readingsComputed : source.buildAromaticCanonicalRerootRule5Readings?
          target view fuel cursor prior.readings with
      | none => simp [priorComputed, readingsComputed] at computed
      | some readings =>
          simp [priorComputed, readingsComputed] at computed
          subst key
          exact ⟨
            source.buildAromaticCanonicalRerootCompoundRule4bcKey?_sound
              target view fuel cursor prior priorComputed,
            source.buildAromaticCanonicalRerootRule5Readings?_sound
              target view fuel cursor prior.readings readings readingsComputed⟩

/-- Descriptor projection selected by a common Rule-5 reference. -/
def aromaticCanonicalRerootRule5Descriptor
    (source : AuthoritativeChemicalInput)
    (commonReference : RS) (reading : source.AromaticCanonicalRerootRule5Reading) :
    List (List (OfficialSparseEntry (List Nat))) :=
  match commonReference with
  | .R => reading.commonR.descriptor
  | .S => reading.commonS.descriptor

def compareAromaticCanonicalRerootCompoundRule5Readings
    (source : AuthoritativeChemicalInput) (commonReference : RS) :
    List source.AromaticCanonicalRerootRule5Reading →
      List source.AromaticCanonicalRerootRule5Reading → Ordering :=
  List.compareLex
    (Ordering.byKey (source.aromaticCanonicalRerootRule5Descriptor commonReference)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))

theorem compareAromaticCanonicalRerootCompoundRule5Readings_transCmp
    (source : AuthoritativeChemicalInput) (commonReference : RS) :
    Std.TransCmp
      (source.compareAromaticCanonicalRerootCompoundRule5Readings commonReference) := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  cases commonReference <;>
    unfold compareAromaticCanonicalRerootCompoundRule5Readings
      aromaticCanonicalRerootRule5Descriptor
      compareLocalizedCumulativeRule45Priority
      OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer
      OfficialRuleMajorKey.compareSparseEntry <;>
    infer_instance

/-- Total lawful through-Rule-5 ordering; common R refines only a complete prior tie. -/
def compareAromaticCanonicalRerootCompoundRule45Keys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalRerootCompoundRule45Key →
      source.AromaticCanonicalRerootCompoundRule45Key → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.prior)
      source.compareAromaticCanonicalRerootCompoundRule4bcKeys)
    (Ordering.byKey (fun key => key.rule5Readings)
      (source.compareAromaticCanonicalRerootCompoundRule5Readings .R))

theorem compareAromaticCanonicalRerootCompoundRule45Keys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalRerootCompoundRule45Keys := by
  letI : Std.TransCmp source.compareAromaticCanonicalRerootCompoundRule4bcKeys :=
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys_transCmp
  letI : Std.TransCmp
      (source.compareAromaticCanonicalRerootCompoundRule5Readings .R) :=
    source.compareAromaticCanonicalRerootCompoundRule5Readings_transCmp .R
  unfold compareAromaticCanonicalRerootCompoundRule45Keys
  infer_instance

/-- Pairwise result retaining the enantiomorphic Rule-5 pseudoasymmetry signal. -/
def compareAromaticCanonicalRerootCompoundThroughRule5
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key) :
    ConstitutionalRule5Comparison :=
  let prior := source.compareAromaticCanonicalRerootCompoundRule4bcKeys
    left.prior right.prior
  if prior != Ordering.eq then { ordering := prior, pseudo := false }
  else
    let cmpR := source.compareAromaticCanonicalRerootCompoundRule5Readings
      .R left.rule5Readings right.rule5Readings
    let cmpS := source.compareAromaticCanonicalRerootCompoundRule5Readings
      .S left.rule5Readings right.rule5Readings
    match cmpR with
    | .lt => { ordering := .lt, pseudo := cmpS != .lt }
    | .gt => { ordering := .gt, pseudo := cmpS != .gt }
    | .eq => { ordering := .eq, pseudo := false }

theorem compareAromaticCanonicalRerootCompoundThroughRule5_ordering
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key) :
    (source.compareAromaticCanonicalRerootCompoundThroughRule5 left right).ordering =
      source.compareAromaticCanonicalRerootCompoundRule45Keys left right := by
  unfold compareAromaticCanonicalRerootCompoundThroughRule5
    compareAromaticCanonicalRerootCompoundRule45Keys
  generalize priorEq : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
    left.prior right.prior = prior
  cases prior with
  | lt => simp [compareLex, Ordering.byKey, priorEq]
  | gt => simp [compareLex, Ordering.byKey, priorEq]
  | eq =>
      generalize cmpREq : source.compareAromaticCanonicalRerootCompoundRule5Readings
        .R left.rule5Readings right.rule5Readings = cmpR
      generalize cmpSEq : source.compareAromaticCanonicalRerootCompoundRule5Readings
        .S left.rule5Readings right.rule5Readings = cmpS
      cases cmpR <;> cases cmpS <;>
        simp [compareLex, Ordering.byKey, priorEq, cmpREq]

/-- Independent pairwise witness for both ligand derivations and pure Rule-5 assembly. -/
def DeclarativeAromaticCanonicalRerootCompoundThroughRule5
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (leftCursor rightCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (result : ConstitutionalRule5Comparison) : Prop :=
  source.DeclarativeAromaticCanonicalRerootCompoundRule45Key
      target view fuel leftCursor left ∧
    source.DeclarativeAromaticCanonicalRerootCompoundRule45Key
      target view fuel rightCursor right ∧
    result = source.compareAromaticCanonicalRerootCompoundThroughRule5 left right

theorem compareAromaticCanonicalRerootCompoundThroughRule5_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (leftCursor rightCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (leftComputed : source.buildAromaticCanonicalRerootCompoundRule45Key?
      target view fuel leftCursor = some left)
    (rightComputed : source.buildAromaticCanonicalRerootCompoundRule45Key?
      target view fuel rightCursor = some right) :
    source.DeclarativeAromaticCanonicalRerootCompoundThroughRule5
      target view fuel leftCursor rightCursor left right
        (source.compareAromaticCanonicalRerootCompoundThroughRule5 left right) := by
  exact ⟨
    source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
      target view fuel leftCursor left leftComputed,
    source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
      target view fuel rightCursor right rightComputed,
    rfl⟩

/-- The complete through-Rule-5 construction contains no Kekule selection parameter. -/
theorem buildAromaticCanonicalRerootCompoundRule45Key_source_fixed
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel cursor =
      source.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel cursor :=
  rfl

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
