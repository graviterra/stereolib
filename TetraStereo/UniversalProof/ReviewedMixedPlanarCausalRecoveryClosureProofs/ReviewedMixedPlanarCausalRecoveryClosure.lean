import TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofsLibrary.MixedPlanarCausalRecovery
import TetraStereo.OneCenter.AuthoritativeSingleWedgeSourcePerception

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.ReviewedMixedPlanarCausalRecoveryClosureProofs.ReviewedMixedPlanarCausalRecoveryClosure

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel




















































/-! ## 1. A generic two-element merge fact -/

/-- With the first channel absent, a two-element merge is never a typed conflict. -/
theorem foldStatus_none_cons_ne_conflict {Label : Type*} [DecidableEq Label]
    (output : Option Label) : foldStatus [none, output] ≠ .conflict := by
  cases output <;> simp [foldStatus, mergeChannel]

/-! ## 2. A plain diagram admits no drawing frame at any atom -/

/-- A centre whose incident records are all plain has no wedge record at all. -/
theorem wedgeRecords_incident_eq_nil_of_plain (diagram : DiagramConfiguration)
    (plain : ∀ bond ∈ diagram.bonds, bond.style = .plain) (center : Nat) :
    wedgeRecords (incidentRecords diagram center) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro bond member
  have original : bond ∈ diagram.bonds := (List.mem_filter.mp member).1
  simp [isWedge, plain bond original]

/-- If the actual source diagram is present and all of its bonds are plain, then no atom admits an
extracted drawing frame: the exactly-one-wedge clause of `AdmittedDiagram` is unsatisfiable. -/
theorem extract_none_of_plain_diagram (source : AuthoritativeChemicalInput)
    (diagram : DiagramConfiguration) (observed : source.diagram? = some diagram)
    (plain : ∀ bond ∈ diagram.bonds, bond.style = .plain)
    (center : Fin source.molecule.atomCount) : extract? source center = none := by
  rw [extract?_eq_none_iff_not_recognized]
  rintro ⟨diagram', positions, diagramEq, _positionsEq, admitted⟩
  have same : diagram' = diagram := Option.some.inj (diagramEq.symm.trans observed)
  rw [same] at admitted
  obtain ⟨_, _, _, _, _, _, _, _, _, count, _⟩ := admitted
  rw [wedgeRecords_incident_eq_nil_of_plain diagram plain center.val] at count
  exact Nat.zero_ne_one count

/-- The structural plain-diagram domain: the actual source diagram is present and carries only plain
bonds. This is an independently specified, non-vacuous domain on the source alone. -/
def HasPlainDiagram (source : AuthoritativeChemicalInput) : Prop :=
  ∃ diagram, source.diagram? = some diagram ∧ ∀ bond ∈ diagram.bonds, bond.style = .plain

/-- In the plain-diagram domain no atom admits an extracted drawing frame. -/
theorem hasPlainDiagram_extract?_eq_none {source : AuthoritativeChemicalInput}
    (plain : HasPlainDiagram source) (center : Fin source.molecule.atomCount) :
    extract? source center = none := by
  obtain ⟨diagram, observed, bonds⟩ := plain
  exact extract_none_of_plain_diagram source diagram observed bonds center

/-! ## 3. The semantic drawing-absence domain -/

/-- The weaker semantic domain: the actual source-native drawing evaluator is absent at every
occurrence, dependency view and rule fuel. `HasPlainDiagram` is a sufficient structural condition for
it, but this is the property the conflict argument actually consumes. -/
def DrawingAbsentEverywhere (source : AuthoritativeChemicalInput) : Prop :=
  ∀ (ruleFuel carrierFuel : Nat) (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target),
    occurrenceOrdinaryDescriptor? source target view ruleFuel = none



theorem occurrenceOrdinaryDescriptor?_eq_none_of_plain {source : AuthoritativeChemicalInput}
    (plain : HasPlainDiagram source) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    occurrenceOrdinaryDescriptor? source target view ruleFuel = none :=
  occurrenceOrdinaryDescriptor?_eq_none_of_recovered_extract_none source target view ruleFuel
    (fun center _ => hasPlainDiagram_extract?_eq_none plain center.1)

/-- `HasPlainDiagram` implies the semantic drawing-absence domain. -/
theorem hasPlainDiagram_drawingAbsent {source : AuthoritativeChemicalInput}
    (plain : HasPlainDiagram source) : DrawingAbsentEverywhere source :=
  fun ruleFuel carrierFuel target view =>
    occurrenceOrdinaryDescriptor?_eq_none_of_plain (carrierFuel := carrierFuel) plain target view ruleFuel

/-! ## 4. The NEW joint model over a source with uniformly absent drawing -/

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)

/-- The drawing channel of the NEW joint model is absent at its own joint view. -/
theorem planarJointDrawingDescriptor?_eq_none_of_drawingAbsent
    (absent : DrawingAbsentEverywhere source) (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    planarJointDrawingDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel target =
      none := by
  unfold planarJointDrawingDescriptor?
  exact absent ruleFuel carrierFuel target
    (planarJointView molecule source agreement writtenExact carrierFuel ruleFuel target)

/-- In the drawing-absence domain the NEW joint status at any target is never a typed conflict: the
merge of an absent drawing channel with any parser channel cannot realise two unequal successes. -/
theorem planarJointStatus_ne_conflict_of_drawingAbsent
    (absent : DrawingAbsentEverywhere source) (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel target ≠
      .conflict := by
  rw [planarJointStatus_eq_fold]
  rw [planarJointDrawingDescriptor?_eq_none_of_drawingAbsent molecule source agreement writtenExact
    absent carrierFuel ruleFuel target]
  exact foldStatus_none_cons_ne_conflict _

/-- **Generic source-wide conflict guard.** In the drawing-absence domain the NEW joint model's
source-wide candidate conflict guard is empty at every carrier and rule fuel. -/
theorem planarGlobalConflictFree_of_drawingAbsent
    (absent : DrawingAbsentEverywhere source) (carrierFuel ruleFuel : Nat) :
    PlanarGlobalConflictFree molecule source agreement writtenExact carrierFuel ruleFuel := by
  apply (planarGlobalConflictIssues_eq_nil_iff molecule source agreement writtenExact carrierFuel
    ruleFuel).mpr
  intro center _
  exact planarJointStatus_ne_conflict_of_drawingAbsent molecule source agreement writtenExact
    absent carrierFuel ruleFuel (source.aromaticCanonicalFinalOccurrence carrierFuel center)



theorem planarJointAuditObligation_of_partial_of_drawingAbsent
    (absent : DrawingAbsentEverywhere source) (carrierFuel ruleFuel : Nat)
    (partialAudit : PlanarJointPartialAudit molecule source agreement writtenExact carrierFuel ruleFuel) :
    PlanarJointAuditObligation molecule source agreement writtenExact carrierFuel ruleFuel :=
  ⟨planarGlobalConflictFree_of_drawingAbsent molecule source agreement writtenExact absent carrierFuel
    ruleFuel, partialAudit⟩

/-- Structural specialisation: over any plain-diagram source the source-wide conflict guard holds at
every carrier and rule fuel. -/
theorem planarGlobalConflictFree_of_plain (plain : HasPlainDiagram source) (carrierFuel ruleFuel : Nat) :
    PlanarGlobalConflictFree molecule source agreement writtenExact carrierFuel ruleFuel :=
  planarGlobalConflictFree_of_drawingAbsent molecule source agreement writtenExact
    (hasPlainDiagram_drawingAbsent plain) carrierFuel ruleFuel



theorem planarJointAuditObligation_of_partial_of_plain (plain : HasPlainDiagram source)
    (carrierFuel ruleFuel : Nat)
    (partialAudit : PlanarJointPartialAudit molecule source agreement writtenExact carrierFuel ruleFuel) :
    PlanarJointAuditObligation molecule source agreement writtenExact carrierFuel ruleFuel :=
  ⟨planarGlobalConflictFree_of_plain molecule source agreement writtenExact plain carrierFuel ruleFuel,
    partialAudit⟩

end TetraStereo.UniversalProof.ReviewedMixedPlanarCausalRecoveryClosureProofs.ReviewedMixedPlanarCausalRecoveryClosure
