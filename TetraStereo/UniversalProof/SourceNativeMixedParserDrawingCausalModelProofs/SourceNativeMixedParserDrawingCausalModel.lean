import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceDescriptor
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
import TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel


















































universe u



section FoldArithmetic

variable {Label : Type u} [DecidableEq Label]


theorem foldStatus_pair (x y : Option Label) :
    foldStatus [x, y] = mergeChannel (mergeChannel .unassigned x) y := rfl

theorem foldStatus_pair_none_none :
    foldStatus ([none, none] : List (Option Label)) = .unassigned := rfl

theorem foldStatus_pair_none_some (a : Label) :
    foldStatus ([none, some a] : List (Option Label)) = .assigned a := rfl

theorem foldStatus_pair_some_none (a : Label) :
    foldStatus ([some a, none] : List (Option Label)) = .assigned a := rfl

theorem foldStatus_pair_some_some (a b : Label) :
    foldStatus ([some a, some b] : List (Option Label)) =
      (if b = a then .assigned a else .conflict) := rfl

theorem foldStatus_pair_some_same (a : Label) :
    foldStatus ([some a, some a] : List (Option Label)) = .assigned a := by
  rw [foldStatus_pair_some_some, if_pos rfl]

/-- Two successes with different labels — including an upper/lower-case mismatch — conflict. -/
theorem foldStatus_pair_some_some_diff (a b : Label) (different : a ≠ b) :
    foldStatus ([some a, some b] : List (Option Label)) = .conflict := by
  rw [foldStatus_pair_some_some, if_neg (fun same => different same.symm)]

end FoldArithmetic

/-! ## 2. Drawing absence from a coordinate-free diagram -/

section Extraction

variable (source : AuthoritativeChemicalInput)

/-- A diagram with no positions has no extractable frame at any center. -/
theorem extract?_eq_none_of_atomPositions_none (diagram : DiagramConfiguration)
    (observed : source.diagram? = some diagram) (noPositions : diagram.atomPositions? = none)
    (center : Fin source.molecule.atomCount) :
    extract? source center = none := by
  simp [extract?, observed, noPositions]

/-- If no center admits an extracted frame the drawing priority evidence is absent. -/
theorem occurrenceOrdinaryPriorityEvidence?_eq_none_of_extraction_none
    (noExtraction : ∀ center, extract? source center = none) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    occurrenceOrdinaryPriorityEvidence? source target view ruleFuel = none := by
  unfold occurrenceOrdinaryPriorityEvidence?
  cases center : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp
  | some c => simp [noExtraction c.1]

/-- If no center admits an extracted frame the drawing evaluator is absent. -/
theorem occurrenceOrdinaryDescriptor?_eq_none_of_extraction_none
    (noExtraction : ∀ center, extract? source center = none) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    occurrenceOrdinaryDescriptor? source target view ruleFuel = none := by
  unfold occurrenceOrdinaryDescriptor?
  rw [occurrenceOrdinaryPriorityEvidence?_eq_none_of_extraction_none source noExtraction
    target view ruleFuel]
  rfl

end Extraction

/-! ## 3. The two actual channels over one source / target / view / fuels -/

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)

/-- The two actual channel results, in a fixed order, read at the *same* restricted view. -/
noncomputable def mixedChannelOutputs {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    List (Option AromaticCanonicalAuxiliaryLabel) :=
  [ occurrenceOrdinaryDescriptor? source target view ruleFuel,
    constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel ]

/-- The canonical execution record of the two actual channel outputs. -/
theorem mixedChannelOutputs_eq {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    mixedChannelOutputs molecule source agreement writtenExact target view ruleFuel =
      [ occurrenceOrdinaryDescriptor? source target view ruleFuel,
        constitutionParserRichDescriptor? molecule source agreement writtenExact target
          view ruleFuel ] := rfl


noncomputable def mixedChannelStatus {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    ChannelStatus AromaticCanonicalAuxiliaryLabel :=
  foldStatus (mixedChannelOutputs molecule source agreement writtenExact target view ruleFuel)

/-- The joint optional evaluator: `assigned → some label`, all-absent and conflict `→ none`. -/
noncomputable def mixedJointDescriptor? {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option AromaticCanonicalAuxiliaryLabel :=
  match mixedChannelStatus molecule source agreement writtenExact target view ruleFuel with
  | .assigned label => some label
  | .unassigned => none
  | .conflict => none

/-- **Exact assigned outcome.** The joint evaluator emits exactly the merged assignment. -/
theorem mixedJointDescriptor?_eq_some_iff_status {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) :
    mixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel = some label ↔
      mixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
        .assigned label := by
  unfold mixedJointDescriptor?
  cases h : mixedChannelStatus molecule source agreement writtenExact target view ruleFuel <;>
    simp_all

/-- **Exact unassigned outcome.** The joint evaluator emits `none` exactly on all-absent or
conflict; conflict is a distinct recomputable status, not a chemical nonstereogenicity claim. -/
theorem mixedJointDescriptor?_eq_none_iff_status {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    mixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel = none ↔
      (mixedChannelStatus molecule source agreement writtenExact target view ruleFuel = .unassigned ∨
       mixedChannelStatus molecule source agreement writtenExact target view ruleFuel = .conflict) := by
  unfold mixedJointDescriptor?
  cases h : mixedChannelStatus molecule source agreement writtenExact target view ruleFuel <;>
    simp_all

/-! ## 4. Independent local meaning of each successful channel -/

/-- Each successful channel retains its **own** independent source meaning; nothing is transferred
between the drawing and parser channels. -/
noncomputable def MixedAssignedMeaning {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) : Prop :=
  (occurrenceOrdinaryDescriptor? source target view ruleFuel = some label →
    CanonicalOccurrenceOrdinaryDescriptor source target view ruleFuel label) ∧
    (constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel =
        some label →
      CanonicalConstitutionParserRichDescriptor molecule source agreement writtenExact target
        view ruleFuel label)

theorem mixedAssignedMeaning_holds {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) :
    MixedAssignedMeaning molecule source agreement writtenExact target view ruleFuel label :=
  ⟨fun computed =>
      (occurrenceOrdinaryDescriptor?_eq_some_iff_canonical source target view ruleFuel label).mp
        computed,
   fun computed =>
      (constitutionParserRichDescriptor?_eq_some_iff_canonical molecule source agreement writtenExact
        target view ruleFuel label).mp computed⟩

/-- A named joint assignment: the merged status assigns `label` and each successful channel keeps
its own independent source meaning. -/
noncomputable def MixedJointDescriptor {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) : Prop :=
  mixedChannelStatus molecule source agreement writtenExact target view ruleFuel = .assigned label ∧
    MixedAssignedMeaning molecule source agreement writtenExact target view ruleFuel label

theorem mixedJointDescriptor_iff_status {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) :
    MixedJointDescriptor molecule source agreement writtenExact target view ruleFuel label ↔
      mixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
        .assigned label := by
  constructor
  · intro named
    unfold MixedJointDescriptor at named
    exact named.1
  · intro assigned
    unfold MixedJointDescriptor
    exact ⟨assigned,
      mixedAssignedMeaning_holds molecule source agreement writtenExact target view ruleFuel label⟩

/-- Canonical joint evaluator exactness in terms of the named joint assignment. -/
theorem mixedJointDescriptor?_eq_some_iff_descriptor {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) :
    mixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel = some label ↔
      MixedJointDescriptor molecule source agreement writtenExact target view ruleFuel label :=
  (mixedJointDescriptor?_eq_some_iff_status molecule source agreement writtenExact target view ruleFuel
      label).trans
    (mixedJointDescriptor_iff_status molecule source agreement writtenExact target view ruleFuel
      label).symm

/-! ## 5. The separate recomputable conflict diagnostic -/

/-- The actual conflict status, retained separately and recomputable from the two actual channels.
This is a typed disagreement of two actual channels; it is **not** a claim of chemical
nonstereogenicity and does not authorize adoption. -/
noncomputable def MixedConflictDiagnostic {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) : Prop :=
  mixedChannelStatus molecule source agreement writtenExact target view ruleFuel = .conflict

/-- A conflict diagnostic exposes two actual successful channels carrying different labels. -/
theorem mixedConflictDiagnostic_witness {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (conflict : MixedConflictDiagnostic molecule source agreement writtenExact target view ruleFuel) :
    ∃ first ∈ mixedChannelOutputs molecule source agreement writtenExact target view ruleFuel,
      ∃ second ∈ mixedChannelOutputs molecule source agreement writtenExact target view ruleFuel,
        ∃ firstLabel secondLabel,
          first = some firstLabel ∧ second = some secondLabel ∧ firstLabel ≠ secondLabel := by
  have classified :=
    foldStatus_classifies (mixedChannelOutputs molecule source agreement writtenExact target view
      ruleFuel)
  unfold MixedConflictDiagnostic at conflict
  unfold mixedChannelStatus at conflict
  rw [conflict] at classified
  exact classified

/-- A conflict diagnostic is nonassignment in the joint evaluator. -/
theorem mixedConflictDiagnostic_nonassignment {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (conflict : MixedConflictDiagnostic molecule source agreement writtenExact target view ruleFuel) :
    mixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel = none := by
  rw [mixedJointDescriptor?_eq_none_iff_status]
  exact Or.inr (by simpa [MixedConflictDiagnostic] using conflict)

/-- **Generic two-channel disagreement.** Two actual successes with different labels merge to a
typed conflict, including an upper/lower-case `chiral`/`pseudoasymmetric` mismatch. -/
theorem mixedChannelStatus_conflict_of_actual_disagreement {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : occurrenceOrdinaryDescriptor? source target view ruleFuel = some leftLabel)
    (parser : constitutionParserRichDescriptor? molecule source agreement writtenExact target view
      ruleFuel = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    mixedChannelStatus molecule source agreement writtenExact target view ruleFuel = .conflict := by
  unfold mixedChannelStatus mixedChannelOutputs
  rw [drawing, parser]
  exact foldStatus_pair_some_some_diff leftLabel rightLabel different

/-- Generic two-channel disagreement yields local nonassignment at the supplied target and view. -/
theorem mixedJointDescriptor?_eq_none_of_actual_disagreement {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : occurrenceOrdinaryDescriptor? source target view ruleFuel = some leftLabel)
    (parser : constitutionParserRichDescriptor? molecule source agreement writtenExact target view
      ruleFuel = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    mixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel = none := by
  have conflict := mixedChannelStatus_conflict_of_actual_disagreement molecule source agreement
    writtenExact target view ruleFuel leftLabel rightLabel drawing parser different
  rw [mixedJointDescriptor?_eq_none_iff_status]
  exact Or.inr conflict






noncomputable def MixedChannelsResolved {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) : Prop :=
  occurrenceOrdinaryDescriptor? source target view ruleFuel ≠ none ∧
    constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel ≠
      none

/-- The local merge maps "one channel absent, the other successful" to `assigned`. This describes
the local evaluator's behavior. It establishes neither `MixedChannelsResolved` at that target nor
source-wide annotation coverage; the latter remains a separate transaction obligation. -/
theorem mixedChannelStatus_assigned_of_absent_and_success {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel)
    (drawingAbsent : occurrenceOrdinaryDescriptor? source target view ruleFuel = none)
    (parserSuccess : constitutionParserRichDescriptor? molecule source agreement writtenExact target
      view ruleFuel = some label) :
    mixedChannelStatus molecule source agreement writtenExact target view ruleFuel = .assigned label := by
  unfold mixedChannelStatus mixedChannelOutputs
  rw [drawingAbsent, parserSuccess]
  exact foldStatus_pair_none_some label

theorem mixedChannelStatus_assigned_of_success_and_absent {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel)
    (drawingSuccess : occurrenceOrdinaryDescriptor? source target view ruleFuel = some label)
    (parserAbsent : constitutionParserRichDescriptor? molecule source agreement writtenExact target
      view ruleFuel = none) :
    mixedChannelStatus molecule source agreement writtenExact target view ruleFuel = .assigned label := by
  unfold mixedChannelStatus mixedChannelOutputs
  rw [drawingSuccess, parserAbsent]
  exact foldStatus_pair_some_none label

/-! ## 7. The joint causal model and its own scheduler -/

/-- The joint declarative outcome. `none` is exactly all-absent or conflict; `some label` is the
named joint assignment with each successful channel's own meaning. -/
noncomputable def MixedOutcome {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  match outcome with
  | none =>
      mixedChannelStatus molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = .unassigned ∨
      mixedChannelStatus molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = .conflict
  | some label =>
      MixedJointDescriptor molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel label

/-- The declarative joint outcome is exactly the joint evaluator's own output. -/
theorem mixedOutcome_iff {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) :
    MixedOutcome molecule source agreement writtenExact ruleFuel state target outcome ↔
      mixedJointDescriptor? molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = outcome := by
  cases outcome with
  | none =>
      exact (mixedJointDescriptor?_eq_none_iff_status molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel).symm
  | some label =>
      exact (mixedJointDescriptor?_eq_some_iff_descriptor molecule source agreement writtenExact
        target (source.aromaticCanonicalDependencyView state target) ruleFuel label).symm

/-- The joint rule semantics: declarative outcome and executable evaluator agree by construction. -/
noncomputable def mixedAuxiliarySemantics (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalRuleSemantics carrierFuel where
  DeclarativeDerivation := MixedOutcome molecule source agreement writtenExact ruleFuel
  executableRule := fun target view =>
    mixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel
  derivation_executable_iff := mixedOutcome_iff molecule source agreement writtenExact ruleFuel

/-- The finite source occurrence system of the joint semantics has a unique `CIPModel`. -/
theorem existsUnique_mixedCIPModel (carrierFuel ruleFuel : Nat) :
    ∃! state, (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
        state :=
  source.existsUnique_aromaticCanonicalCIPModel
    (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)

/-- The internally scheduled joint state, produced by the source occurrence scheduler. -/
noncomputable def mixedScheduledState (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  DeclarativeCIP.OccurrenceScheduler.decode
    (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (DeclarativeCIP.OccurrenceScheduler.closure
      (source.aromaticCanonicalOccurrenceSystem
        (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
      (@source.AromaticCanonicalDepthDependency carrierFuel))

theorem mixedScheduledState_cipModel (carrierFuel ruleFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
      (mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel) :=
  source.aromaticCanonicalSchedulerClosure_cipModel
    (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)

/-- Under any joint model the state is the joint evaluator at every original occurrence. -/
theorem mixedModel_evaluates {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
        state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    mixedJointDescriptor? molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = state target := by
  have fixed := (source.aromaticCanonicalOccurrenceSystem
    (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).cipModel_iff_executableStateStep_fixed
      (source.aromaticCanonicalDerivationStepCorrespondence
        (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
      state |>.mp model
  exact congrFun fixed target

/-- The joint model is unique: any model equals the internally scheduled state. -/
theorem mixedModel_unique (carrierFuel ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
        state) :
    state = mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel := by
  obtain ⟨canonical, _canonicalModel, unique⟩ :=
    existsUnique_mixedCIPModel molecule source agreement writtenExact carrierFuel ruleFuel
  exact (unique state model).trans
    (unique _ (mixedScheduledState_cipModel molecule source agreement writtenExact carrierFuel
      ruleFuel)).symm

/-- Output soundness: an assigned joint model result carries the named joint assignment. -/
theorem mixedModel_output_sound {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
        state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (label : AromaticCanonicalAuxiliaryLabel) (assigned : state target = some label) :
    MixedJointDescriptor molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel label :=
  (mixedJointDescriptor?_eq_some_iff_descriptor molecule source agreement writtenExact target
    (source.aromaticCanonicalDependencyView state target) ruleFuel label).mp
    ((mixedModel_evaluates molecule source agreement writtenExact state model target).trans assigned)

/-- **Independent conflict diagnosis under the joint model.** At any original occurrence (in
particular a final center), disagreement between two actual successful channels implies
nonassignment and a recomputable typed conflict. No converse from nonassignment is asserted. The diagnosis is computed from
the two actual evaluators, not from the model assumption. -/
theorem mixedModel_conflict_nonassignment {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
        state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : occurrenceOrdinaryDescriptor? source target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = some leftLabel)
    (parser : constitutionParserRichDescriptor? molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    state target = none ∧
      MixedConflictDiagnostic molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel := by
  have evaluates := mixedModel_evaluates molecule source agreement writtenExact state model target
  have conflict := mixedChannelStatus_conflict_of_actual_disagreement molecule source agreement
    writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel leftLabel
    rightLabel drawing parser different
  refine ⟨?_, ?_⟩
  · rw [← evaluates, mixedJointDescriptor?_eq_none_iff_status]
    exact Or.inr conflict
  · show mixedChannelStatus molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = .conflict
    exact conflict

/-- Specialisation to a final center: the joint model diagnoses an actual two-channel disagreement
at `source.aromaticCanonicalFinalOccurrence carrierFuel center` independently. -/
theorem mixedModel_finalCenter_conflict_nonassignment {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
        state)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : occurrenceOrdinaryDescriptor? source
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)
      (source.aromaticCanonicalDependencyView state
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel = some leftLabel)
    (parser : constitutionParserRichDescriptor? molecule source agreement writtenExact
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)
      (source.aromaticCanonicalDependencyView state
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    state (source.aromaticCanonicalFinalOccurrence carrierFuel center) = none ∧
      MixedConflictDiagnostic molecule source agreement writtenExact
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel :=
  mixedModel_conflict_nonassignment molecule source agreement writtenExact state model
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) leftLabel rightLabel drawing parser
    different

end TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
