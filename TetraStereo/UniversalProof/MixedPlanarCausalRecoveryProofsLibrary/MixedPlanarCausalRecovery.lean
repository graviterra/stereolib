import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceDescriptor
import TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
import TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence
import TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
import TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence
open TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
open TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit






















































































/-! ## 1. Drawing absence from a genuinely recovered, non-extractable centre -/

section Extraction

variable (source : AuthoritativeChemicalInput)





theorem occurrenceOrdinaryPriorityEvidence?_eq_none_of_recovered_extract_none
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (noExtract : ∀ center, source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center →
      extract? source center.1 = none) :
    occurrenceOrdinaryPriorityEvidence? source target view ruleFuel = none := by
  unfold occurrenceOrdinaryPriorityEvidence?
  cases observed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp
  | some center => simp [noExtract center observed]

/-- If the genuinely recovered occurrence centre admits no extracted drawing frame, the drawing
evaluator is absent. -/
theorem occurrenceOrdinaryDescriptor?_eq_none_of_recovered_extract_none
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (noExtract : ∀ center, source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center →
      extract? source center.1 = none) :
    occurrenceOrdinaryDescriptor? source target view ruleFuel = none := by
  unfold occurrenceOrdinaryDescriptor?
  rw [occurrenceOrdinaryPriorityEvidence?_eq_none_of_recovered_extract_none source target view
    ruleFuel noExtract]
  rfl

end Extraction

/-! ## 2. The two actual channels over one source / target / view / fuels -/

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)




noncomputable def planarMixedChannelOutputs {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    List (Option AromaticCanonicalAuxiliaryLabel) :=
  [ occurrenceOrdinaryDescriptor? source target view ruleFuel,
    planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target view
      ruleFuel ]

/-- The canonical execution record of the two actual channel outputs. -/
theorem planarMixedChannelOutputs_eq {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    planarMixedChannelOutputs molecule source agreement writtenExact target view ruleFuel =
      [ occurrenceOrdinaryDescriptor? source target view ruleFuel,
        planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target view
          ruleFuel ] := rfl


noncomputable def planarMixedChannelStatus {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    ChannelStatus AromaticCanonicalAuxiliaryLabel :=
  foldStatus (planarMixedChannelOutputs molecule source agreement writtenExact target view ruleFuel)

/-- The NEW joint optional evaluator: `assigned → some label`, all-absent and conflict `→ none`. -/
noncomputable def planarMixedJointDescriptor? {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    Option AromaticCanonicalAuxiliaryLabel :=
  match planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel with
  | .assigned label => some label
  | .unassigned => none
  | .conflict => none

/-- **Exact assigned outcome.** The joint evaluator emits exactly the merged assignment. -/
theorem planarMixedJointDescriptor?_eq_some_iff_status {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) :
    planarMixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel =
        some label ↔
      planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
        .assigned label := by
  unfold planarMixedJointDescriptor?
  cases h : planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel <;>
    simp_all

/-- **Exact unassigned outcome.** The joint evaluator emits `none` exactly on all-absent or
conflict; conflict is a distinct recomputable status, not a chemical nonstereogenicity claim. -/
theorem planarMixedJointDescriptor?_eq_none_iff_status {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    planarMixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel = none ↔
      (planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
          .unassigned ∨
       planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
          .conflict) := by
  unfold planarMixedJointDescriptor?
  cases h : planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel <;>
    simp_all

/-! ## 3. Independent local meaning of each successful channel -/

/-- Each successful channel retains its **own** independent source meaning: the drawing channel
keeps `CanonicalOccurrenceOrdinaryDescriptor`, the planar parser channel keeps
`PlanarConstitutionParserRichDescriptorMeaning`. Nothing is transferred between them. -/
noncomputable def PlanarMixedAssignedMeaning {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) : Prop :=
  (occurrenceOrdinaryDescriptor? source target view ruleFuel = some label →
    CanonicalOccurrenceOrdinaryDescriptor source target view ruleFuel label) ∧
    (planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target view
        ruleFuel = some label →
      PlanarConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact target
        view ruleFuel label)

theorem planarMixedAssignedMeaning_holds {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) :
    PlanarMixedAssignedMeaning molecule source agreement writtenExact target view ruleFuel label :=
  ⟨fun computed =>
      (occurrenceOrdinaryDescriptor?_eq_some_iff_canonical source target view ruleFuel label).mp
        computed,
   fun computed =>
      planarConstitutionParserRichDescriptor?_sound molecule source agreement writtenExact target
        view ruleFuel label computed⟩

/-- A named joint assignment: the merged status assigns `label` and each successful channel keeps
its own independent source meaning. -/
noncomputable def PlanarMixedJointDescriptor {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) : Prop :=
  planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
      .assigned label ∧
    PlanarMixedAssignedMeaning molecule source agreement writtenExact target view ruleFuel label

theorem planarMixedJointDescriptor_iff_status {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) :
    PlanarMixedJointDescriptor molecule source agreement writtenExact target view ruleFuel label ↔
      planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
        .assigned label := by
  constructor
  · intro named
    unfold PlanarMixedJointDescriptor at named
    exact named.1
  · intro assigned
    unfold PlanarMixedJointDescriptor
    exact ⟨assigned,
      planarMixedAssignedMeaning_holds molecule source agreement writtenExact target view ruleFuel
        label⟩

/-- Canonical joint evaluator exactness in terms of the named joint assignment. -/
theorem planarMixedJointDescriptor?_eq_some_iff_descriptor {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel) :
    planarMixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel =
        some label ↔
      PlanarMixedJointDescriptor molecule source agreement writtenExact target view ruleFuel
        label :=
  (planarMixedJointDescriptor?_eq_some_iff_status molecule source agreement writtenExact target view
      ruleFuel label).trans
    (planarMixedJointDescriptor_iff_status molecule source agreement writtenExact target view ruleFuel
      label).symm

/-! ## 4. The separate recomputable conflict diagnostic -/

/-- The actual conflict status, retained separately and recomputable from the two actual channels.
This is a typed disagreement of two actual channels; it is **not** a claim of chemical
nonstereogenicity and does not authorize adoption. -/
noncomputable def PlanarMixedConflictDiagnostic {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) : Prop :=
  planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel = .conflict

/-- A conflict diagnostic exposes two actual successful channels carrying different labels. -/
theorem planarMixedConflictDiagnostic_witness {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (conflict :
      PlanarMixedConflictDiagnostic molecule source agreement writtenExact target view ruleFuel) :
    ∃ first ∈ planarMixedChannelOutputs molecule source agreement writtenExact target view ruleFuel,
      ∃ second ∈ planarMixedChannelOutputs molecule source agreement writtenExact target view ruleFuel,
        ∃ firstLabel secondLabel,
          first = some firstLabel ∧ second = some secondLabel ∧ firstLabel ≠ secondLabel := by
  have classified :=
    foldStatus_classifies (planarMixedChannelOutputs molecule source agreement writtenExact target
      view ruleFuel)
  unfold PlanarMixedConflictDiagnostic at conflict
  unfold planarMixedChannelStatus at conflict
  rw [conflict] at classified
  exact classified

/-- A conflict diagnostic is nonassignment in the joint evaluator. -/
theorem planarMixedConflictDiagnostic_nonassignment {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (conflict :
      PlanarMixedConflictDiagnostic molecule source agreement writtenExact target view ruleFuel) :
    planarMixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel = none := by
  rw [planarMixedJointDescriptor?_eq_none_iff_status]
  exact Or.inr (by simpa [PlanarMixedConflictDiagnostic] using conflict)

/-- **Generic two-channel disagreement.** Two actual successes with different labels merge to a
typed conflict, including an upper/lower-case `chiral`/`pseudoasymmetric` mismatch. -/
theorem planarMixedChannelStatus_conflict_of_actual_disagreement {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : occurrenceOrdinaryDescriptor? source target view ruleFuel = some leftLabel)
    (parser : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target
      view ruleFuel = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
      .conflict := by
  unfold planarMixedChannelStatus planarMixedChannelOutputs
  rw [drawing, parser]
  exact foldStatus_pair_some_some_diff leftLabel rightLabel different

/-- Generic two-channel disagreement yields local nonassignment at the supplied target and view. -/
theorem planarMixedJointDescriptor?_eq_none_of_actual_disagreement {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : occurrenceOrdinaryDescriptor? source target view ruleFuel = some leftLabel)
    (parser : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target
      view ruleFuel = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    planarMixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel = none := by
  have conflict := planarMixedChannelStatus_conflict_of_actual_disagreement molecule source agreement
    writtenExact target view ruleFuel leftLabel rightLabel drawing parser different
  rw [planarMixedJointDescriptor?_eq_none_iff_status]
  exact Or.inr conflict






noncomputable def PlanarMixedChannelsResolved {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) : Prop :=
  occurrenceOrdinaryDescriptor? source target view ruleFuel ≠ none ∧
    planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target view
      ruleFuel ≠ none

/-- The local merge maps "drawing absent, parser successful" to `assigned`. This establishes neither
`PlanarMixedChannelsResolved` at that target nor source-wide annotation coverage. -/
theorem planarMixedChannelStatus_assigned_of_absent_and_success {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel)
    (drawingAbsent : occurrenceOrdinaryDescriptor? source target view ruleFuel = none)
    (parserSuccess : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel = some label) :
    planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
      .assigned label := by
  unfold planarMixedChannelStatus planarMixedChannelOutputs
  rw [drawingAbsent, parserSuccess]
  exact foldStatus_pair_none_some label

/-- The local merge maps "drawing successful, parser absent" to `assigned`. -/
theorem planarMixedChannelStatus_assigned_of_success_and_absent {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (label : AromaticCanonicalAuxiliaryLabel)
    (drawingSuccess : occurrenceOrdinaryDescriptor? source target view ruleFuel = some label)
    (parserAbsent : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact
      target view ruleFuel = none) :
    planarMixedChannelStatus molecule source agreement writtenExact target view ruleFuel =
      .assigned label := by
  unfold planarMixedChannelStatus planarMixedChannelOutputs
  rw [drawingSuccess, parserAbsent]
  exact foldStatus_pair_some_none label

/-! ## 6. The NEW joint causal model and its own scheduler -/

/-- The NEW joint declarative outcome. `none` is exactly all-absent or conflict; `some label` is the
named joint assignment with each successful channel's own meaning. -/
noncomputable def PlanarMixedOutcome {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  match outcome with
  | none =>
      planarMixedChannelStatus molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = .unassigned ∨
      planarMixedChannelStatus molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = .conflict
  | some label =>
      PlanarMixedJointDescriptor molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel label

/-- The declarative joint outcome is exactly the NEW joint evaluator's own output. -/
theorem planarMixedOutcome_iff {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) :
    PlanarMixedOutcome molecule source agreement writtenExact ruleFuel state target outcome ↔
      planarMixedJointDescriptor? molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = outcome := by
  cases outcome with
  | none =>
      exact (planarMixedJointDescriptor?_eq_none_iff_status molecule source agreement writtenExact
        target (source.aromaticCanonicalDependencyView state target) ruleFuel).symm
  | some label =>
      exact (planarMixedJointDescriptor?_eq_some_iff_descriptor molecule source agreement
        writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel
        label).symm

/-- The joint rule semantics: declarative outcome and executable evaluator agree by construction. -/
noncomputable def planarMixedAuxiliarySemantics (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalRuleSemantics carrierFuel where
  DeclarativeDerivation := PlanarMixedOutcome molecule source agreement writtenExact ruleFuel
  executableRule := fun target view =>
    planarMixedJointDescriptor? molecule source agreement writtenExact target view ruleFuel
  derivation_executable_iff := planarMixedOutcome_iff molecule source agreement writtenExact ruleFuel

/-- The finite source occurrence system of the NEW joint semantics has a unique `CIPModel`. -/
theorem existsUnique_planarMixedCIPModel (carrierFuel ruleFuel : Nat) :
    ∃! state, (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
        ruleFuel)).CIPModel state :=
  source.existsUnique_aromaticCanonicalCIPModel
    (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)

/-- The internally scheduled joint state, produced by the source occurrence scheduler. -/
noncomputable def planarMixedScheduledState (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  DeclarativeCIP.OccurrenceScheduler.decode
    (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (DeclarativeCIP.OccurrenceScheduler.closure
      (source.aromaticCanonicalOccurrenceSystem
        (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
      (@source.AromaticCanonicalDepthDependency carrierFuel))

theorem planarMixedScheduledState_cipModel (carrierFuel ruleFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
        ruleFuel)).CIPModel
      (planarMixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel) :=
  source.aromaticCanonicalSchedulerClosure_cipModel
    (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)

/-- Under any NEW joint model the state is the joint evaluator at every original occurrence. -/
theorem planarMixedModel_evaluates {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
        ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    planarMixedJointDescriptor? molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = state target := by
  have fixed := (source.aromaticCanonicalOccurrenceSystem
    (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
      ruleFuel)).cipModel_iff_executableStateStep_fixed
      (source.aromaticCanonicalDerivationStepCorrespondence
        (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
          ruleFuel))
      state |>.mp model
  exact congrFun fixed target




theorem planarMixedModel_unique (carrierFuel ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
        ruleFuel)).CIPModel state) :
    state = planarMixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel := by
  obtain ⟨canonical, _canonicalModel, unique⟩ :=
    existsUnique_planarMixedCIPModel molecule source agreement writtenExact carrierFuel ruleFuel
  exact (unique state model).trans
    (unique _ (planarMixedScheduledState_cipModel molecule source agreement writtenExact carrierFuel
      ruleFuel)).symm

/-- Output soundness: an assigned NEW joint model result carries the named joint assignment. -/
theorem planarMixedModel_output_sound {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
        ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (label : AromaticCanonicalAuxiliaryLabel) (assigned : state target = some label) :
    PlanarMixedJointDescriptor molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel label :=
  (planarMixedJointDescriptor?_eq_some_iff_descriptor molecule source agreement writtenExact target
    (source.aromaticCanonicalDependencyView state target) ruleFuel label).mp
    ((planarMixedModel_evaluates molecule source agreement writtenExact state model target).trans
      assigned)

/-- **Independent conflict diagnosis under the NEW joint model.** At any original occurrence
disagreement between two actual successful channels implies nonassignment and a recomputable typed
conflict. No converse from nonassignment is asserted; the diagnosis is computed from the two actual
evaluators, not from the model assumption. -/
theorem planarMixedModel_conflict_nonassignment {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
        ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : occurrenceOrdinaryDescriptor? source target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = some leftLabel)
    (parser : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    state target = none ∧
      PlanarMixedConflictDiagnostic molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel := by
  have evaluates := planarMixedModel_evaluates molecule source agreement writtenExact state model
    target
  have conflict := planarMixedChannelStatus_conflict_of_actual_disagreement molecule source
    agreement writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel
    leftLabel rightLabel drawing parser different
  refine ⟨?_, ?_⟩
  · rw [← evaluates, planarMixedJointDescriptor?_eq_none_iff_status]
    exact Or.inr conflict
  · show planarMixedChannelStatus molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = .conflict
    exact conflict

/-- Specialisation to a final centre: the NEW joint model diagnoses an actual two-channel
disagreement at `source.aromaticCanonicalFinalOccurrence carrierFuel center` independently. -/
theorem planarMixedModel_finalCenter_conflict_nonassignment {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel
        ruleFuel)).CIPModel state)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (leftLabel rightLabel : AromaticCanonicalAuxiliaryLabel)
    (drawing : occurrenceOrdinaryDescriptor? source
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)
      (source.aromaticCanonicalDependencyView state
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel = some leftLabel)
    (parser : planarConstitutionParserRichDescriptor? molecule source agreement writtenExact
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)
      (source.aromaticCanonicalDependencyView state
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel = some rightLabel)
    (different : leftLabel ≠ rightLabel) :
    state (source.aromaticCanonicalFinalOccurrence carrierFuel center) = none ∧
      PlanarMixedConflictDiagnostic molecule source agreement writtenExact
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel :=
  planarMixedModel_conflict_nonassignment molecule source agreement writtenExact state model
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) leftLabel rightLabel drawing parser
    different

/-! ## 7. Source-wide candidate conflict guard at the NEW joint own views -/


noncomputable def planarJointState (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  planarMixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel

/-- The dependency view of the NEW joint own state at a target. -/
noncomputable def planarJointView (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    source.AromaticCanonicalDependencyView target :=
  source.aromaticCanonicalDependencyView
    (planarJointState molecule source agreement writtenExact carrierFuel ruleFuel) target

/-- The planar parser channel read at the NEW joint own state's view. -/
noncomputable def planarJointParserDescriptor? (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel :=
  planarConstitutionParserRichDescriptor? molecule source agreement writtenExact target
    (planarJointView molecule source agreement writtenExact carrierFuel ruleFuel target) ruleFuel

/-- The drawing channel read at the NEW joint own state's view. -/
noncomputable def planarJointDrawingDescriptor? (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    Option AromaticCanonicalAuxiliaryLabel :=
  occurrenceOrdinaryDescriptor? source target
    (planarJointView molecule source agreement writtenExact carrierFuel ruleFuel target) ruleFuel

/-- The NEW joint two-channel status at the NEW joint own state's view. -/
noncomputable def planarJointStatus (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    ChannelStatus AromaticCanonicalAuxiliaryLabel :=
  planarMixedChannelStatus molecule source agreement writtenExact target
    (planarJointView molecule source agreement writtenExact carrierFuel ruleFuel target) ruleFuel

/-- The NEW joint status unfolds to the two actual channel results in fixed order. -/
theorem planarJointStatus_eq_fold (carrierFuel ruleFuel : Nat)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel target =
      foldStatus [planarJointDrawingDescriptor? molecule source agreement writtenExact carrierFuel
          ruleFuel target,
        planarJointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
          target] := rfl




noncomputable def planarGlobalConflictIssues (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalTetrahedralCenter :=
  source.aromaticCanonicalTetrahedralCenters.filterMap fun center =>
    if planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) = .conflict then
      some center
    else none

/-- **Exact guard characterisation**: the source-wide candidate conflict guard is empty precisely
when no actual tetrahedral candidate's NEW joint status at the NEW joint own view is a typed
conflict. -/
theorem planarGlobalConflictIssues_eq_nil_iff (carrierFuel ruleFuel : Nat) :
    planarGlobalConflictIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      ∀ center, center ∈ source.aromaticCanonicalTetrahedralCenters →
        planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel
          (source.aromaticCanonicalFinalOccurrence carrierFuel center) ≠ .conflict := by
  unfold planarGlobalConflictIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty center present conflict
    have h := empty center present
    rw [if_pos conflict] at h
    exact absurd h (by simp)
  · intro noConflict center present
    rw [if_neg (noConflict center present)]

/-- The source-wide candidate conflict guard predicate. -/
noncomputable def PlanarGlobalConflictFree (carrierFuel ruleFuel : Nat) : Prop :=
  planarGlobalConflictIssues molecule source agreement writtenExact carrierFuel ruleFuel = []

/-! ## 8. Source-bound raw-parity interpretation at the NEW joint own views -/






noncomputable def PlanarRawParityJointInterpretation (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) : Prop :=
  ∃ candidate : source.AromaticCanonicalTetrahedralCenter,
    (parserIndexViaConversion molecule source agreement.1 candidate).val = annotation.index ∧
      (∃ spec, molecule.atomAt?
          (parserIndexViaConversion molecule source agreement.1 candidate).val = some spec ∧
        spec.tetrahedral? = some annotation.parity) ∧
        ∃ descriptor : AromaticCanonicalAuxiliaryLabel,
          planarJointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
              (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) = some descriptor ∧
            PlanarConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact
              (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)
              (planarJointView molecule source agreement writtenExact carrierFuel ruleFuel
                (source.aromaticCanonicalFinalOccurrence carrierFuel candidate))
              ruleFuel descriptor

/-- A scheduled NEW joint parser descriptor at a candidate that carries the actual raw parity yields
the raw-parity interpretation. -/
theorem planarRawParityJointInterpretation_of_candidate (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) (candidate : source.AromaticCanonicalTetrahedralCenter)
    (indexEq :
      (parserIndexViaConversion molecule source agreement.1 candidate).val = annotation.index)
    (specData : ∃ spec, molecule.atomAt?
        (parserIndexViaConversion molecule source agreement.1 candidate).val = some spec ∧
      spec.tetrahedral? = some annotation.parity)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (descriptorEq : planarJointParserDescriptor? molecule source agreement writtenExact carrierFuel
      ruleFuel (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) = some descriptor) :
    PlanarRawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
      annotation :=
  ⟨candidate, indexEq, specData, descriptor, descriptorEq,
    planarConstitutionParserRichDescriptor?_sound molecule source agreement writtenExact
      (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)
      (planarJointView molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)) ruleFuel descriptor
      (by simpa only [planarJointParserDescriptor?] using descriptorEq)⟩

/-! ## 9. Annotated drawing-centre coverage at the NEW joint own views -/

/-- Every absolute-scope actual source atom configuration index. -/
def planarAbsoluteConfigurationAtoms : List Nat :=
  (sourceAtomConfigurations source).filterMap fun configuration =>
    if configuration.scope = DiagramConfigurationScope.absolute then some configuration.atom
    else none

/-- Every actual solid/hashed wedge endpoint source index of the source diagram. -/
def planarWedgeEndpoints : List Nat :=
  match source.diagram? with
  | none => []
  | some diagram =>
      (diagram.bonds.filter fun bond =>
        decide (bond.style = .solidWedge ∨ bond.style = .hashedWedge)).map DiagramBond.source

/-- Every actual annotated source atom index: absolute configurations and wedge endpoints. -/
def planarAnnotatedSourceAtoms : List Nat :=
  planarAbsoluteConfigurationAtoms source ++ planarWedgeEndpoints source

/-- The actual source candidates at a source atom index. -/
noncomputable def planarCandidatesAt (atomIndex : Nat) :
    List source.AromaticCanonicalTetrahedralCenter :=
  source.aromaticCanonicalTetrahedralCenters.filter fun candidate =>
    candidate.1.val == atomIndex






noncomputable def PlanarAnnotatedCenterInterpreted (carrierFuel ruleFuel : Nat)
    (atomIndex : Nat) : Prop :=
  ∃ candidate ∈ planarCandidatesAt source atomIndex,
    (atomIndex ∉ planarWedgeEndpoints source ∨
      planarJointDrawingDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) ≠ none) ∧
    (atomIndex ∉ planarAbsoluteConfigurationAtoms source ∨
      planarJointParserDescriptor? molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) ≠ none) ∧
    (∃ label, planarJointStatus molecule source agreement writtenExact carrierFuel ruleFuel
      (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) = .assigned label)











noncomputable def PlanarJointPartialAudit (carrierFuel ruleFuel : Nat) : Prop :=
  (∀ annotation, annotation ∈ rawAtomAnnotations molecule →
    PlanarRawParityJointInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
      annotation) ∧
    rawBondDirections molecule = [] ∧
    MixedBondAnnotationsAccepted source ∧
    (∀ atomIndex, atomIndex ∈ planarAnnotatedSourceAtoms source →
      PlanarAnnotatedCenterInterpreted molecule source agreement writtenExact carrierFuel ruleFuel
        atomIndex)










noncomputable def PlanarJointAuditObligation (carrierFuel ruleFuel : Nat) : Prop :=
  PlanarGlobalConflictFree molecule source agreement writtenExact carrierFuel ruleFuel ∧
    PlanarJointPartialAudit molecule source agreement writtenExact carrierFuel ruleFuel

end TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel
