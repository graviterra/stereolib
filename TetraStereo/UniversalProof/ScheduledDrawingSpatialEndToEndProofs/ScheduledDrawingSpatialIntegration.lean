import TetraStereo.OneCenter.AuthoritativeSingleWedgeDescriptorConstruction
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6RSPseudoTotality
import TetraStereo.OneCenter.AuthoritativeSemanticParserDiagramRule3Through6Analysis

set_option autoImplicit false




























namespace TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource

universe u

variable {Label : Type u}

/-! ## Generic three-way channel status -/

/-- The three mutually exclusive merge outcomes of a finite list of optional channel results. -/
inductive ChannelStatus (Label : Type u) where
  | unassigned : ChannelStatus Label
  | assigned : Label → ChannelStatus Label
  | conflict : ChannelStatus Label
  deriving DecidableEq, Repr

/-- One merge step: absence is neutral, a first success assigns, a disagreeing success conflicts,
and `conflict` is absorbing. -/
def mergeChannel [DecidableEq Label] :
    ChannelStatus Label → Option Label → ChannelStatus Label
  | .conflict, _ => .conflict
  | acc, none => acc
  | .unassigned, some label => .assigned label
  | .assigned earlier, some label =>
      if label = earlier then .assigned earlier else .conflict

/-- The executable fold of the channel results. -/
def foldStatus [DecidableEq Label] (outputs : List (Option Label)) : ChannelStatus Label :=
  outputs.foldl mergeChannel .unassigned

/-- Independent specification of the fold, stated directly over the optional channel results.
`unassigned` describes all-absent, `assigned` is a success shared by every success, `conflict`
is two successful results with different labels. -/
def ClassifiesStatus (outputs : List (Option Label)) : ChannelStatus Label → Prop
  | .unassigned => ∀ output ∈ outputs, output = none
  | .assigned label =>
      (∃ output ∈ outputs, output = some label) ∧
        ∀ output ∈ outputs, output = none ∨ output = some label
  | .conflict =>
      ∃ first ∈ outputs, ∃ second ∈ outputs, ∃ firstLabel secondLabel,
        first = some firstLabel ∧ second = some secondLabel ∧ firstLabel ≠ secondLabel

/-- Extending a prefix by one result preserves its independent classification under one merge
step. -/
theorem mergeChannel_classifies [DecidableEq Label] (seen : List (Option Label))
    (next : Option Label) (acc : ChannelStatus Label)
    (classified : ClassifiesStatus seen acc) :
    ClassifiesStatus (seen ++ [next]) (mergeChannel acc next) := by
  cases acc with
  | conflict =>
      change ClassifiesStatus (seen ++ [next]) .conflict
      simp only [ClassifiesStatus] at classified
      obtain ⟨first, firstMem, second, secondMem, firstLabel, secondLabel,
        firstEq, secondEq, different⟩ := classified
      exact ⟨first, List.mem_append.mpr (Or.inl firstMem),
        second, List.mem_append.mpr (Or.inl secondMem),
        firstLabel, secondLabel, firstEq, secondEq, different⟩
  | unassigned =>
      cases next with
      | none =>
          change ClassifiesStatus (seen ++ [none]) .unassigned
          intro output member
          rcases List.mem_append.mp member with present | here
          · exact classified output present
          · exact List.mem_singleton.mp here
      | some label =>
          change ClassifiesStatus (seen ++ [some label]) (.assigned label)
          refine ⟨⟨some label, List.mem_append.mpr (Or.inr (by simp)), rfl⟩, ?_⟩
          intro output member
          rcases List.mem_append.mp member with present | here
          · exact Or.inl (classified output present)
          · exact Or.inr (List.mem_singleton.mp here)
  | assigned earlier =>
      simp only [ClassifiesStatus] at classified
      obtain ⟨⟨witness, witnessMem, witnessEq⟩, allSame⟩ := classified
      cases next with
      | none =>
          change ClassifiesStatus (seen ++ [none]) (.assigned earlier)
          refine ⟨⟨witness, List.mem_append.mpr (Or.inl witnessMem), witnessEq⟩, ?_⟩
          intro output member
          rcases List.mem_append.mp member with present | here
          · exact allSame output present
          · exact Or.inl (List.mem_singleton.mp here)
      | some label =>
          change ClassifiesStatus (seen ++ [some label])
            (if label = earlier then .assigned earlier else .conflict)
          split_ifs with same
          · refine ⟨⟨witness, List.mem_append.mpr (Or.inl witnessMem), witnessEq⟩, ?_⟩
            intro output member
            rcases List.mem_append.mp member with present | here
            · exact allSame output present
            · exact Or.inr ((List.mem_singleton.mp here).trans (congrArg some same))
          · refine ⟨witness, List.mem_append.mpr (Or.inl witnessMem), some label,
              List.mem_append.mpr (Or.inr (by simp)), earlier, label,
              witnessEq, rfl, fun h => same h.symm⟩

/-- Prefix-generalised fold reflection. -/
theorem foldl_classifies [DecidableEq Label] (outputs : List (Option Label)) :
    ∀ (seenPrefix : List (Option Label)) (acc : ChannelStatus Label),
      ClassifiesStatus seenPrefix acc →
      ClassifiesStatus (seenPrefix ++ outputs) (outputs.foldl mergeChannel acc) := by
  induction outputs with
  | nil =>
      intro seenPrefix acc classified
      simpa using classified
  | cons head tail inductionHypothesis =>
      intro seenPrefix acc classified
      have step := mergeChannel_classifies seenPrefix head acc classified
      have rest := inductionHypothesis (seenPrefix ++ [head]) (mergeChannel acc head) step
      rw [List.foldl_cons]
      simpa [List.append_assoc] using rest

/-- **Executable reflection.** The computed fold always satisfies the independent specification;
`unassigned` is never vacuously `assigned`, and disagreement is `conflict`. -/
theorem foldStatus_classifies [DecidableEq Label] (outputs : List (Option Label)) :
    ClassifiesStatus outputs (foldStatus outputs) := by
  simpa [foldStatus] using
    foldl_classifies outputs [] .unassigned (by intro output member; simp at member)

/-- Absence never becomes an assignment: a single success beside absences assigns that success. -/
theorem foldStatus_some_none_none [DecidableEq Label] (label : Label) :
    foldStatus [some label, none, none] = .assigned label := rfl

/-- Opposite uppercase labels conflict. -/
theorem foldStatus_opposite_labels_conflict :
    foldStatus ([some (.chiral .R), some (.chiral .S)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .conflict := by decide

/-- A literal mixed upper/lower pair conflicts: `chiral` and `pseudoasymmetric` are not equal. -/
theorem foldStatus_mixed_case_labels_conflict :
    foldStatus ([some (.chiral .R), some (.pseudoasymmetric .r)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .conflict := by decide

/-! ## Same scheduled auxiliary view for every channel -/

/-- The single scheduled dependency view shared by all three channels. -/
noncomputable def scheduledDrawingView (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) :=
  source.aromaticCanonicalDependencyView
    (source.aromaticCanonicalScheduledAuxiliaryState semantics)
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)

/-- The three channel results, in a fixed order, all read the same scheduled view. -/
noncomputable def scheduledDrawingOutputs (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    List (Option AromaticCanonicalAuxiliaryLabel) :=
  [ ordinaryDescriptor? source carrierFuel center
      (scheduledDrawingView source semantics center) ruleFuel,
    source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)
      (scheduledDrawingView source semantics center) ruleFuel,
    source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
      semantics ruleFuel center ]

/-- The source-level scheduled endpoint: the fold of the three channel results. -/
noncomputable def scheduledDrawingSpatialStatus (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    ChannelStatus AromaticCanonicalAuxiliaryLabel :=
  foldStatus (scheduledDrawingOutputs source semantics ruleFuel center)

/-! ## Independent meaning across the original source judgments -/

/-- Independent meaning of a successful drawing-channel result. -/
def DrawingChannelMeaning (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (ruleFuel : Nat) (output : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∀ descriptor, output = some descriptor →
    OrdinaryDescriptorMeaning source carrierFuel center view ruleFuel descriptor

/-- Independent meaning of a successful direct spatial-ordinary-channel result. -/
def DirectSpatialChannelMeaning (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (output : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∀ descriptor, output = some descriptor →
    source.CanonicalAromaticCanonicalOccurrenceRule3Through5Descriptor
      target view ruleFuel descriptor

/-- Independent meaning of a successful scheduled spatial-tie result. -/
def ScheduledTieChannelMeaning (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (output : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∀ descriptor, output = some descriptor →
    source.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
      semantics ruleFuel center descriptor

/-- The source wrapper's independent meaning: every channel result that succeeds carries its own
original source judgment, obtained at the same scheduled view, and the scheduled auxiliary state
is an internal `CIPModel`. The source/center/fuel/view bindings are preserved. -/
def ScheduledDrawingSpatialMeaning (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  DrawingChannelMeaning source carrierFuel center
      (scheduledDrawingView source semantics center) ruleFuel
      (ordinaryDescriptor? source carrierFuel center
        (scheduledDrawingView source semantics center) ruleFuel) ∧
    DirectSpatialChannelMeaning source
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)
      (scheduledDrawingView source semantics center) ruleFuel
      (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (scheduledDrawingView source semantics center) ruleFuel) ∧
    ScheduledTieChannelMeaning source semantics ruleFuel center
      (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor? semantics ruleFuel center) ∧
    (source.aromaticCanonicalOccurrenceSystem semantics).CIPModel
      (source.aromaticCanonicalScheduledAuxiliaryState semantics)

/-- For the supplied rule semantics, every successful channel is justified by its own source-level
judgment and the scheduled state is an internal fixed point at the common scheduled view. -/
theorem scheduledDrawingSpatialMeaning_holds (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    ScheduledDrawingSpatialMeaning source semantics ruleFuel center :=
  ⟨fun _ computed => ordinaryDescriptor?_sound source carrierFuel center _ ruleFuel _ computed,
   fun _ computed =>
     (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
       _ _ ruleFuel _).mp computed,
   fun _ computed =>
     (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
       semantics ruleFuel center _).mp computed,
   source.aromaticCanonicalScheduledAuxiliaryState_cipModel semantics⟩

/-- The computed executable status satisfies the independent classification of the three results. -/
theorem scheduledDrawingSpatialStatus_classifies (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    ClassifiesStatus (scheduledDrawingOutputs source semantics ruleFuel center)
      (scheduledDrawingSpatialStatus source semantics ruleFuel center) := by
  unfold scheduledDrawingSpatialStatus
  exact foldStatus_classifies _

/-- **Assigned soundness.** An assigned status has an actual successful channel witness. Every
channel result is absent or equals that label, and each channel retains its source meaning. -/
theorem scheduledDrawingSpatialStatus_assigned_sound (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (label : AromaticCanonicalAuxiliaryLabel)
    (assigned : scheduledDrawingSpatialStatus source semantics ruleFuel center = .assigned label) :
    (∃ output ∈ scheduledDrawingOutputs source semantics ruleFuel center,
        output = some label) ∧
      (∀ output ∈ scheduledDrawingOutputs source semantics ruleFuel center,
        output = none ∨ output = some label) ∧
      ScheduledDrawingSpatialMeaning source semantics ruleFuel center := by
  have classified := scheduledDrawingSpatialStatus_classifies source semantics ruleFuel center
  rw [assigned] at classified
  exact ⟨classified.1, classified.2,
    scheduledDrawingSpatialMeaning_holds source semantics ruleFuel center⟩

/-- **Conflict soundness.** A computed conflict supplies two successful results carrying different
labels; absence alone cannot supply this witness and no precedence is chosen. -/
theorem scheduledDrawingSpatialStatus_conflict_sound (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (conflict : scheduledDrawingSpatialStatus source semantics ruleFuel center = .conflict) :
    ∃ first ∈ scheduledDrawingOutputs source semantics ruleFuel center,
      ∃ second ∈ scheduledDrawingOutputs source semantics ruleFuel center,
        ∃ firstLabel secondLabel,
          first = some firstLabel ∧ second = some secondLabel ∧ firstLabel ≠ secondLabel := by
  have classified := scheduledDrawingSpatialStatus_classifies source semantics ruleFuel center
  rw [conflict] at classified
  exact classified

/-! ## Absent spatial channel: drawing-only source is admitted, the two spatial channels refuse -/

/-- Without a spatial channel, no real reroot node can acquire coordinates, so a nonempty
coordinate list lookup fails. Uses the safe-sorter permutation and the nonempty highest-first
order; no coordinates are invented. -/
theorem mapM_rerootSpatialPoint?_eq_none_of_spatial_none (source : AuthoritativeChemicalInput)
    (noSpatial : source.spatial? = none) {carrierFuel : Nat}
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (order : List (Fin 4)) (nonempty : order ≠ []) :
    order.mapM (fun index =>
      source.aromaticCanonicalRerootSpatialPoint? (base.cursorAt index)) = none := by
  cases order with
  | nil => exact absurd rfl nonempty
  | cons head tail =>
      simp [List.mapM_cons,
        source.aromaticCanonicalRerootSpatialPoint?_eq_none_of_spatial_none noSpatial
          (base.cursorAt head)]

/-- The highest-first ordering produced by the safe tracked sorter is never empty, because it is a
permutation of `List.finRange 4`. -/
theorem safeTrackedOrder_highestFirst_ne_nil (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? frame =
      some tracked) :
    tracked.highestFirst ≠ [] := by
  have perm := (source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_sound
    frame tracked computed).2.1
  have lengthEq : tracked.highestFirst.length = 4 := by
    have := perm.length_eq
    simpa [List.length_finRange] using this
  intro empty
  rw [empty] at lengthEq
  simp at lengthEq

/-- Direct spatial-ordinary evidence is impossible without a spatial channel. -/
theorem aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?_eq_none_of_spatial_none
    (source : AuthoritativeChemicalInput) (noSpatial : source.spatial? = none)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence? target view ruleFuel = none := by
  unfold aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp
  | some center =>
      cases baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target with
      | none => simp
      | some base =>
          cases keysComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
              target view ruleFuel base.roots with
          | none => simp [keysComputed]
          | some keys =>
              cases trackedComputed :
                  source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys with
              | none => simp [keysComputed, trackedComputed]
              | some tracked =>
                  simp [keysComputed, trackedComputed,
                    mapM_rerootSpatialPoint?_eq_none_of_spatial_none source noSpatial base
                      tracked.highestFirst
                      (safeTrackedOrder_highestFirst_ne_nil source keys tracked trackedComputed)]

/-- The direct spatial-ordinary descriptor refuses a source with no spatial channel. -/
theorem aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_none_of_spatial_none
    (source : AuthoritativeChemicalInput) (noSpatial : source.spatial? = none)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    source.aromaticCanonicalOccurrenceRule3Through5Descriptor? target view ruleFuel = none := by
  unfold aromaticCanonicalOccurrenceRule3Through5Descriptor?
  rw [aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?_eq_none_of_spatial_none
    source noSpatial target view ruleFuel]
  rfl

/-- The scheduled spatial Rule-6 tie endpoint refuses a source with no spatial channel. -/
theorem aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_of_spatial_none
    (source : AuthoritativeChemicalInput) (noSpatial : source.spatial? = none)
    {carrierFuel : Nat} (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor? semantics ruleFuel center =
      none := by
  unfold aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
  | none => simp [target, rootsComputed]
  | some roots =>
      simp [target, rootsComputed,
        source.aromaticCanonicalRerootFrameParity?_eq_none_of_spatial_none noSpatial roots]

/-! ## Realization: admitted strict atomic carrier-zero source yields `assigned` -/

/-- **Drawing-only realization.** For an admitted strict atomic-separated source frame at carrier
zero / rule two with no spatial channel, the two spatial channels refuse and only the recognized
ordinary drawing succeeds. The fold is therefore `assigned (.chiral raw)`, and the independent
meaning holds. No key or sort success premise is supplied. -/
theorem scheduledDrawingSpatialStatus_assigned_of_noSpatial_atomic_separation
    (source : AuthoritativeChemicalInput) (semantics : source.AromaticCanonicalRuleSemantics 0)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : SingleWedgeSource.Frame)
    (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing)
    (noSpatial : source.spatial? = none) :
    ∃ raw, scheduledDrawingSpatialStatus source semantics 2 center = .assigned (.chiral raw) ∧
      ScheduledDrawingSpatialMeaning source semantics 2 center := by
  obtain ⟨raw, drawingComputed⟩ :=
    ordinaryDescriptor?_chiral_exists_of_zero_carrier_source_atomic_separation source center
      (scheduledDrawingView source semantics center) drawing bound separated
  refine ⟨raw, ?_, scheduledDrawingSpatialMeaning_holds source semantics 2 center⟩
  have ordinaryNone :=
    aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_none_of_spatial_none source noSpatial
      (source.aromaticCanonicalFinalOccurrence 0 center) (scheduledDrawingView source semantics center) 2
  have tieNone :=
    aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_of_spatial_none
      source noSpatial semantics 2 center
  unfold scheduledDrawingSpatialStatus scheduledDrawingOutputs
  rw [drawingComputed, ordinaryNone, tieNone]
  rfl

/-! ## Closed source-level regression: the actual CFClBrI source -/

namespace Regressions

open SingleWedgeSourceRegression
open SingleWedgeOccurrenceAlignmentRegression
open SingleWedgeAtomicPriorityBridgeRegression
open SingleWedgePriorityDescriptorRegression

/-- The actual closed CFClBrI source has no spatial channel, so its two spatial channels refuse and
the recognized ordinary drawing alone yields `assigned`. The exact `R/S` label is not guessed; it
is carried as `raw`. -/
theorem cfclbri_closed_source_assigned
    (semantics : SingleWedgeSourceRegression.source.AromaticCanonicalRuleSemantics 0) :
    ∃ raw, scheduledDrawingSpatialStatus SingleWedgeSourceRegression.source semantics 2
        cfclbriProductionCenter = .assigned (.chiral raw) ∧
      ScheduledDrawingSpatialMeaning SingleWedgeSourceRegression.source semantics 2
        cfclbriProductionCenter := by
  obtain ⟨aligned, alignedComputed⟩ := cfclbri_constructed_center_alignment 0
  have bound := (occurrenceAlignment?_sound SingleWedgeSourceRegression.source 0
    cfclbriProductionCenter aligned.1 aligned.2 alignedComputed).1
  exact scheduledDrawingSpatialStatus_assigned_of_noSpatial_atomic_separation
    SingleWedgeSourceRegression.source semantics cfclbriProductionCenter aligned.1 bound
    (cfclbri_source_endpoint_atomic_separation aligned.1)
    cfclbri_no_spatial_channel

end Regressions

end TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
