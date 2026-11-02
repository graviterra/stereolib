import TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Actual root state of the nine-atom cyclic pseudo candidate

`LocalizedCyclicPseudoActualEvaluation.root_component_compound_eq_actual_concrete` identifies each
actual root compound with the production compound assembly over the concrete root-zero reader.
That assembly is evaluated by the kernel here. The comparison results are read back into the
retained keys of the actual compiled root frame, and the current retained judgment returns the
root state. No key, label, order or count is supplied.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader

open TetraStereo.OneCenter
open CertifiedLocalizedCIPInput
open LocalizedRuleMajorReference
open DeclarativeCIP
open LocalizedCyclicPseudoSpatialWitness
open LocalizedCyclicPseudoActualEvaluation
open LocalizedCyclicPseudoActualRootLetter

noncomputable section

abbrev ComponentFrame := LocalizedCyclicPseudoRootComponentEvaluation.Frame
abbrev RootCompound := pseudoSpatialCertified.LocalizedRerootCompoundRule45Key
abbrev RootCursor := pseudoSpatialCertified.LocalizedRerootCursor (carrierFuel pseudoReference)
abbrev StageKey := pseudoSpatialCertified.LocalizedRerootCumulativeRule45Key

/-! ## Cursor-free compound assembly -/

private theorem rule4bcReading_cursor_free
    (compile : LocalizedCumulativeRule45Stage → Option StageKey) (first second : RootCursor)
    (reference : Option RS) :
    pseudoSpatialCertified.buildRuleMajorCompoundRule4bcReadingWith?
        (fun stage _ => compile stage) first reference =
      pseudoSpatialCertified.buildRuleMajorCompoundRule4bcReadingWith?
        (fun stage _ => compile stage) second reference := by
  cases reference <;> rfl

private theorem rule4bcReadings_cursor_free
    (compile : LocalizedCumulativeRule45Stage → Option StageKey) (first second : RootCursor) :
    ∀ references : List (Option RS),
      pseudoSpatialCertified.buildRuleMajorCompoundRule4bcReadingsWith?
          (fun stage _ => compile stage) first references =
        pseudoSpatialCertified.buildRuleMajorCompoundRule4bcReadingsWith?
          (fun stage _ => compile stage) second references
  | [] => rfl
  | reference :: references => by
      simp only [CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingsWith?,
        rule4bcReading_cursor_free compile first second reference,
        rule4bcReadings_cursor_free compile first second references]

private theorem rule5Reading_cursor_free
    (compile : LocalizedCumulativeRule45Stage → Option StageKey) (first second : RootCursor)
    (prior : pseudoSpatialCertified.LocalizedRerootRule4bcReading) :
    pseudoSpatialCertified.buildRuleMajorCompoundRule5ReadingWith?
        (fun stage _ => compile stage) first prior =
      pseudoSpatialCertified.buildRuleMajorCompoundRule5ReadingWith?
        (fun stage _ => compile stage) second prior := rfl

private theorem rule5Readings_cursor_free
    (compile : LocalizedCumulativeRule45Stage → Option StageKey) (first second : RootCursor) :
    ∀ priors : List pseudoSpatialCertified.LocalizedRerootRule4bcReading,
      pseudoSpatialCertified.buildRuleMajorCompoundRule5ReadingsWith?
          (fun stage _ => compile stage) first priors =
        pseudoSpatialCertified.buildRuleMajorCompoundRule5ReadingsWith?
          (fun stage _ => compile stage) second priors
  | [] => rfl
  | prior :: priors => by
      simp only [CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule5ReadingsWith?,
        rule5Reading_cursor_free compile first second prior,
        rule5Readings_cursor_free compile first second priors]

/-- A stage compiler that ignores its cursor assembles the same compound at every cursor. -/
theorem compound_cursor_free
    (compile : LocalizedCumulativeRule45Stage → Option StageKey) (first second : RootCursor) :
    pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
        (fun stage _ => compile stage) first =
      pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
        (fun stage _ => compile stage) second := by
  unfold CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyWith?
  simp only [rule4bcReadings_cursor_free compile first second,
    rule5Readings_cursor_free compile first second]

/-! ## The concrete root compounds -/

/-- One root ligand compound, assembled by the production builder over the concrete reader. -/
def concreteCompound (candidate : ComponentFrame) : Option RootCompound :=
  pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
    (fun stage (_ : RootCursor) =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
        LocalizedCyclicPseudoRootComponentEvaluation.concreteReadFrame
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        candidate (some LocalizedCyclicPseudoRootComponentEvaluation.rootF))
    (⟨rootTarget, none⟩ : RootCursor)

theorem concreteCompound_eq_actual (slot : Fin 4) (candidate : ComponentFrame)
    (occurrenceEq : (rootFrames.frame.cursorAt slot).occurrence.1 = candidate)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF,
        LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF]) :
    concreteCompound candidate = some (rootFrames.compounds slot) := by
  unfold concreteCompound
  rw [compound_cursor_free _ _ (rootFrames.frame.cursorAt slot)]
  exact root_component_compound_eq_actual_concrete slot candidate
    (by rw [occurrenceEq]) candidateMem

theorem concrete_fluorine :
    concreteCompound LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF =
      some (rootFrames.compounds rootFluorineSlot) :=
  concreteCompound_eq_actual rootFluorineSlot _
    root_actual_frame_correspondence.2.2.2.2.1 (by simp)

theorem concrete_arm :
    concreteCompound LocalizedCyclicPseudoRootComponentEvaluation.armF =
      some (rootFrames.compounds rootArmSlot) :=
  concreteCompound_eq_actual rootArmSlot _
    root_actual_frame_correspondence.2.2.2.2.2.1 (by simp)

theorem concrete_closing :
    concreteCompound LocalizedCyclicPseudoRootComponentEvaluation.closeF =
      some (rootFrames.compounds rootClosingSlot) :=
  concreteCompound_eq_actual rootClosingSlot _
    root_actual_frame_correspondence.2.2.2.2.2.2.1 (by simp)

theorem concrete_hydrogen :
    concreteCompound LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF =
      some (rootFrames.compounds rootHydrogenSlot) :=
  concreteCompound_eq_actual rootHydrogenSlot _
    root_actual_frame_correspondence.2.2.2.2.2.2.2 (by simp)

/-! ## Kernel-evaluated comparisons -/

/-- Through-Rule-5 comparison of two concrete root compounds. -/
def throughRule5Check (left right : ComponentFrame) (ordering : Ordering) (pseudo : Bool) :
    Bool :=
  match concreteCompound left, concreteCompound right with
  | some leftKey, some rightKey =>
      decide (pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey =
        { ordering := ordering, pseudo := pseudo })
  | _, _ => false

/-- Prior (Rules 4a, 4b and 4c) comparison of two concrete root compounds. -/
def priorCheck (left right : ComponentFrame) (ordering : Ordering) : Bool :=
  match concreteCompound left, concreteCompound right with
  | some leftKey, some rightKey =>
      decide (pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
        leftKey.prior rightKey.prior = ordering)
  | _, _ => false

/-- Rule-4a key comparison of two concrete root compounds. -/
def rule4aCheck (left right : ComponentFrame) (ordering : Ordering) : Bool :=
  match concreteCompound left, concreteCompound right with
  | some leftKey, some rightKey =>
      decide (pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
        leftKey.prior.rule4aKey rightKey.prior.rule4aKey = ordering)
  | _, _ => false

/-- Rule-4b reference selection and its count priority in one concrete root compound. -/
def referencesCheck (candidate : ComponentFrame) (references : List RS) (count : Nat) : Bool :=
  match concreteCompound candidate with
  | some key =>
      decide (key.prior.references = references ∧ key.prior.referenceCountPriority = count)
  | none => false

/-- Rule-5 reading-list comparison of two concrete root compounds under one common reference. -/
def rule5Check (left right : ComponentFrame) (common : RS) (ordering : Ordering) : Bool :=
  match concreteCompound left, concreteCompound right with
  | some leftKey, some rightKey =>
      decide (pseudoSpatialCertified.compareLocalizedRerootCompoundRule5Readings common
        leftKey.rule5Readings rightKey.rule5Readings = ordering)
  | _, _ => false

theorem arm_references_check :
    referencesCheck LocalizedCyclicPseudoRootComponentEvaluation.armF [RS.R] 2 = true := by
  decide +kernel

theorem closing_references_check :
    referencesCheck LocalizedCyclicPseudoRootComponentEvaluation.closeF [RS.S] 2 = true := by
  decide +kernel

theorem arm_closing_rule4a_check :
    rule4aCheck LocalizedCyclicPseudoRootComponentEvaluation.armF
      LocalizedCyclicPseudoRootComponentEvaluation.closeF .eq = true := by
  decide +kernel

theorem arm_closing_prior_check :
    priorCheck LocalizedCyclicPseudoRootComponentEvaluation.armF
      LocalizedCyclicPseudoRootComponentEvaluation.closeF .eq = true := by
  decide +kernel

theorem arm_closing_rule5R_check :
    rule5Check LocalizedCyclicPseudoRootComponentEvaluation.armF
      LocalizedCyclicPseudoRootComponentEvaluation.closeF RS.R .gt = true := by
  decide +kernel

theorem arm_closing_rule5S_check :
    rule5Check LocalizedCyclicPseudoRootComponentEvaluation.armF
      LocalizedCyclicPseudoRootComponentEvaluation.closeF RS.S .lt = true := by
  decide +kernel

theorem arm_closing_throughRule5_check :
    throughRule5Check LocalizedCyclicPseudoRootComponentEvaluation.armF
      LocalizedCyclicPseudoRootComponentEvaluation.closeF .gt true = true := by
  decide +kernel

theorem fluorine_arm_prior_check :
    priorCheck LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF
      LocalizedCyclicPseudoRootComponentEvaluation.armF .gt = true := by
  decide +kernel

theorem fluorine_closing_prior_check :
    priorCheck LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF
      LocalizedCyclicPseudoRootComponentEvaluation.closeF .gt = true := by
  decide +kernel

theorem fluorine_hydrogen_prior_check :
    priorCheck LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF
      LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF .gt = true := by
  decide +kernel

theorem arm_hydrogen_prior_check :
    priorCheck LocalizedCyclicPseudoRootComponentEvaluation.armF
      LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF .gt = true := by
  decide +kernel

theorem closing_hydrogen_prior_check :
    priorCheck LocalizedCyclicPseudoRootComponentEvaluation.closeF
      LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF .gt = true := by
  decide +kernel

/-! ## Read-back into the actual root compounds -/

private theorem prior_of_check {left right : ComponentFrame} {leftKey rightKey : RootCompound}
    {ordering : Ordering}
    (leftEq : concreteCompound left = some leftKey)
    (rightEq : concreteCompound right = some rightKey)
    (check : priorCheck left right ordering = true) :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = ordering := by
  unfold priorCheck at check
  rw [leftEq, rightEq] at check
  exact of_decide_eq_true check

private theorem throughRule5_of_check {left right : ComponentFrame}
    {leftKey rightKey : RootCompound} {ordering : Ordering} {pseudo : Bool}
    (leftEq : concreteCompound left = some leftKey)
    (rightEq : concreteCompound right = some rightKey)
    (check : throughRule5Check left right ordering pseudo = true) :
    pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey =
      { ordering := ordering, pseudo := pseudo } := by
  unfold throughRule5Check at check
  rw [leftEq, rightEq] at check
  exact of_decide_eq_true check

private theorem rule4a_of_check {left right : ComponentFrame} {leftKey rightKey : RootCompound}
    {ordering : Ordering}
    (leftEq : concreteCompound left = some leftKey)
    (rightEq : concreteCompound right = some rightKey)
    (check : rule4aCheck left right ordering = true) :
    pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey = ordering := by
  unfold rule4aCheck at check
  rw [leftEq, rightEq] at check
  exact of_decide_eq_true check

private theorem references_of_check {candidate : ComponentFrame} {key : RootCompound}
    {references : List RS} {count : Nat}
    (keyEq : concreteCompound candidate = some key)
    (check : referencesCheck candidate references count = true) :
    key.prior.references = references ∧ key.prior.referenceCountPriority = count := by
  unfold referencesCheck at check
  rw [keyEq] at check
  exact of_decide_eq_true check

private theorem rule5_of_check {left right : ComponentFrame} {leftKey rightKey : RootCompound}
    {common : RS} {ordering : Ordering}
    (leftEq : concreteCompound left = some leftKey)
    (rightEq : concreteCompound right = some rightKey)
    (check : rule5Check left right common ordering = true) :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule5Readings common
      leftKey.rule5Readings rightKey.rule5Readings = ordering := by
  unfold rule5Check at check
  rw [leftEq, rightEq] at check
  exact of_decide_eq_true check

/-- The actual ring-carbon compounds select their own uppercase references, one each. -/
theorem actual_ring_carbon_references :
    ((rootFrames.compounds rootArmSlot).prior.references = [RS.R] ∧
        (rootFrames.compounds rootArmSlot).prior.referenceCountPriority = 2) ∧
      ((rootFrames.compounds rootClosingSlot).prior.references = [RS.S] ∧
        (rootFrames.compounds rootClosingSlot).prior.referenceCountPriority = 2) :=
  ⟨references_of_check concrete_arm arm_references_check,
    references_of_check concrete_closing closing_references_check⟩

/-- The actual ring-carbon Rule-4a keys tie. -/
theorem actual_arm_closing_rule4a_tie :
    pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (rootFrames.compounds rootArmSlot).prior.rule4aKey
      (rootFrames.compounds rootClosingSlot).prior.rule4aKey = .eq :=
  rule4a_of_check concrete_arm concrete_closing arm_closing_rule4a_check

/-- Under common reference `R` the `R`-labelled ring carbon is senior; under `S` the order
reverses. -/
theorem actual_arm_closing_rule5_readings :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule5Readings RS.R
        (rootFrames.compounds rootArmSlot).rule5Readings
        (rootFrames.compounds rootClosingSlot).rule5Readings = .gt ∧
      pseudoSpatialCertified.compareLocalizedRerootCompoundRule5Readings RS.S
        (rootFrames.compounds rootArmSlot).rule5Readings
        (rootFrames.compounds rootClosingSlot).rule5Readings = .lt :=
  ⟨rule5_of_check concrete_arm concrete_closing arm_closing_rule5R_check,
    rule5_of_check concrete_arm concrete_closing arm_closing_rule5S_check⟩

private theorem throughRule5_of_prior_gt (left right : RootCompound)
    (prior : pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = .gt) :
    pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := .gt, pseudo := false } := by
  unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5
  simp [prior]

/-- The two ring-carbon ligands tie through Rule 4c. -/
theorem actual_arm_closing_prior_tie :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds rootArmSlot).prior (rootFrames.compounds rootClosingSlot).prior =
        .eq :=
  prior_of_check concrete_arm concrete_closing arm_closing_prior_check

/-- The ring-carbon prior tie holds at each source-ordered gate: Rule 4a, reference count, the
own-reference Rule-4b readings, and the own-reference Rule-4c readings. -/
theorem actual_arm_closing_prior_gates :
    pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
        (rootFrames.compounds rootArmSlot).prior.rule4aKey
        (rootFrames.compounds rootClosingSlot).prior.rule4aKey = .eq ∧
      (compare (rootFrames.compounds rootArmSlot).prior.referenceCountPriority
          (rootFrames.compounds rootClosingSlot).prior.referenceCountPriority = .eq ∧
        (pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bReadings
            (rootFrames.compounds rootArmSlot).prior.readings
            (rootFrames.compounds rootClosingSlot).prior.readings = .eq ∧
          pseudoSpatialCertified.compareLocalizedRerootCompoundRule4cReadings
            (rootFrames.compounds rootArmSlot).prior.readings
            (rootFrames.compounds rootClosingSlot).prior.readings = .eq)) :=
  (pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp
    actual_arm_closing_prior_tie

/-- Rule 5 ranks the `R`-labelled ring carbon above the `S`-labelled one, with the
enantiomorphic signal. -/
theorem actual_arm_closing_throughRule5 :
    pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5
      (rootFrames.compounds rootArmSlot) (rootFrames.compounds rootClosingSlot) =
        { ordering := .gt, pseudo := true } :=
  throughRule5_of_check concrete_arm concrete_closing arm_closing_throughRule5_check

theorem actual_fluorine_arm_prior :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds rootFluorineSlot).prior (rootFrames.compounds rootArmSlot).prior =
        .gt :=
  prior_of_check concrete_fluorine concrete_arm fluorine_arm_prior_check

theorem actual_fluorine_closing_prior :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds rootFluorineSlot).prior
        (rootFrames.compounds rootClosingSlot).prior = .gt :=
  prior_of_check concrete_fluorine concrete_closing fluorine_closing_prior_check

theorem actual_fluorine_hydrogen_prior :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds rootFluorineSlot).prior
        (rootFrames.compounds rootHydrogenSlot).prior = .gt :=
  prior_of_check concrete_fluorine concrete_hydrogen fluorine_hydrogen_prior_check

theorem actual_arm_hydrogen_prior :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds rootArmSlot).prior (rootFrames.compounds rootHydrogenSlot).prior =
        .gt :=
  prior_of_check concrete_arm concrete_hydrogen arm_hydrogen_prior_check

theorem actual_closing_hydrogen_prior :
    pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds rootClosingSlot).prior
        (rootFrames.compounds rootHydrogenSlot).prior = .gt :=
  prior_of_check concrete_closing concrete_hydrogen closing_hydrogen_prior_check

/-! ## Retained keys of the actual root frame -/

private theorem retained_lt_of_throughRule5 {higher lower : Fin 4} {pseudo : Bool}
    (comparison : pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5
      (rootFrames.compounds higher) (rootFrames.compounds lower) =
        { ordering := .gt, pseudo := pseudo }) :
    rootFrames.retainedKeys lower < rootFrames.retainedKeys higher :=
  (completeLigandRule5Key_compare_gt_iff _ _).mp
    ((rootFrames.retainedActual_fullOrdering spatial_simpleBonded higher lower).symm.trans
      (congrArg CertifiedLocalizedCIPInput.ConstitutionalRule5Comparison.ordering comparison))

private theorem retained_prior_lt {higher lower : Fin 4}
    (comparison : pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds higher).prior (rootFrames.compounds lower).prior = .gt) :
    (ofLex (rootFrames.retainedKeys lower)).1 < (ofLex (rootFrames.retainedKeys higher)).1 :=
  (completeLigandPriorKey_compare_gt_iff _ _).mp
    ((rootFrames.retainedActual_priorComparison spatial_simpleBonded higher lower).symm.trans
      comparison)

private theorem retained_prior_eq {left right : Fin 4}
    (comparison : pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
      (rootFrames.compounds left).prior (rootFrames.compounds right).prior = .eq) :
    (ofLex (rootFrames.retainedKeys left)).1 = (ofLex (rootFrames.retainedKeys right)).1 :=
  (completeLigandPriorKey_compare_eq_iff _ _).mp
    ((rootFrames.retainedActual_priorComparison spatial_simpleBonded left right).symm.trans
      comparison)

/-- The actual retained keys strictly descend along the slot order `F, C2, C4, H`. -/
theorem actual_root_retained_order :
    actualRootPriorityOrder.Pairwise
      (fun left right => rootFrames.retainedKeys right < rootFrames.retainedKeys left) := by
  have fluorineArm := retained_lt_of_throughRule5
    (throughRule5_of_prior_gt _ _ actual_fluorine_arm_prior)
  have fluorineClosing := retained_lt_of_throughRule5
    (throughRule5_of_prior_gt _ _ actual_fluorine_closing_prior)
  have fluorineHydrogen := retained_lt_of_throughRule5
    (throughRule5_of_prior_gt _ _ actual_fluorine_hydrogen_prior)
  have armClosing := retained_lt_of_throughRule5 actual_arm_closing_throughRule5
  have armHydrogen := retained_lt_of_throughRule5
    (throughRule5_of_prior_gt _ _ actual_arm_hydrogen_prior)
  have closingHydrogen := retained_lt_of_throughRule5
    (throughRule5_of_prior_gt _ _ actual_closing_hydrogen_prior)
  unfold actualRootPriorityOrder
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ List.Pairwise.nil)))
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact fluorineArm
    · exact fluorineClosing
    · exact fluorineHydrogen
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact armClosing
    · exact armHydrogen
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst slot
    exact closingHydrogen
  · intro slot member
    simp at member

/-- Exactly one unordered pair of actual root ligands, the ring carbons, ties before Rule 5. -/
theorem actual_root_prior_pair_count :
    completeRule5PairCount rootFrames.retainedKeys = 1 := by
  classical
  have symmetric : ∀ first second : Fin 4,
      CompletePriorPair rootFrames.retainedKeys first second →
        CompletePriorPair rootFrames.retainedKeys second first :=
    fun _ _ pair => ⟨pair.1.symm, pair.2.symm⟩
  obtain ⟨_, _, _, armClosingNe, _, _⟩ := actual_root_slots_distinct
  have tie := retained_prior_eq actual_arm_closing_prior_tie
  have fluorineArm := retained_prior_lt actual_fluorine_arm_prior
  have fluorineClosing := retained_prior_lt actual_fluorine_closing_prior
  have fluorineHydrogen := retained_prior_lt actual_fluorine_hydrogen_prior
  have armHydrogen := retained_prior_lt actual_arm_hydrogen_prior
  have closingHydrogen := retained_prior_lt actual_closing_hydrogen_prior
  unfold completeRule5PairCount
  rw [sourceEnantiomorphicPairCount_eq_one_iff _ symmetric]
  refine ⟨rootArmSlot, rootClosingSlot, armClosingNe, ⟨armClosingNe, tie⟩, ?_⟩
  intro first second different pair
  have firstMem : first ∈ actualRootPriorityOrder :=
    actualRootPriorityOrder_perm.mem_iff.mpr (List.mem_finRange first)
  have secondMem : second ∈ actualRootPriorityOrder :=
    actualRootPriorityOrder_perm.mem_iff.mpr (List.mem_finRange second)
  have pairTie := pair.2
  unfold actualRootPriorityOrder at firstMem secondMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMem secondMem
  rcases firstMem with rfl | rfl | rfl | rfl <;> rcases secondMem with rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl different
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩
    | exact absurd pairTie (ne_of_gt fluorineArm)
    | exact absurd pairTie (ne_of_lt fluorineArm)
    | exact absurd pairTie (ne_of_gt fluorineClosing)
    | exact absurd pairTie (ne_of_lt fluorineClosing)
    | exact absurd pairTie (ne_of_gt fluorineHydrogen)
    | exact absurd pairTie (ne_of_lt fluorineHydrogen)
    | exact absurd pairTie (ne_of_gt armHydrogen)
    | exact absurd pairTie (ne_of_lt armHydrogen)
    | exact absurd pairTie (ne_of_gt closingHydrogen)
    | exact absurd pairTie (ne_of_lt closingHydrogen)

/-- The independent complete-root judgment at the actual coordinates and retained keys. -/
theorem actual_root_completeJudgment :
    CompleteRootDescriptorJudgment rootFrames.retainedKeys actualRootPoints
      (.pseudoasymmetric PseudoRS.s) := by
  refine ⟨actualRootPriorityOrder, RS.S, actualRootPriorityOrder_perm,
    actual_root_retained_order, actual_root_geometric_order_is_S, ?_⟩
  rw [actual_root_prior_pair_count]
  rfl

/-- The current generated reference state at the actual root occurrence is lowercase `s`. -/
theorem actual_root_referenceState :
    referenceState pseudoReference rootTarget =
      some (.pseudoasymmetric PseudoRS.s : LocalizedAuxiliaryLabel) :=
  (rootFrames.referenceState_some_iff_retainedJudgment spatial_simpleBonded _).2 (by
    unfold RetainedContextualDescriptorJudgmentAt
    exact ⟨actualRootPoints, actual_root_coordinates, actual_root_completeJudgment⟩)

/-- Endpoint: the actual root state is `s`; it is lowercase because the retained prior-pair count
is one, the physical enantiomorphic pair count of the same root is one, and the raw geometric
letter of the descending slot order is `S`. -/
theorem actual_root_descriptor_endpoint :
    referenceState pseudoReference rootTarget =
        some (.pseudoasymmetric PseudoRS.s : LocalizedAuxiliaryLabel) ∧
      completeRule5PairCount rootFrames.retainedKeys = 1 ∧
      physicalEnantiomorphicPairCount LocalizedCyclicPseudoPhysicalDomain.physicalMolecule
        LocalizedCyclicPseudoPhysicalDomain.physicalCfg
        LocalizedCyclicPseudoPhysicalDomain.rootCenter = 1 ∧
      RationalTetrahedralDescriptor (actualRootPriorityOrder.map actualRootPoints) RS.S :=
  ⟨actual_root_referenceState, actual_root_prior_pair_count, actual_root_physical_pair_count,
    actual_root_geometric_order_is_S⟩

end

end TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.compound_cursor_free
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.concreteCompound_eq_actual
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.arm_references_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.closing_references_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.arm_closing_rule4a_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.arm_closing_prior_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.arm_closing_rule5R_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.arm_closing_rule5S_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.arm_closing_throughRule5_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.fluorine_arm_prior_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.fluorine_closing_prior_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.fluorine_hydrogen_prior_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.arm_hydrogen_prior_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.closing_hydrogen_prior_check
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_ring_carbon_references
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_arm_closing_rule4a_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_arm_closing_rule5_readings
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_arm_closing_prior_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_arm_closing_prior_gates
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_arm_closing_throughRule5
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_root_retained_order
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_root_prior_pair_count
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_root_completeJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_root_referenceState
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoComputableReader.actual_root_descriptor_endpoint
