import TetraStereo.OneCenter.LocalizedActualRule4aTableBridge
import TetraStereo.OneCenter.LocalizedActualRule4aNodeReadback
import TetraStereo.OneCenter.DeclarativeCIPObservedKeyProjection
import TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeOrder
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeBuilder
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! The stage-4a sparse-table comparison bridge for observer-parametric contextual keys.

This file transports the existing sparse table comparison algebra to `ruleKeyWithObservations`.
The observer is an explicit independent function; representation hypotheses connect its keys
to the actual matched tables. Realized-tree induction discharges those hypotheses downstream. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

noncomputable section
open scoped Classical
open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

private theorem contextualScalar4a_eq_projectZero {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCumulativeRule45Key) :
    Rule4aTableBridge.scalar4a key = projectCumulative 0 key.descriptor := by
  unfold Rule4aTableBridge.scalar4a Rule4aTableBridge.sparseEntryMap projectCumulative
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro entry _
  cases entry.2 <;> rfl

/-- A stage-4a key's old actual comparator is precisely the whole-rule width-one comparator.
The scalar table identity is the existing sparse-table payload-map theorem. -/
theorem compareRule4aOld_eq_ruleMajor_one {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {treeI treeJ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    (matchI : LocalizedCumulativeTreeTableMatch .rule4a treeI keyI)
    (matchJ : LocalizedCumulativeTreeTableMatch .rule4a treeJ keyJ) :
    input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ =
      input.compareRuleMajorCumulativeDescriptor 1 keyI keyJ := by
  have scalarI := Rule4aTableBridge.scalar4a_eq_table matchI
  have scalarJ := Rule4aTableBridge.scalar4a_eq_table matchJ
  have col : input.compareRuleMajorCumulativeColumnTables 1 keyI keyJ =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (Rule4aTableBridge.scalar4a keyI) (Rule4aTableBridge.scalar4a keyJ) := by
    unfold compareRuleMajorCumulativeColumnTables ruleMajorCumulativeColumns
    simp only [List.range_one, List.map_cons, List.map_nil,
      List.compareLex_cons_cons, List.compareLex_nil_nil]
    rw [← contextualScalar4a_eq_projectZero keyI, ← contextualScalar4a_eq_projectZero keyJ]
    cases c : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (Rule4aTableBridge.scalar4a keyI) (Rule4aTableBridge.scalar4a keyJ) <;>
      simp [Ordering.then]
  rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumnsFunction]
  simp only [compareLocalizedRerootCumulativeRule45Keys, compareLex, Ordering.byKey]
  rw [Rule4aTableBridge.compare_descriptor_eq_scalar matchI matchJ, col]

/-- The observed stereochemical path is nonbottom exactly on the shared constitutional support.
No evidence mask is required: a bottom label is still a present stereochemical observation. -/
theorem observedStereoNodePathObservation_eq_bot_iff
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (graph : RootedDigraph Atom) (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph) (rule : StereochemicalRule) (W D : Nat) :
    ∀ (path : List Nat) (node : graph.Node),
      observedStereoNodePathObservation graph observe evidence W D rule node path = ⊥ ↔
        nodePathObservationWithObservations graph observe W D 0 node path = ⊥ := by
  intro path
  induction path with
  | nil => intro node; rw [observedStereoNodePathObservation_nil,
      nodePathObservationWithObservations_nil (graph := graph) (observe := observe)
        (W := W) (D := D) (r := 0) (by omega) node]; simp
  | cons digit path ih =>
      intro node
      obtain ⟨ranked, hperm, hsorted⟩ :=
        exists_observedOrdinaryRanked graph observe evidence W D node
      rw [observedStereoNodePathObservation_cons graph observe evidence W D rule node hperm hsorted,
        nodePathObservationWithObservations_cons (graph := graph) (observe := observe)
          (W := W) (D := D) (r := 0) (by omega) node hperm
          (observedRuleKey_sorted_of_ordinary_sorted graph observe evidence W D hsorted)]
      by_cases guard : digit < W ∧ path.length < D
      · rw [if_pos guard, if_pos guard]
        cases ranked[digit]? with
        | none => simp
        | some child =>
            simp only [Option.map_some, Option.getD_some]
            exact ih child
      · rw [if_neg guard, if_neg guard]
        simp

/-- At the root, an observed Rule-4a label matching the actual priority code is the
stage-4a table's encoded observation. -/
theorem observedStereoNodePathObservation_nil_eq_encoded4a
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (graph : RootedDigraph Atom) (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph) (W D : Nat)
    (node : graph.Node) {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (stereoEq : stereoLabel graph evidence .rule4aStereogenicUnitKind node =
      (code (prio4a tree) : StereoLabel)) :
    observedStereoNodePathObservation graph observe evidence W D
      .rule4aStereogenicUnitKind node [] = encoded4a key [] := by
  rw [observedStereoNodePathObservation_nil, stereoEq, encoded4a_nil tableMatch realizes]

/-- Under a constitutional representation and Rule-4a path representation, the actual width-one
rule-major comparison orders the corresponding observed pair keys. -/
theorem observedPairKey_le_of_ruleMajor_compare_ne_lt
    {input : CertifiedLocalizedCIPInput} [Fintype input.Atom] [DecidableEq input.Atom]
    {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {graph : RootedDigraph input.Atom} (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph)
    {treeI treeJ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    (matchI : LocalizedCumulativeTreeTableMatch .rule4a treeI keyI)
    (matchJ : LocalizedCumulativeTreeTableMatch .rule4a treeJ keyJ)
    (realizesI : LocalizedCumulativeTreeRealizes input read treeI)
    (realizesJ : LocalizedCumulativeTreeRealizes input read treeJ)
    {W D : Nat} {nodeI nodeJ : graph.Node}
    (repI : Represents W D (ruleKeyWithObservations graph W D observe nodeI) keyI.constitutional)
    (repJ : Represents W D (ruleKeyWithObservations graph W D observe nodeJ) keyJ.constitutional)
    (rep4I : Represents4a W D
      (observedRule4aComponent graph observe evidence W D nodeI) keyI)
    (rep4J : Represents4a W D
      (observedRule4aComponent graph observe evidence W D nodeJ) keyJ)
    (hne : input.compareRuleMajorCumulativeDescriptor 1 keyI keyJ ≠ Ordering.lt) :
    observedPairKey graph observe evidence W D nodeJ ≤
      observedPairKey graph observe evidence W D nodeI := by
  have oldNe : input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ ≠ Ordering.lt := by
    rw [compareRule4aOld_eq_ruleMajor_one matchI matchJ]
    exact hne
  have wfI := wellFormedRuleMajorKey_of_tableMatch matchI realizesI
  have wfJ := wellFormedRuleMajorKey_of_tableMatch matchJ realizesJ
  have hconst : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional =
      compare (ruleKeyWithObservations graph W D observe nodeI)
        (ruleKeyWithObservations graph W D observe nodeJ) :=
    compare_eq_compare_vector wfI wfJ
      (ruleKeyWithObservations_vectorWellShaped (graph := graph) (observe := observe) W D nodeI)
      (ruleKeyWithObservations_vectorWellShaped (graph := graph) (observe := observe) W D nodeJ) repI repJ
  unfold observedPairKey
  rcases h : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional with _ | _ | _
  · exfalso
    apply oldNe
    simp [compareLocalizedRerootCumulativeRule45Keys, compareLex, Ordering.byKey, h]
  · have veq : ruleKeyWithObservations graph W D observe nodeI =
        ruleKeyWithObservations graph W D observe nodeJ :=
      (vectorCompare_eq_iff _ _).1 (hconst.symm.trans h)
    have rule1aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        keyI.constitutional.rule1a keyJ.constitutional.rule1a = Ordering.eq := by
      unfold OfficialRuleMajorKey.compare at h
      exact (compareLex_eq_eq.1 h).1
    have hdesc : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        keyI.descriptor keyJ.descriptor ≠ Ordering.lt := by
      have oldNe' := oldNe
      unfold compareLocalizedRerootCumulativeRule45Keys at oldNe'
      simpa [compareLex, Ordering.byKey, h] using oldNe'
    rw [Rule4aTableBridge.compare_descriptor_eq_compare_key matchI matchJ realizesI realizesJ
      rule1aTie
      (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
        .rule4aStereogenicUnitKind nodeI)
      (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
        .rule4aStereogenicUnitKind nodeJ)
      rep4I rep4J] at hdesc
    have hle : observedRule4aComponent graph observe evidence W D nodeJ ≤
        observedRule4aComponent graph observe evidence W D nodeI :=
      not_lt.1 fun hlt => hdesc ((stereoKeyCompare_lt_iff _ _).2 hlt)
    rw [Prod.Lex.le_iff]
    exact Or.inr ⟨veq.symm, hle⟩
  · have hgt : ruleKeyWithObservations graph W D observe nodeJ <
        ruleKeyWithObservations graph W D observe nodeI :=
      (vectorCompare_gt_iff _ _).1 (hconst.symm.trans h)
    rw [Prod.Lex.le_iff]
    exact Or.inl hgt

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareRule4aOld_eq_ruleMajor_one
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedStereoNodePathObservation_eq_bot_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedStereoNodePathObservation_nil_eq_encoded4a
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedPairKey_le_of_ruleMajor_compare_ne_lt
