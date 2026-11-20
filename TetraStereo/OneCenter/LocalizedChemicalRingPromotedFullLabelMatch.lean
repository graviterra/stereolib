import TetraStereo.OneCenter.LocalizedChemicalRingPromotedChildMatch
import TetraStereo.OneCenter.LocalizedChemicalRingAddressInduction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! Actual refined-key ties preserve complete reader labels at the same promoted addresses
that preserve constitution and reference membership. No auxiliary-label correspondence is
assumed. This is an occurrence-level result; descending it to one physical molecular symmetry
and proving that symmetry proper remain separate obligations. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotedFullLabelMatch

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPromotedColorReadback
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedChemicalRingHereditaryTie
open LocalizedChemicalRingPromotedChildMatch LocalizedChemicalRingAddressInduction
open LocalizedChemicalRingActualFullLabelMatch LocalizedChemicalRingActualComparisonLabelMatch

noncomputable section
open scoped Classical

theorem labels_at_matching_addresses
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realL : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) treeL)
    (realR : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) treeR)
    {P Q : Type*} [LinearOrder P] [LinearOrder Q]
    (priorL : (ruleMajorTreeGraph treeL).Node → P) (priorR : (ruleMajorTreeGraph treeR).Node → Q)
    (agreeL : SiblingPriorAgreement input target view treeL priorL)
    (agreeR : SiblingPriorAgreement input target view treeR priorR)
    (addressL : (ruleMajorTreeGraph treeL).Addressing) (addressR : (ruleMajorTreeGraph treeR).Addressing)
    (denseL : Dense addressL) (denseR : Dense addressR)
    (sortedL : KeySorted priorL addressL) (sortedR : KeySorted priorR addressR)
    (roots : RebuildMatch target view treeL.source treeR.source)
    (x : (ruleMajorTreeGraph treeL).Node) (y : (ruleMajorTreeGraph treeR).Node)
    (address : addressL.address x = addressR.address y) :
    input.localizedDependencyLabel target view (nodeSource input treeL x) =
      input.localizedDependencyLabel target view (nodeSource input treeR y) := by
  have roots' : RebuildMatch target view (nodeSource input treeL (ruleMajorTreeGraph treeL).root)
      (nodeSource input treeR (ruleMajorTreeGraph treeR).root) := by
    simpa only [nodeSource_root] using roots
  have pair := related_of_address_eq (ruleMajorTreeGraph treeL) (ruleMajorTreeGraph treeR)
    addressL addressR denseL denseR
    (fun a b => RebuildMatch target view (nodeSource input treeL a) (nodeSource input treeR b))
    roots' (matched_orderedChildren target view treeL treeR realL realR priorL priorR agreeL agreeR
      addressL addressR denseL denseR sortedL sortedR) x y address
  obtain ⟨left, right, builtL, builtR, tie⟩ := pair
  exact full_tie_root_labels _ _ _ _ _ _ _ _ builtL builtR
    (congrArg ConstitutionalRule5Comparison.ordering tie)

section Actual

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

/-- The actual refined keys construct a single correspondence preserving constitutional
observations, occupied positions, full optional R/S/r/s labels, and the reference marker.
The auxiliary state is arbitrary, so the result applies to the evaluator's generated state. -/
theorem actual_tie_joint_full_label_readback (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right) :
    let treeL := slotTree input single state target real unit targetUnit left
    let treeR := slotTree input single state target real unit targetUnit right
    ∃ matched : MatchedMarkerAddressings (ruleMajorTreeGraph treeL) (ruleMajorTreeGraph treeR)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeL)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeR)
        (referenceMark input reference treeL) (referenceMark input reference treeR) W D,
      (∀ rule position, observationAt (ruleMajorTreeGraph treeL) (observe treeL)
          matched.leftAddressing rule position =
        observationAt (ruleMajorTreeGraph treeR) (observe treeR) matched.rightAddressing rule position) ∧
      (∀ position, (∃ node, matched.leftAddressing.address node = position) ↔
        (∃ node, matched.rightAddressing.address node = position)) ∧
      (∀ x y, matched.leftAddressing.address x = matched.rightAddressing.address y →
        rawStateReader input state target (nodeSource input treeL x) =
          rawStateReader input state target (nodeSource input treeR y) ∧
        referenceMark input reference treeL x = referenceMark input reference treeR y) := by
  dsimp only
  obtain ⟨matched, constitution, occupied⟩ := actual_tie_joint_readback input single state target real
    unit targetUnit reference W D fallback left right widthL heightL widthR heightR tie
  refine ⟨matched, constitution, occupied, ?_⟩
  intro x y address
  refine ⟨?_, matched.marks_eq x y address⟩
  let descriptorMap := rawStateDescriptorMap input state
  let frame := frames input single state target real unit targetUnit
  have realTree (slot : Fin 4) := LocalizedRuleMajorSortTrace.realizes_of_trace (frame.stages slot).a.trace
  have rootChild (slot : Fin 4) : (frame.stages slot).a.tree.source ∈
      input.executableLocalizedRerootChildren ⟨target, none⟩ := by
    rw [(frame.stages slot).a.sourceEq]
    exact frame.childAt slot
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral input state) single unit targetUnit left right
  have ordinary : frame.retainedKeys unit left = frame.retainedKeys unit right :=
    congrArg (fun value : RefinedKey => (ofLex value).1) tie
  rw [ordinary, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have roots : RebuildMatch target (input.molecularView descriptorMap target)
      (frame.stages left).a.tree.source (frame.stages right).a.tree.source := by
    refine ⟨frame.compounds left, frame.compounds right,
      frame_uniform_built descriptorMap target frame left,
      frame_uniform_built descriptorMap target frame right, ?_⟩
    exact through_tie_of_ordering_eq input _ _ full
  simp only [rawStateReader_eq_molecularReader]
  exact labels_at_matching_addresses target (input.molecularView descriptorMap target)
    (frame.stages left).a.tree (frame.stages right).a.tree (realTree left) (realTree right)
    _ _
    (deepPrior_agreement descriptorMap target fallback _ (realTree left)
      (rawStateDescriptorMap_tetrahedral input state) single (rootChild left))
    (deepPrior_agreement descriptorMap target fallback _ (realTree right)
      (rawStateDescriptorMap_tetrahedral input state) single (rootChild right))
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1 matched.rightCanonical.1
    matched.prior_sorted.1 matched.prior_sorted.2 roots x y address

end Actual
end
end TetraStereo.OneCenter.LocalizedChemicalRingPromotedFullLabelMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedFullLabelMatch.labels_at_matching_addresses
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedFullLabelMatch.actual_tie_joint_full_label_readback
