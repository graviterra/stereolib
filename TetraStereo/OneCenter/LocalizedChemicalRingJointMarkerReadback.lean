import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction
import TetraStereo.OneCenter.LocalizedChemicalRingPromotedFullLabelMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
# Actual joint-key ties preserve labels and every reference on one hierarchy mapping

The actual four-slot comparison supplies all successful builds and sorting information. This
connector derives one common addressing and hierarchy equivalence preserving constitution,
occupancy, the full optional R/S/r/s reader label, and every retained reference simultaneously.
No desired label correspondence, hierarchy map, successful build, or canonicality is assumed.
The finite layout must cover both actual arms. Molecular descent and physical interpretation of
the generated labels remain separate obligations.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReadback

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedSubtreeContext
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointMarkerReconstruction
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedChemicalRingHereditaryTie
open LocalizedChemicalRingActualComparisonLabelMatch LocalizedChemicalRingPromotedFullLabelMatch
open LocalizedChemicalRingPromotedChildMatch

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (references : List input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

/-- The same constructed mapping preserves generated observations and all retained marks. -/
theorem actual_joint_tie_full_readback (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit references W D left =
      refinedKey input single state target real unit targetUnit references W D right) :
    let treeL := slotTree input single state target real unit targetUnit left
    let treeR := slotTree input single state target real unit targetUnit right
    ∃ (matched : MatchedJointMarkerAddressings (ruleMajorTreeGraph treeL) (ruleMajorTreeGraph treeR)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeL)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeR)
        (referenceMarks input references treeL) (referenceMarks input references treeR)
        references.length W D)
      (equiv : AlignedHierarchyEquiv matched.leftAddressing matched.rightAddressing),
      (∀ rule position, observationAt (ruleMajorTreeGraph treeL) (observe treeL)
          matched.leftAddressing rule position =
        observationAt (ruleMajorTreeGraph treeR) (observe treeR) matched.rightAddressing rule position) ∧
      (∀ position, (∃ node, matched.leftAddressing.address node = position) ↔
        (∃ node, matched.rightAddressing.address node = position)) ∧
      (∀ x, rawStateReader input state target (nodeSource input treeL x) =
        rawStateReader input state target (nodeSource input treeR (equiv.toEquiv x))) ∧
      (∀ x index, index < references.length →
        (referenceMarks input references treeL x).getD index 0 =
          (referenceMarks input references treeR (equiv.toEquiv x)).getD index 0) := by
  dsimp only
  let descriptorMap := rawStateDescriptorMap input state
  let frame := frames input single state target real unit targetUnit
  have realTree (slot : Fin 4) :=
    LocalizedRuleMajorSortTrace.realizes_of_trace (frame.stages slot).a.trace
  have rootChild (slot : Fin 4) : (frame.stages slot).a.tree.source ∈
      input.executableLocalizedRerootChildren ⟨target, none⟩ := by
    rw [(frame.stages slot).a.sourceEq]
    exact frame.childAt slot
  have ordinary : frame.retainedKeys unit left = frame.retainedKeys unit right :=
    congrArg (fun value : RefinedKey => (ofLex value).1) tie
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral input state) single unit targetUnit left right
  rw [ordinary, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have markers :
      (compiled input single state target real unit targetUnit references W D left).markers =
        (compiled input single state target real unit targetUnit references W D right).markers :=
    congrArg (fun value : RefinedKey => (ofLex value).2) tie
  have jointTie : compareJointKeys input
      (compiled input single state target real unit targetUnit references W D left)
      (compiled input single state target real unit targetUnit references W D right) = .eq := by
    unfold compareJointKeys
    rw [compiled_prior input single state target real unit targetUnit references W D left,
      compiled_prior input single state target real unit targetUnit references W D right,
      full, markers]
    simp
  have built (slot : Fin 4) :
      buildJoint? input target (input.molecularView descriptorMap target) references W D
        (2 * (retainedCarrierFuel input + 1)) (frame.stages slot).a.tree.source =
      some (compiled input single state target real unit targetUnit references W D slot) := by
    rw [(frame.stages slot).a.sourceEq]
    simpa only [rawStateView_eq_molecularView] using
      compiled_built input single state target real unit targetUnit references W D slot
  obtain ⟨matched, equiv, constitution, occupied, marks, _⟩ :=
    joint_built_tie_reconstruction input descriptorMap target fallback references W D
      (frame.stages left).a.trace (frame.stages right).a.trace (realTree left) (realTree right)
      (rawStateDescriptorMap_tetrahedral input state) single (rootChild left) (rootChild right)
      _ _ (built left) (built right) jointTie widthL heightL widthR heightR
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit left)).declarativeAddressing
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit right)).declarativeAddressing
  refine ⟨matched, equiv, constitution, occupied, ?_, fun x index bound => marks index bound x⟩
  intro x
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
    matched.prior_sorted.1 matched.prior_sorted.2 roots x (equiv.toEquiv x) (equiv.aligns x).symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReadback.actual_joint_tie_full_readback
