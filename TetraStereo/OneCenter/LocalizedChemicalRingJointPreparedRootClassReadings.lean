import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPromotionCancellation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Actual root promotion readings within a key class

Absent an odd boundary symmetry, two root ligands with equal actual generated keys have
equal actual extended-context fallback readings. The molecular symmetry, its evenness and
the fallback transport are derived. This does not require equality of readings in different
key classes or assume that any selected fallback resolves.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootClassReadings

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry referenceAt)
open LocalizedChemicalRingJointPreparedExecution (generated fallback keys)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots slotKeys slotOrder slotAdjacent)
open LocalizedChemicalRingJointPreparedRootPromotionCancellation
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedGenericMarkedRecalculation (consensus)
open DeclarativeCIP.ProductionOccurrenceRules456 (promotionAggregate)
open LocalizedChemicalRingJointPreparedPromotionOutcomes (actualOutcomes actualReadings)
open LocalizedChemicalRingOrderingTransport (tiedEntries_mem tiedEntries_sublist)
open LocalizedChemicalRingJointMarkerRanking (refined_compare_eq_iff)
open LocalizedMarkedRetainedOrdinaryRanking (keyOrder_perm keyOrder_pairwise)

noncomputable section
open scoped Classical

/-- The actual selected population contains each slot at most once. -/
theorem selectedSlots_nodup (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (single : input.moleculeGraph.SimpleBonded) (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (state : OccurrenceAuxState) (references : List input.Atom) :
    (selectedSlots input mol single c node data state references).Nodup := by
  exact (tiedEntries_sublist false _ _).nodup
    ((keyOrder_perm _ _).nodup_iff.mpr (List.nodup_finRange 4))

/-- Each actual selected slot has a distinct selected partner in its own current key class. -/
theorem selectedSlots_partner (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (single : input.moleculeGraph.SimpleBonded) (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (state : OccurrenceAuxState) (references : List input.Atom) (i : Fin 4)
    (member : i ∈ selectedSlots input mol single c node data state references) :
    ∃ j ∈ selectedSlots input mol single c node data state references,
      j ≠ i ∧ slotKeys input mol single c node data state references j =
        slotKeys input mol single c node data state references i := by
  let key := slotKeys input mol single c node data state references
  have membership (i : Fin 4) :
      i ∈ selectedSlots input mol single c node data state references ↔
        i ∈ slotOrder input mol single c node data state references ∧
          ∃ j ∈ slotOrder input mol single c node data state references, j ≠ i ∧ key j = key i :=
    tiedEntries_mem compare refined_compare_eq_iff key _
      ((keyOrder_perm _ _).nodup_iff.mpr (List.nodup_finRange 4)) (keyOrder_pairwise _ _) i
  obtain ⟨inOrder, j, jOrder, distinct, equal⟩ := (membership i).mp member
  exact ⟨j, (membership j).mpr ⟨jOrder, i, inOrder, Ne.symm distinct, equal.symm⟩,
    distinct, equal⟩

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported charge calibrated in
/-- Actual same-key root slots have identical actual fallback readings when no odd boundary
symmetry exists. The retained reference list and reflected-side context are unchanged. -/
theorem fallback_eq_of_root_key_eq
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (noOdd : ¬ OddBoundarySymmetry input cfg c [] references) (i j : Fin 4)
    (tie : keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references i =
      keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references j) :
    fallback input mol c node data (structuralDepth mol node)
        (observedGeometry input reflected) references i =
      fallback input mol c node data (structuralDepth mol node)
        (observedGeometry input reflected) references j := by
  by_cases same : i = j
  · subst j
    rfl
  obtain ⟨e, fixed, moved, keeps, proper⟩ := root_tie_boundaryProper input mol agreement
    admissible supported single charge cfg calibrated c node data reached rootAddress current
    references reflected i j same tie
  have history : data.target.1.node.history = [c.1] :=
    root_history input mol c node data rootAddress current
  have centerFixed : input.detectedMultiCenterMolecule.centerPerm e c = c :=
    Subtype.ext (fixed c.1 (by simp [history]))
  have even : relativeSign input.detectedMultiCenterMolecule cfg e c = 1 := by
    rcases relativeSign_eq_one_or_neg_one input.detectedMultiCenterMolecule cfg e c with even | odd
    · exact even
    · apply False.elim
      apply noOdd
      refine ⟨e, ?_, keeps, odd, ?_⟩
      · intro atom member
        apply fixed atom
        simpa [history] using member
      · intro d outside
        apply proper d
        simpa [history] using outside
  have action : slotAction input mol e c node data i = j := by
    apply data.ligandOf.injective
    apply input.detectedMultiCenterMolecule.ligandAtomAt_injective c
    exact (referenceAt_action input mol e c node data centerFixed i).trans moved
  have transported := root_even_fallback_action input mol agreement admissible supported single
    cfg calibrated c node data reached current rootAddress references e fixed keeps proper even
    (structuralDepth mol node) reflected i
  rw [action] at transported
  exact transported.symm

include agreement admissible supported charge calibrated in
/-- Every actual four-way root tie satisfies the cancellation equation, including when all
promotions remain unresolved. No orbit, common-reading or oddness assumption is supplied. -/
theorem actualAggregate_eq_consensus_of_constant_root_keys
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (constant : ∀ i, keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references i =
      keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references 0) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (consensus (actualReadings input mol single c node data (structuralDepth mol node)
        references reflected)) := by
  by_cases odd : OddBoundarySymmetry input cfg c [] references
  · exact actualAggregate_eq_consensus_of_rootOddBoundary input mol agreement admissible supported
      single cfg calibrated c node data reached current rootAddress references reflected odd
  · have tied : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references) := by
      intro injective
      have different : (1 : Fin 4) ≠ 0 := by decide
      exact different (injective (constant 1))
    apply actualAggregate_eq_consensus_of_uniform_readings input mol agreement admissible supported
      single cfg calibrated c node data (structuralDepth mol node) references reflected tied
      (fallback input mol c node data (structuralDepth mol node)
        (observedGeometry input reflected) references 0)
    intro i _
    exact fallback_eq_of_root_key_eq input mol agreement admissible supported single charge cfg
      calibrated c node data reached current rootAddress references reflected odd i 0 (constant i)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootClassReadings

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootClassReadings.selectedSlots_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootClassReadings.selectedSlots_partner
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootClassReadings.fallback_eq_of_root_key_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootClassReadings.actualAggregate_eq_consensus_of_constant_root_keys
