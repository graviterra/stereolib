import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyCovariance
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootCancellationAssembly
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Resolution of the actual selected promotions at nonconstant roots without an odd boundary.
An extended-context tie would fix the promoted atom while moving another pair. Full current-key
covariance and the selected stabilizer exclude that residual symmetry. The existing cancellation
assembly consequently has no remaining selected-resolution argument.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSelectedResolution

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (keys generated fallback step fallback_none_iff)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots)
open LocalizedChemicalRingJointPreparedRootClassReadings (selectedSlots_partner)
open LocalizedChemicalRingJointPreparedRootPromotionCancellation (root_tie_boundaryProper)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingJointPreparedRootKeyCovariance (root_current_key_action)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedGenericMarkedRecalculation (structuralDepth consensus)
open LocalizedChemicalRingJointPreparedPromotionOutcomes (actualOutcomes actualReadings)
open DeclarativeCIP.ProductionOccurrenceRules456 (promotionAggregate)

noncomputable section
open scoped Classical

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
/-- Every actually selected fallback resolves in the nonconstant/no-odd root case. -/
theorem selected_fallback_resolves
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (noOdd : ¬ OddBoundarySymmetry input cfg c [] references)
    (nonconstant : ¬ ∀ i, keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references i =
      keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references 0)
    (slot : Fin 4)
    (selected : slot ∈ selectedSlots input mol single c node data
      (generated input mol (structuralDepth mol node) (observedGeometry input reflected)
        node references) references) :
    fallback input mol c node data (structuralDepth mol node)
      (observedGeometry input reflected) references slot ≠ none := by
  intro failed
  have residualTie := (fallback_none_iff input mol agreement admissible supported single c node data
    (structuralDepth mol node) references cfg (calibrated c) reflected slot).mp failed
  apply residualTie
  intro left right tie
  by_contra distinct
  obtain ⟨e, fixed, moved, keeps, proper⟩ := root_tie_boundaryProper input mol agreement
    admissible supported single charge cfg calibrated c node data reached rootAddress current
    (references ++ [referenceAt input mol c node data slot]) reflected left right distinct tie
  have oldKept : ∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom := by
    intro atom member
    exact keeps atom (List.mem_append_left _ member)
  have selectedKept : (e : Equiv.Perm input.Atom) (referenceAt input mol c node data slot) =
      referenceAt input mol c node data slot :=
    keeps _ (List.mem_append_right _ (by simp))
  have history : data.target.1.node.history = [c.1] :=
    root_history input mol c node data rootAddress current
  have centerFixed : input.detectedMultiCenterMolecule.centerPerm e c = c :=
    Subtype.ext (fixed c.1 (by simp [history]))
  have even : relativeSign input.detectedMultiCenterMolecule cfg e c = 1 := by
    rcases relativeSign_eq_one_or_neg_one input.detectedMultiCenterMolecule cfg e c with even | odd
    · exact even
    · exact False.elim (noOdd ⟨e,
        (by intro atom member; apply fixed atom; simpa [history] using member), oldKept,
        odd, (by intro d outside; apply proper d; simpa [history] using outside)⟩)
  let p := slotAction input mol e c node data
  have slotEven : permHandedness p = 1 := by
    have compose : p = data.ligandOf⁻¹ *
        input.detectedMultiCenterMolecule.ligandPermAt e c * data.ligandOf := by
      ext i
      rfl
    rw [compose, permHandedness_conj_inv,
      ← LocalizedChemicalRingCompletenessOrbit.relativeSign_fixed input cfg e c centerFixed]
    exact even
  have fixes : p slot = slot := by
    apply data.ligandOf.injective
    apply input.detectedMultiCenterMolecule.ligandAtomAt_injective c
    exact (referenceAt_action input mol e c node data centerFixed slot).trans selectedKept
  have preserves := root_current_key_action input mol agreement admissible supported single cfg
    calibrated c node data reached current rootAddress e fixed references oldKept proper
    (structuralDepth mol node) reflected
  obtain ⟨partner, _, different, sameKey⟩ := selectedSlots_partner input mol single c node data
    (generated input mol (structuralDepth mol node) (observedGeometry input reflected)
      node references) references slot selected
  have allEqualImpossible : ¬ ∀ i, keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references i =
      keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references slot := by
    intro allEqual
    apply nonconstant
    intro i
    exact (allEqual i).trans (allEqual 0).symm
  have identity := LocalizedChemicalRingSelectedStabilizer.selected_even_stabilizer_eq_one
    (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references) p slot partner fixes slotEven preserves
    different sameKey allEqualImpossible
  have action : p left = right := by
    apply data.ligandOf.injective
    apply input.detectedMultiCenterMolecule.ligandAtomAt_injective c
    exact (referenceAt_action input mol e c node data centerFixed left).trans moved
  rw [identity, Equiv.Perm.one_apply] at action
  exact distinct action

include agreement admissible supported charge calibrated in
/-- Actual cancellation and consensus agree at every root, including all refusal cases. -/
theorem actualAggregate_eq_consensus_of_root
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (consensus (actualReadings input mol single c node data (structuralDepth mol node)
        references reflected)) :=
  LocalizedChemicalRingJointPreparedRootCancellationAssembly.actualAggregate_eq_consensus_of_root_resolution
    input mol agreement admissible supported single charge cfg calibrated c node data reached
    current rootAddress references reflected
    (selected_fallback_resolves input mol agreement admissible supported single charge cfg calibrated
      c node data reached current rootAddress references reflected)

include agreement admissible supported charge calibrated in
/-- Nonstrict root execution satisfies cancellation without a supplied resolution or balance. -/
theorem actualAggregate_eq_step_of_root_tied
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references)) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (step input mol node (structuralDepth mol node)
        (observedGeometry input reflected) references) :=
  LocalizedChemicalRingJointPreparedRootCancellationAssembly.actualAggregate_eq_step_of_root_resolution
    input mol agreement admissible supported single charge cfg calibrated c node data reached
    current rootAddress references reflected tied
    (selected_fallback_resolves input mol agreement admissible supported single charge cfg calibrated
      c node data reached current rootAddress references reflected)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSelectedResolution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSelectedResolution.selected_fallback_resolves
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSelectedResolution.actualAggregate_eq_consensus_of_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSelectedResolution.actualAggregate_eq_step_of_root_tied
