import TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveReport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSelectedResolution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact success/refusal for nontransitive roots with at most one moving physical class.
The independent class condition prevents cross-class cancellation. Together with absence of
odd physical symmetry it suffices for both actual geometry readings, without assumed labels,
fallback resolution or pairwise proper distinguishability. Published policy fidelity and
absolute-letter/casing interpretation remain separate obligations. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootSingleMovingClass

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRootPhysicalKeyClasses (PhysicalTransport keys_eq_iff_physicalTransport)
open LocalizedChemicalRingRootTransitiveClassification
  (PhysicalTransitive constant_keys_iff_physicalTransitive)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (generated keys fallback step)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots selectedSlots_nonempty)
open LocalizedChemicalRingJointPreparedRootClassReadings
  (selectedSlots_partner fallback_eq_of_root_key_eq)
open LocalizedChemicalRingJointPreparedRootSelectedResolution (selected_fallback_resolves)
open LocalizedChemicalRingJointPreparedRefusalCharacterization
  (OddBoundarySymmetry refusal_of_oddBoundary)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingJointPreparedRootInput (root_data root_reached)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointPreparedReport (analyze mem_analyze_at_center_iff)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- Any two ligands which can move to a different ligand belong to the same physical class.
This permits an entirely fixed action, and excludes two separate moving classes. -/
def SingleMovingClass (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center) (references : List input.Atom) : Prop :=
  ∀ left left' right right' : Fin 4, left ≠ left' → right ≠ right' →
    PhysicalTransport input cfg c references left left' →
    PhysicalTransport input cfg c references right right' → left ≠ right →
    PhysicalTransport input cfg c references left right

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
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
  (references : List input.Atom)

include agreement admissible supported single charge calibrated reached current rootAddress in
/-- The independent class condition puts every selected promotion in the same actual key class. -/
theorem selected_keys_eq_of_singleMovingClass
    (oneClass : SingleMovingClass input cfg c references) (reflected : Bool)
    (left right : Fin 4)
    (leftSelected : left ∈ selectedSlots input mol single c node data
      (generated input mol (structuralDepth mol node) (observedGeometry input reflected) node references)
      references)
    (rightSelected : right ∈ selectedSlots input mol single c node data
      (generated input mol (structuralDepth mol node) (observedGeometry input reflected) node references)
      references) :
    keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references left =
      keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references right := by
  by_cases same : left = right
  · simp only [same]
  obtain ⟨left', _, leftDifferent, leftTied⟩ := selectedSlots_partner input mol single c node data
    (generated input mol (structuralDepth mol node) (observedGeometry input reflected) node references)
    references left leftSelected
  obtain ⟨right', _, rightDifferent, rightTied⟩ := selectedSlots_partner input mol single c node data
    (generated input mol (structuralDepth mol node) (observedGeometry input reflected) node references)
    references right rightSelected
  have physicalLeft := (keys_eq_iff_physicalTransport input mol agreement admissible supported single
    charge cfg calibrated c node data reached current rootAddress references reflected
    left left' (Ne.symm leftDifferent)).mp leftTied.symm
  have physicalRight := (keys_eq_iff_physicalTransport input mol agreement admissible supported single
    charge cfg calibrated c node data reached current rootAddress references reflected
    right right' (Ne.symm rightDifferent)).mp rightTied.symm
  apply (keys_eq_iff_physicalTransport input mol agreement admissible supported single charge cfg
    calibrated c node data reached current rootAddress references reflected left right same).mpr
  exact oneClass _ _ _ _
    (fun h => leftDifferent (data.ligandOf.injective h).symm)
    (fun h => rightDifferent (data.ligandOf.injective h).symm)
    physicalLeft physicalRight (fun h => same (data.ligandOf.injective h))

include agreement admissible supported single charge calibrated reached current rootAddress in
/-- The actual raw step succeeds on either geometry under the independent physical conditions. -/
theorem step_ne_none_of_singleMovingClass
    (oneClass : SingleMovingClass input cfg c references)
    (nontransitive : ¬ PhysicalTransitive input cfg c references)
    (noOdd : ¬ OddBoundarySymmetry input cfg c [] references) (reflected : Bool) :
    step input mol node (structuralDepth mol node) (observedGeometry input reflected)
      references ≠ none := by
  rw [LocalizedChemicalRingJointPreparedExecution.step_eq input mol agreement admissible supported
    single c node data (structuralDepth mol node)]
  by_cases inj : Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references)
  · rw [if_pos inj]
    obtain ⟨value, computed⟩ := LocalizedChemicalRingInheritedRefusalCases.readback_some input cfg c
      (calibrated c) reflected (LocalizedChemicalRingInheritedRefusalCases.rank input mol c node data
        (keys input mol single c node data (structuralDepth mol node)
          (observedGeometry input reflected) references))
    rw [computed]
    exact Option.some_ne_none value
  · rw [if_neg inj]
    have nonempty := selectedSlots_nonempty input mol single c node data
      (generated input mol (structuralDepth mol node) (observedGeometry input reflected) node references)
      references inj
    obtain ⟨slot, selected⟩ := List.exists_mem_of_ne_nil _ nonempty
    have nonconstant : ¬ ∀ i, keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references i =
      keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references 0 := by
      intro constant
      exact nontransitive ((constant_keys_iff_physicalTransitive input mol agreement admissible
        supported single charge cfg calibrated c node data reached current rootAddress references
        reflected).mp constant)
    have resolved := selected_fallback_resolves input mol agreement admissible supported single
      charge cfg calibrated c node data reached current rootAddress references reflected noOdd
      nonconstant slot selected
    cases found : fallback input mol c node data (structuralDepth mol node)
        (observedGeometry input reflected) references slot with
    | none => exact False.elim (resolved found)
    | some value =>
        have all (other : Fin 4) (member : other ∈ selectedSlots input mol single c node data
            (generated input mol (structuralDepth mol node) (observedGeometry input reflected)
              node references) references) :
            fallback input mol c node data (structuralDepth mol node)
              (observedGeometry input reflected) references other = some value := by
          have tied := selected_keys_eq_of_singleMovingClass input mol agreement admissible supported
            single charge cfg calibrated c node data reached current rootAddress references oneClass
            reflected other slot member selected
          exact (fallback_eq_of_root_key_eq input mol agreement admissible supported single charge cfg
            calibrated c node data reached current rootAddress references reflected noOdd other slot
            tied).trans found
        rw [LocalizedChemicalRingCompletenessMarked.consensus_map_const _ nonempty _ value all]
        exact Option.some_ne_none value

include agreement admissible supported single charge calibrated reached current rootAddress in
/-- Exhaustive descriptor refusal criterion for nontransitive roots with one moving class. -/
theorem descriptor_none_iff_oddBoundary
    (oneClass : SingleMovingClass input cfg c references)
    (nontransitive : ¬ PhysicalTransitive input cfg c references) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = none ↔
    OddBoundarySymmetry input cfg c [] references := by
  constructor
  · intro refused
    by_contra noOdd
    have original := step_ne_none_of_singleMovingClass input mol agreement admissible supported
      single charge cfg calibrated c node data reached current rootAddress references oneClass
      nontransitive noOdd false
    have reflected := step_ne_none_of_singleMovingClass input mol agreement admissible supported
      single charge cfg calibrated c node data reached current rootAddress references oneClass
      nontransitive noOdd true
    rcases (LocalizedChemicalRingJointPreparedExecution.descriptor_none_iff input mol node
      (structuralDepth mol node) (inputGeometry input) references).mp refused with failed | failed
    · exact original failed
    · exact reflected failed
  · intro odd
    have history := root_history input mol c node data rootAddress current
    exact refusal_of_oddBoundary input mol agreement admissible supported single cfg calibrated
      c node data reached current [] references (by simp [history]) (by simp) odd

include agreement admissible supported single charge calibrated in
/-- The exact criterion holds for the literal detected-center report, including refusal entries. -/
theorem detected_report_success_refusal_iff
    (center : input.detectedMultiCenterMolecule.Center)
    (oneClass : SingleMovingClass input cfg center [])
    (nontransitive : ¬ PhysicalTransitive input cfg center []) :
    ((∃ label, (center.1.val, some label) ∈ analyze input mol) ↔
      ¬ OddBoundarySymmetry input cfg center [] []) ∧
    ((center.1.val, none) ∈ analyze input mol ↔ OddBoundarySymmetry input cfg center [] []) := by
  obtain ⟨data, rootAddress⟩ := root_data input mol agreement admissible supported single center
  have criterion := descriptor_none_iff_oddBoundary input mol agreement admissible supported single
    charge cfg calibrated center (canonicalCenterRoot center.1.val) data
    (root_reached input mol agreement center) rfl rootAddress [] oneClass nontransitive
  have refusal : (center.1.val, none) ∈ analyze input mol ↔
      OddBoundarySymmetry input cfg center [] [] := by
    rw [mem_analyze_at_center_iff]
    exact criterion
  refine ⟨?_, refusal⟩
  simp only [mem_analyze_at_center_iff]
  change (∃ label, preparedDescriptor? mol (jointOperations input mol)
    (structuralDepth mol (canonicalCenterRoot center.1.val)) (inputGeometry input) []
      (([] : List input.Atom).map Fin.val) (canonicalCenterRoot center.1.val) = some label) ↔ _
  rw [← criterion]
  cases preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol (canonicalCenterRoot center.1.val)) (inputGeometry input) []
      (([] : List input.Atom).map Fin.val) (canonicalCenterRoot center.1.val) <;> simp

end
end TetraStereo.OneCenter.LocalizedChemicalRingRootSingleMovingClass

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSingleMovingClass.SingleMovingClass
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSingleMovingClass.selected_keys_eq_of_singleMovingClass
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSingleMovingClass.step_ne_none_of_singleMovingClass
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSingleMovingClass.descriptor_none_iff_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSingleMovingClass.detected_report_success_refusal_iff
