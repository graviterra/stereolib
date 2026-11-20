import TetraStereo.OneCenter.LocalizedChemicalRingRootFallbackPhysicalObstruction
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootClassReadings
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Physical classification of transitive root outcomes

When independent molecular symmetries relate every pair of root ligands, the actual root
descriptor succeeds exactly when there is no odd boundary symmetry and fixing one root ligand
removes every remaining motion of the root ligands. This includes the previously unresolved
four-way tie. The criterion contains no evaluator keys, generated labels or expected outputs.
It characterizes the current single-promotion evaluator; it does not adopt that evaluator as
an interpretation of a published chemical rule.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveClassification

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRootPhysicalKeyClasses (PhysicalTransport keys_eq_iff_physicalTransport)
open LocalizedChemicalRingRootFallbackPhysicalObstruction
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (generated keys fallback step)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots selectedSlots_nonempty)
open LocalizedChemicalRingJointPreparedRootClassReadings (fallback_eq_of_root_key_eq)
open LocalizedChemicalRingJointPreparedRefusalCharacterization
  (OddBoundarySymmetry refusal_of_oddBoundary)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculation (structuralDepth consensus)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- Independent transitivity of the physical action on the root's four ligands. -/
def PhysicalTransitive (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center) (references : List input.Atom) : Prop :=
  ∀ left right : Fin 4, left ≠ right → PhysicalTransport input cfg c references left right

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
/-- Four-way equality of actual keys is exactly independent physical transitivity. -/
theorem constant_keys_iff_physicalTransitive (reflected : Bool) :
    (∀ i, keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references i =
      keys input mol single c node data (structuralDepth mol node)
        (observedGeometry input reflected) references 0) ↔
    PhysicalTransitive input cfg c references := by
  constructor
  · intro constant left right distinct
    have different : data.ligandOf.symm left ≠ data.ligandOf.symm right :=
      fun same => distinct (data.ligandOf.symm.injective same)
    have tied := (constant (data.ligandOf.symm left)).trans
      (constant (data.ligandOf.symm right)).symm
    simpa using (keys_eq_iff_physicalTransport input mol agreement admissible supported single
      charge cfg calibrated c node data reached current rootAddress references reflected
      (data.ligandOf.symm left) (data.ligandOf.symm right) different).mp tied
  · intro transitive i
    by_cases same : i = 0
    · simp only [same]
    · exact (keys_eq_iff_physicalTransport input mol agreement admissible supported single
        charge cfg calibrated c node data reached current rootAddress references reflected
        i 0 same).mpr (transitive _ _ (fun h => same (data.ligandOf.injective h)))

include agreement admissible supported single charge calibrated reached current rootAddress in
/-- With a transitive even physical action, consensus is exactly any one promoted reading. -/
theorem step_eq_fallback_of_transitive_noOdd
    (transitive : PhysicalTransitive input cfg c references)
    (noOdd : ¬ OddBoundarySymmetry input cfg c [] references)
    (reflected : Bool) (slot : Fin 4) :
    step input mol node (structuralDepth mol node) (observedGeometry input reflected) references =
      fallback input mol c node data (structuralDepth mol node)
        (observedGeometry input reflected) references slot := by
  have constant := (constant_keys_iff_physicalTransitive input mol agreement admissible supported
    single charge cfg calibrated c node data reached current rootAddress references reflected).mpr
    transitive
  have notInj : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references) := by
    intro injective
    have different : (1 : Fin 4) ≠ 0 := by decide
    exact different (injective (constant 1))
  have nonempty := selectedSlots_nonempty input mol single c node data
    (generated input mol (structuralDepth mol node) (observedGeometry input reflected) node references)
    references notInj
  have uniform (i : Fin 4) :
      fallback input mol c node data (structuralDepth mol node)
        (observedGeometry input reflected) references i =
      fallback input mol c node data (structuralDepth mol node)
        (observedGeometry input reflected) references slot :=
    fallback_eq_of_root_key_eq input mol agreement admissible supported single charge cfg
      calibrated c node data reached current rootAddress references reflected noOdd i slot
      ((constant i).trans (constant slot).symm)
  rw [LocalizedChemicalRingJointPreparedExecution.step_eq input mol agreement admissible
    supported single c node data (structuralDepth mol node), if_neg notInj]
  cases found : fallback input mol c node data (structuralDepth mol node)
      (observedGeometry input reflected) references slot with
  | none =>
      obtain ⟨other, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact LocalizedChemicalRingCompletenessMarked.consensus_map_none _ _ other member
        ((uniform other).trans found)
  | some value =>
      exact LocalizedChemicalRingCompletenessMarked.consensus_map_const _ nonempty _ value
        (fun other _ => (uniform other).trans found)

include agreement admissible supported single charge calibrated reached current rootAddress in
/-- Both geometries refuse by the same independent point-stabilizer criterion. -/
theorem descriptor_none_iff_markedRootMotion_of_transitive_noOdd
    (transitive : PhysicalTransitive input cfg c references)
    (noOdd : ¬ OddBoundarySymmetry input cfg c [] references) (slot : Fin 4) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = none ↔
    MarkedRootMotion input cfg c references (referenceAt input mol c node data slot) := by
  have criterion (reflected : Bool) :
      step input mol node (structuralDepth mol node) (observedGeometry input reflected)
        references = none ↔
      MarkedRootMotion input cfg c references (referenceAt input mol c node data slot) := by
    rw [step_eq_fallback_of_transitive_noOdd input mol agreement admissible supported single
      charge cfg calibrated c node data reached current rootAddress references transitive noOdd
      reflected slot]
    exact fallback_none_iff_markedRootMotion input mol agreement admissible supported single
      charge cfg calibrated c node data reached current rootAddress references reflected slot
  rw [LocalizedChemicalRingJointPreparedExecution.descriptor_none_iff]
  change (step input mol node (structuralDepth mol node) (observedGeometry input false)
      references = none ∨
    step input mol node (structuralDepth mol node) (observedGeometry input true)
      references = none) ↔ _
  rw [criterion false, criterion true, or_self]

include agreement admissible supported single charge calibrated reached current rootAddress in
/-- Exact refusal classification for every physically transitive root, including odd actions. -/
theorem descriptor_none_iff_transitive_obstruction
    (transitive : PhysicalTransitive input cfg c references) (slot : Fin 4) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = none ↔
    OddBoundarySymmetry input cfg c [] references ∨
      MarkedRootMotion input cfg c references (referenceAt input mol c node data slot) := by
  by_cases odd : OddBoundarySymmetry input cfg c [] references
  · have history := root_history input mol c node data rootAddress current
    have refused := refusal_of_oddBoundary input mol agreement admissible supported single
      cfg calibrated c node data reached current [] references (by simp [history]) (by simp) odd
    simp only [refused, odd, true_or, iff_self]
  · rw [descriptor_none_iff_markedRootMotion_of_transitive_noOdd input mol agreement admissible
      supported single charge cfg calibrated c node data reached current rootAddress references
      transitive odd slot]
    simp only [odd, false_or]

include agreement admissible supported single charge calibrated reached current rootAddress in
/-- Exact success classification, with the promoted point quantified independently of a frame. -/
theorem descriptor_success_iff_transitive_freePoint
    (transitive : PhysicalTransitive input cfg c references) :
    (∃ label, preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = some label) ↔
    ¬ OddBoundarySymmetry input cfg c [] references ∧
      ∃ ligand : Fin 4, FreeAt input cfg c references
        (input.detectedMultiCenterMolecule.ligandAtomAt c ligand) := by
  constructor
  · rintro ⟨label, success⟩
    have absent : ¬ (OddBoundarySymmetry input cfg c [] references ∨
        MarkedRootMotion input cfg c references (referenceAt input mol c node data 0)) := by
      intro obstruction
      have refused := (descriptor_none_iff_transitive_obstruction input mol agreement admissible
        supported single charge cfg calibrated c node data reached current rootAddress references
        transitive 0).mpr obstruction
      rw [success] at refused
      cases refused
    refine ⟨fun odd => absent (Or.inl odd), data.ligandOf 0, ?_⟩
    intro left right transported
    by_contra distinct
    exact absent (Or.inr ⟨left, right, distinct, transported⟩)
  · rintro ⟨noOdd, ligand, free⟩
    cases result : preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
        (inputGeometry input) [] (references.map Fin.val) node with
    | some label => exact ⟨label, rfl⟩
    | none =>
        have obstruction := (descriptor_none_iff_transitive_obstruction input mol agreement
          admissible supported single charge cfg calibrated c node data reached current rootAddress
          references transitive (data.ligandOf.symm ligand)).mp result
        rcases obstruction with odd | ⟨left, right, distinct, transported⟩
        · exact False.elim (noOdd odd)
        · have moved : PhysicalTransport input cfg c
              (references ++ [input.detectedMultiCenterMolecule.ligandAtomAt c ligand]) left right := by
            simpa [referenceAt] using transported
          exact False.elim (distinct (free left right moved))

end
end TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveClassification

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveClassification.constant_keys_iff_physicalTransitive
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveClassification.step_eq_fallback_of_transitive_noOdd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveClassification.descriptor_none_iff_markedRootMotion_of_transitive_noOdd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveClassification.descriptor_none_iff_transitive_obstruction
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveClassification.descriptor_success_iff_transitive_freePoint
