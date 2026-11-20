import TetraStereo.OneCenter.LocalizedChemicalRingRootSingleMovingClass
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact localization of the remaining nontransitive refusal domain. Four distinct native
ligand slots in two different moving classes exhaust a four-slot root: the unresolved partition
is two plus two. This does not assert that every such root refuses or that its class readings
agree; those are separate questions. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootTwoMovingPairs

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRootPhysicalKeyClasses (PhysicalTransport keys_eq_iff_physicalTransport)
open LocalizedChemicalRingRootSingleMovingClass (SingleMovingClass)
open LocalizedChemicalRingRootTransitiveClassification (PhysicalTransitive)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (keys)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry)
open LocalizedChemicalRingJointPreparedRootInput (root_data root_reached)
open LocalizedChemicalRingJointPreparedReport (analyze)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- Two separate moving physical classes, witnessed by four distinct native root ligands.
The four witnesses exhaust `Fin 4`; the cross-class nontransport excludes a merged class. -/
def TwoMovingPairs (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (center : input.detectedMultiCenterMolecule.Center) (references : List input.Atom) : Prop :=
  ∃ left left' right right' : Fin 4,
    ([left, left', right, right'] : List (Fin 4)).Pairwise (· ≠ ·) ∧
    PhysicalTransport input cfg center references left left' ∧
    PhysicalTransport input cfg center references right right' ∧
    ¬ PhysicalTransport input cfg center references left right

/-- Two separate moving pairs violate the one-moving-class condition directly. -/
theorem twoMovingPairs_not_singleMovingClass (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (center : input.detectedMultiCenterMolecule.Center) (references : List input.Atom)
    (twoPairs : TwoMovingPairs input cfg center references) :
    ¬ SingleMovingClass input cfg center references := by
  rintro oneClass
  obtain ⟨left, left', right, right', different, moveLeft, moveRight, separated⟩ := twoPairs
  have head := (List.pairwise_cons.mp different).1
  have tail := (List.pairwise_cons.mp (List.pairwise_cons.mp different).2).2
  have rightDifferent := (List.pairwise_cons.mp tail).1 right' (by simp)
  exact separated (oneClass left left' right right' (head left' (by simp)) rightDifferent
    moveLeft moveRight (head right (by simp)))

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

include agreement admissible supported single charge calibrated in
/-- Failure of the independent one-moving-class condition is exactly the two-pair partition.
Actual key equality is used only inside the proof to establish disjointness of physical classes. -/
theorem not_singleMovingClass_iff_twoMovingPairs
    (center : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol center node) (reached : Reached mol node)
    (current : node.atom = center.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool) :
    ¬ SingleMovingClass input cfg center references ↔ TwoMovingPairs input cfg center references := by
  constructor
  · intro notOne
    unfold SingleMovingClass at notOne
    push_neg at notOne
    obtain ⟨left, left', right, right', differentLeft, differentRight,
      moveLeft, moveRight, crossDifferent, crossAbsent⟩ := notOne
    let key (slot : Fin 4) := keys input mol single center node data (structuralDepth mol node)
      (observedGeometry input reflected) references (data.ligandOf.symm slot)
    have correspondence (a b : Fin 4) (distinct : a ≠ b) :
        key a = key b ↔ PhysicalTransport input cfg center references a b := by
      have slotDistinct : data.ligandOf.symm a ≠ data.ligandOf.symm b :=
        fun same => distinct (data.ligandOf.symm.injective same)
      simpa only [key, Equiv.apply_symm_apply] using
        keys_eq_iff_physicalTransport input mol agreement admissible supported single charge cfg
          calibrated center node data reached current rootAddress references reflected
          (data.ligandOf.symm a) (data.ligandOf.symm b) slotDistinct
    have tieLeft := (correspondence left left' differentLeft).mpr moveLeft
    have tieRight := (correspondence right right' differentRight).mpr moveRight
    have separated : key left ≠ key right :=
      fun tied => crossAbsent ((correspondence left right crossDifferent).mp tied)
    have leftRight' : left ≠ right' := by
      intro same
      apply separated
      rw [same]
      exact tieRight.symm
    have left'Right : left' ≠ right := by
      intro same
      exact separated (tieLeft.trans (congrArg key same))
    have left'Right' : left' ≠ right' := by
      intro same
      exact separated (tieLeft.trans ((congrArg key same).trans tieRight.symm))
    refine ⟨left, left', right, right', ?_, moveLeft, moveRight, crossAbsent⟩
    simp [List.pairwise_cons, differentLeft, differentRight, crossDifferent, leftRight', left'Right, left'Right']
  · exact twoMovingPairs_not_singleMovingClass input cfg center references

include agreement admissible supported single charge calibrated in
/-- Every remaining nontransitive actual refusal without an odd boundary belongs to the two-pair
physical domain. This is a necessary condition for refusal, not a refusal claim for all two-pair roots. -/
theorem detected_refusal_without_odd_implies_twoMovingPairs
    (center : input.detectedMultiCenterMolecule.Center)
    (nontransitive : ¬ PhysicalTransitive input cfg center [])
    (noOdd : ¬ OddBoundarySymmetry input cfg center [] [])
    (refused : (center.1.val, none) ∈ analyze input mol) :
    TwoMovingPairs input cfg center [] := by
  have notOne : ¬ SingleMovingClass input cfg center [] := by
    intro oneClass
    exact noOdd ((LocalizedChemicalRingRootSingleMovingClass.detected_report_success_refusal_iff
      input mol agreement admissible supported single charge cfg calibrated center oneClass
      nontransitive).2.mp refused)
  obtain ⟨data, rootAddress⟩ := root_data input mol agreement admissible supported single center
  exact (not_singleMovingClass_iff_twoMovingPairs input mol agreement admissible supported single
    charge cfg calibrated center (canonicalCenterRoot center.1.val) data
    (root_reached input mol agreement center) rfl rootAddress [] false).mp notOne

end
end TetraStereo.OneCenter.LocalizedChemicalRingRootTwoMovingPairs

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTwoMovingPairs.TwoMovingPairs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTwoMovingPairs.twoMovingPairs_not_singleMovingClass
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTwoMovingPairs.not_singleMovingClass_iff_twoMovingPairs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTwoMovingPairs.detected_refusal_without_odd_implies_twoMovingPairs
