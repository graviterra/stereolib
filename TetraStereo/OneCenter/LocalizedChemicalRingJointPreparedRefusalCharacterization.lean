import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTiePhysical
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! The actual prepared auxiliary descriptor refuses exactly when an independent residual
physical obstruction exists: one molecular automorphism fixes the history and all references,
is odd at the current center and proper at every center outside the history. This is the
non-root tied-branch scope; original-root chemical assignment is a separate theorem. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointPreparedOccurrenceCorrection (occurrence_correction)
open LocalizedChemicalRingJointPreparedSourceProper (claim_all)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingJointOperationTransportExecution (actual_preparedDescriptor_map)
open LocalizedChemicalRingJointPreparedResidualDecoder (descriptor_flip_of_residual_signs)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut)
open LocalizedChemicalRingResidualReadingTransport (mapNode_eq_of_history_fixed)
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingOrientationReadback (flipDescriptorBy flipDescriptorBy_some_eq)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-- A physical residual obstruction, stated without evaluator states, comparison keys or labels. -/
def OddBoundarySymmetry (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center) (B references : List input.Atom) : Prop :=
  ∃ e : input.detectedMultiCenterMolecule.Aut,
    (∀ atom ∈ B ++ [c.1], (e : Equiv.Perm input.Atom) atom = atom) ∧
    (∀ atom ∈ references, (e : Equiv.Perm input.Atom) atom = atom) ∧
    relativeSign input.detectedMultiCenterMolecule cfg e c = -1 ∧
    ∀ d : input.detectedMultiCenterMolecule.Center, d.1 ∉ B ++ [c.1] →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1

variable (mol : RawMolecule)
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
  (real : node.provenance = .realAtom) (current : node.atom = c.1.val)
  (branch : TiedRootBranch input data.target) (B references : List input.Atom)
  (boundary : data.target.1.node.history.reverse = B ++ [c.1]) (outside : c.1 ∉ B)

include agreement admissible supported single charge calibrated reached real current branch boundary outside in
/-- Refusal constructs the physical obstruction, retaining all references. -/
theorem oddBoundary_of_refusal
    (refused : preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = none) :
    OddBoundarySymmetry input cfg c B references := by
  have sameTarget (actual : OccurrenceData input mol c node) : actual.target = data.target :=
    Option.some.inj (actual.found.symm.trans data.found)
  obtain ⟨e, _, _, _, _, fixed, _, refs, odd, proper⟩ :=
    occurrence_correction input mol agreement admissible supported single charge cfg calibrated
      (structuralDepth mol node + 1)
      (fun n _ => claim_all input mol agreement admissible supported single charge cfg calibrated n)
      c node reached real current (Nat.lt_succ_self _) B outside
      (fun actual => by rw [sameTarget actual]; exact boundary)
      (fun actual => by rw [sameTarget actual]; exact branch) references refused
  exact ⟨e, fixed, refs, odd, proper⟩

include agreement admissible supported single calibrated reached current boundary outside in
/-- An odd physical residual symmetry forces actual refusal, including either descriptor case. -/
theorem refusal_of_oddBoundary (obstruction : OddBoundarySymmetry input cfg c B references) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = none := by
  obtain ⟨e, fixed, refs, odd, properOff⟩ := obstruction
  have sound := (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).history
  have carriedAll : ∀ atom ∈ B ++ [c.1], atom.val ∈ node.history := by
    intro atom member
    rw [← sound]
    apply List.mem_map.mpr
    exact ⟨atom, List.mem_reverse.mp (boundary.symm ▸ member), rfl⟩
  have rawFixed : ∀ value ∈ node.history, relabelOf input (e : Equiv.Perm input.Atom) value = value := by
    intro value member
    rw [← sound] at member
    obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
    have memberB : atom ∈ B ++ [c.1] := boundary ▸ List.mem_reverse.mpr present
    rw [relabelOf_val, fixed atom memberB]
  have proper : ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph B c.1 d.1 → d.1 ≠ c.1 →
        relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
    intro d member different
    apply properOff
    intro present
    rcases List.mem_append.mp present with inB | last
    · exact inComponent_not_mem input.moleculeGraph member inB
    · exact different (List.mem_singleton.mp last)
  let graphAut : input.moleculeGraph.Aut :=
    ⟨e, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule e⟩
  have transported := actual_preparedDescriptor_map input mol agreement admissible supported single
    graphAut (structuralSymmetry_of_aut input mol agreement admissible supported e)
    (structuralDepth mol node) (inputGeometry input) (references.map Fin.val) node reached
  have marksFixed : (references.map Fin.val).map (relabelOf input (e : Equiv.Perm input.Atom)) =
      references.map Fin.val := by
    rw [List.map_map]
    apply List.map_congr_left
    intro atom member
    rw [Function.comp_apply, relabelOf_val, refs atom member]
  change preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) []
      ((references.map Fin.val).map (relabelOf input (e : Equiv.Perm input.Atom)))
      (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = _ at transported
  rw [marksFixed, mapNode_eq_of_history_fixed mol _ node reached rawFixed] at transported
  have flip := descriptor_flip_of_residual_signs input mol agreement admissible supported single
    cfg e calibrated B node c.1 current.symm outside
    (fun atom member => carriedAll atom (List.mem_append_left _ member)) reached proper
    (jointOperations input mol) c current data.atoms data.rawFrame (structuralDepth mol node)
    [] (references.map Fin.val)
  rw [← transported] at flip
  cases result : preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node with
  | none => rfl
  | some label =>
      rw [result] at flip
      have impossible := flipDescriptorBy_some_eq _ (relativeSign_eq_one_or_neg_one _ cfg e c)
        label flip.symm
      rw [odd] at impossible
      norm_num at impossible

include agreement admissible supported single charge calibrated reached real current branch boundary outside in
/-- Complete actual refusal characterization by the independent residual physical criterion. -/
theorem refusal_iff_oddBoundary :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = none ↔
      OddBoundarySymmetry input cfg c B references :=
  ⟨oddBoundary_of_refusal input mol agreement admissible supported single charge cfg calibrated
      c node data reached real current branch B references boundary outside,
    refusal_of_oddBoundary input mol agreement admissible supported single cfg calibrated
      c node data reached current B references boundary outside⟩

include agreement admissible supported single charge calibrated reached real current branch boundary outside in
/-- Actual auxiliary assignment exists exactly when the independent physical obstruction is absent. -/
theorem success_iff_no_oddBoundary :
    (∃ label, preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = some label) ↔
      ¬ OddBoundarySymmetry input cfg c B references := by
  have criterion := refusal_iff_oddBoundary input mol agreement admissible supported single charge
    cfg calibrated c node data reached real current branch B references boundary outside
  constructor
  · rintro ⟨label, success⟩ obstruction
    have refused := criterion.mpr obstruction
    rw [success] at refused
    cases refused
  · intro absent
    cases result : preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
        (inputGeometry input) [] (references.map Fin.val) node with
    | none => exact False.elim (absent (criterion.mp result))
    | some label => exact ⟨label, rfl⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization.oddBoundary_of_refusal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization.refusal_of_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization.refusal_iff_oddBoundary

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization.success_iff_no_oddBoundary
