import TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport
import TetraStereo.OneCenter.LocalizedChemicalRingThreeCycleConsensus
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedParentEligibility
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! The even-three-cycle branch of the physical residual induction cannot refuse merely
because successful local readings disagree. Actual symmetry transport makes the readings
constant on the actual eligible population; refusal supplies a genuinely failed local
reading and its actual key tie. Residual physical properness remains the induction
hypothesis, not an established property of every reconstructed symmetry. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingResidualReadingTransport
open LocalizedChemicalRingSelectedRefusalWitness LocalizedChemicalRingSelectedParentEligibility
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

/-- The actual molecular action expressed in the occurrence frame's slots. -/
def slotAction : Equiv.Perm (Fin 4) :=
  (data.ligandOf.trans (input.detectedMultiCenterMolecule.ligandPermAt e c)).trans data.ligandOf.symm

theorem referenceAt_action (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c)
    (slot : Fin 4) :
    referenceAt input mol c node data (slotAction input mol e c node data slot) =
      (e : Equiv.Perm input.Atom) (referenceAt input mol c node data slot) := by
  simp only [referenceAt, slotAction, Equiv.trans_apply, Equiv.apply_symm_apply]
  have h := input.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt e c (data.ligandOf slot)
  rw [fixed] at h
  exact h

variable
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (reached : Reached mol node) (current : node.atom = c.1.val)
  (historyFixed : ∀ atom ∈ node.history, relabelOf input (e : Equiv.Perm input.Atom) atom = atom)

include reached current historyFixed in
theorem center_fixed : input.detectedMultiCenterMolecule.centerPerm e c = c := by
  have fixedNode := mapNode_eq_of_history_fixed mol _ node reached historyFixed
  have atom := congrArg RawMolecule.CanonicalBranchNode.atom fixedNode
  change relabelOf input (e : Equiv.Perm input.Atom) node.atom = node.atom at atom
  rw [current, relabelOf_val] at atom
  exact Subtype.ext (Fin.ext atom)

include agreement admissible supported single reached current historyFixed in
/-- Membership transport for the ACTUAL eligible population, derived from ordinary
callback covariance at the fixed raw occurrence. -/
theorem eligible_closed (slot : Fin 4)
    (member : slot ∈ eligibleSlots input mol single c node data) :
    slotAction input mol e c node data slot ∈ eligibleSlots input mol single c node data := by
  have fixedNode := mapNode_eq_of_history_fixed mol _ node reached historyFixed
  have fixed := center_fixed input mol e c node reached current historyFixed
  have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
    input mol agreement admissible supported single e
  have rel := cov.ordinary node reached data.atoms data.atoms data.rawFrame
    (by rw [fixedNode]; exact data.rawFrame)
  rw [fixedNode, ordinary_eq input mol single c node data, ordinaryRel_some_some] at rel
  obtain ⟨_, _, _, perm⟩ := rel
  rw [eligible_eq input mol single c node data] at perm
  have transported : (referenceAt input mol c node data (slotAction input mol e c node data slot)).val ∈
      (eligibleSlots input mol single c node data).map (fun i => (referenceAt input mol c node data i).val) := by
    rw [perm.mem_iff, List.map_map]
    refine List.mem_map.mpr ⟨slot, member, ?_⟩
    simp only [Function.comp_apply, relabelOf_val, referenceAt_action input mol e c node data fixed]
  obtain ⟨other, otherMember, equal⟩ := List.mem_map.mp transported
  have same : other = slotAction input mol e c node data slot :=
    data.ligandOf.injective (input.detectedMultiCenterMolecule.ligandAtomAt_injective c (Fin.ext equal))
  rwa [same] at otherMember

variable
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (real : node.provenance = .realAtom)
  (B : List input.Atom) (outside : c.1 ∉ B)
  (carried : ∀ atom ∈ B, atom.val ∈ node.history)
  (proper : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph B c.1 d.1 → d.1 ≠ c.1 →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
  (even : relativeSign input.detectedMultiCenterMolecule cfg e c = 1)

include reached current historyFixed in
/-- The current center's proper sign follows from the actual frame action's cube law;
only OTHER residual centers require the physical induction hypothesis. -/
theorem local_even_of_cube (cube : (slotAction input mol e c node data) ^ 3 = 1) :
    relativeSign input.detectedMultiCenterMolecule cfg e c = 1 := by
  have fixed := center_fixed input mol e c node reached current historyFixed
  rw [LocalizedChemicalRingCompletenessOrbit.relativeSign_fixed input cfg e c fixed]
  have sign := LocalizedChemicalRingThreeCycleConsensus.sign_one_of_conjugate_cube
    data.ligandOf (input.detectedMultiCenterMolecule.ligandPermAt e c) cube
  simp [permHandedness, sign]

include agreement admissible supported single reached current historyFixed calibrated real
  outside carried proper even in
theorem reading_action (depth : Nat) (reflected : Bool) (slot : Fin 4) :
    generatedReading input mol c node data depth reflected (slotAction input mol e c node data slot) =
      generatedReading input mol c node data depth reflected slot := by
  have fixed := center_fixed input mol e c node reached current historyFixed
  have transported := candidate_reading_transport input mol agreement admissible supported single
    cfg e calibrated c node reached real current historyFixed B outside carried proper
    depth reflected (referenceAt input mol c node data slot)
  rw [even, if_pos rfl] at transported
  simpa only [generatedReading, reading, referenceAt_action input mol e c node data fixed] using transported

include agreement admissible supported single reached current historyFixed calibrated real
  outside carried proper in
/-- Every actually eligible reading is equal in the even-three-cycle case. The eligible
population and its properness are derived from the actual keys and incoming separation. -/
theorem eligible_readings_equal (branch : TiedRootBranch input data.target)
    (notInjective : ¬ Function.Injective (ordinaryKeys input mol single c node data))
    (cube : (slotAction input mol e c node data) ^ 3 = 1)
    (nontrivial : slotAction input mol e c node data ≠ 1)
    (depth : Nat) (reflected : Bool) (i j : Fin 4)
    (memberI : i ∈ eligibleSlots input mol single c node data)
    (memberJ : j ∈ eligibleSlots input mol single c node data) :
    generatedReading input mol c node data depth reflected j =
      generatedReading input mol c node data depth reflected i := by
  let eligible := eligibleSlots input mol single c node data
  have even := local_even_of_cube input mol e c node data reached current historyFixed cfg cube
  obtain ⟨excluded, _, excludedMem⟩ := parent_not_eligible input mol single c node data branch
  obtain ⟨first, firstMem⟩ := List.exists_mem_of_ne_nil eligible
    (eligible_ne_nil input mol single c node data notInjective)
  obtain ⟨second, different, equal⟩ := (eligible_iff_other input mol single c node data first).mp firstMem
  have secondMem : second ∈ eligible :=
    (eligible_iff_other input mol single c node data second).mpr ⟨first, different.symm, equal.symm⟩
  obtain ⟨parent, fixed, moved, nonparent⟩ := LocalizedChemicalRingThreeCycleConsensus.eligible_orbit
    (slotAction input mol e c node data) cube nontrivial eligible.toFinset
    ⟨excluded, by simpa using excludedMem⟩
    ⟨first, List.mem_toFinset.mpr firstMem, second, List.mem_toFinset.mpr secondMem, different.symm⟩
    (fun k hk => List.mem_toFinset.mpr (eligible_closed input mol single e c node data agreement
      admissible supported reached current historyFixed k (List.mem_toFinset.mp hk)))
  exact LocalizedChemicalRingThreeCycleConsensus.readings_eq _ parent fixed moved _
    (reading_action input mol single e c node data agreement admissible supported reached current
      historyFixed cfg calibrated real B outside carried proper even depth reflected)
    i j (nonparent i (List.mem_toFinset.mpr memberI)) (nonparent j (List.mem_toFinset.mpr memberJ))

include agreement admissible supported single reached current historyFixed calibrated real
  outside carried proper in
/-- In this induction case, actual refusal supplies a failed local reading and its actual
key tie. The successful-readings-disagree alternative is eliminated, not assumed away. -/
theorem refusal_has_failed_eligible (branch : TiedRootBranch input data.target)
    (cube : (slotAction input mol e c node data) ^ 3 = 1)
    (nontrivial : slotAction input mol e c node data ≠ 1)
    (depth : Nat) (ctx : Option Nat) (reflected : Bool)
    (refused : LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input reflected) [] ctx node (generated input mol node depth reflected) = none) :
    ∃ slot ∈ eligibleSlots input mol single c node data,
      generatedReading input mol c node data depth reflected slot = none ∧
      ∃ left right : Fin 4, left ≠ right ∧
        markedKeys input mol single c node data
          (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
          (referenceAt input mol c node data slot) left =
        markedKeys input mol single c node data
          (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
          (referenceAt input mol c node data slot) right := by
  obtain ⟨notInjective, _, failure⟩ := (step_none_iff input mol single cfg c (calibrated c) node data
    agreement admissible supported depth ctx reflected).mp refused
  rcases failure with ⟨slot, member, tie⟩ | ⟨i, memberI, j, memberJ, a, b, first, second, different⟩
  · exact ⟨slot, member, (generatedReading_none_iff input mol single cfg c (calibrated c) node data
      agreement admissible supported depth reflected slot).mpr tie, tie⟩
  · have same := eligible_readings_equal input mol single e c node data agreement admissible
      supported reached current historyFixed cfg calibrated real B outside carried proper
      branch notInjective cube nontrivial depth reflected i j memberI memberJ
    rw [first, second, Option.some.injEq] at same
    exact False.elim (different same.symm)

end
end TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal.referenceAt_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal.center_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal.eligible_closed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal.reading_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal.local_even_of_cube
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal.eligible_readings_equal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal.refusal_has_failed_eligible
