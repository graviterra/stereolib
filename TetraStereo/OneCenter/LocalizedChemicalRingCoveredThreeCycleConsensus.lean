import TetraStereo.OneCenter.LocalizedChemicalRingCoveredReadingTransport
import TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
At a real reached occurrence whose history covers every detected center, an actual
history-fixing three-cycle makes all eligible generated readings equal. Incoming-slot
exclusion and eligible-population closure come from the actual comparisons. Coverage
discharges descendant readback agreement; only the current frame needs calibration.

The consensus may still be absent. In that case an actual refused candidate step has a
failed eligible reading and an actual marked-key tie, rather than two successful readings
that disagree. No physical sign at another center, reader agreement, or successful label
is assumed. The tied-root-branch premise retains its existing carrier-path meaning.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCoveredThreeCycleConsensus

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSelectedRefusalWitness LocalizedChemicalRingSelectedParentEligibility
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action center_fixed
  eligible_closed local_even_of_cube)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedGenericMarkedRecalculation (consensus)
open LocalizedChemicalRingSenseTransport (consensus_eq_some_iff)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (reached : Reached mol node) (real : node.provenance = .realAtom)
  (current : node.atom = c.1.val)
  (historyFixed : ∀ atom ∈ node.history, relabelOf input (e : Equiv.Perm input.Atom) atom = atom)
  (covered : ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val ∈ node.history)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)

include agreement admissible supported single reached real current historyFixed covered calibrated in
/-- The actual reference action preserves generated readings. Its local proper sign is
derived from the cube law; coverage replaces all other-center physical-sign hypotheses. -/
theorem reading_action (cube : (slotAction input mol e c node data) ^ 3 = 1)
    (depth : Nat) (reflected : Bool) (slot : Fin 4) :
    generatedReading input mol c node data depth reflected (slotAction input mol e c node data slot) =
      generatedReading input mol c node data depth reflected slot := by
  have fixed := center_fixed input mol e c node reached current historyFixed
  have even := local_even_of_cube input mol e c node data reached current historyFixed cfg cube
  have imageCalibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule
      cfg (input.detectedMultiCenterMolecule.centerPerm e c) := by
    rw [fixed]
    exact calibrated
  have transported := LocalizedChemicalRingCoveredReadingTransport.candidate_reading_transport
    input mol agreement admissible supported single cfg e c calibrated imageCalibrated
    node reached real current historyFixed covered depth reflected (referenceAt input mol c node data slot)
  rw [even, if_pos rfl] at transported
  simpa only [generatedReading, reading, referenceAt_action input mol e c node data fixed] using transported

include agreement admissible supported single reached real current historyFixed covered calibrated in
/-- Any two actually eligible references give the same optional reading. Nonemptiness
and a second eligible slot follow from the supplied membership, not a sorting premise. -/
theorem eligible_readings_equal (branch : TiedRootBranch input data.target)
    (cube : (slotAction input mol e c node data) ^ 3 = 1)
    (nontrivial : slotAction input mol e c node data ≠ 1)
    (depth : Nat) (reflected : Bool) (i j : Fin 4)
    (memberI : i ∈ eligibleSlots input mol single c node data)
    (memberJ : j ∈ eligibleSlots input mol single c node data) :
    generatedReading input mol c node data depth reflected j =
      generatedReading input mol c node data depth reflected i := by
  let eligible := eligibleSlots input mol single c node data
  obtain ⟨excluded, _, excludedMem⟩ := parent_not_eligible input mol single c node data branch
  obtain ⟨second, different, equal⟩ := (eligible_iff_other input mol single c node data i).mp memberI
  have secondMem : second ∈ eligible :=
    (eligible_iff_other input mol single c node data second).mpr ⟨i, different.symm, equal.symm⟩
  obtain ⟨parent, fixed, moved, nonparent⟩ := LocalizedChemicalRingThreeCycleConsensus.eligible_orbit
    (slotAction input mol e c node data) cube nontrivial eligible.toFinset
    ⟨excluded, by simpa using excludedMem⟩
    ⟨i, List.mem_toFinset.mpr memberI, second, List.mem_toFinset.mpr secondMem, different.symm⟩
    (fun k hk => List.mem_toFinset.mpr (eligible_closed input mol single e c node data agreement
      admissible supported reached current historyFixed k (List.mem_toFinset.mp hk)))
  exact LocalizedChemicalRingThreeCycleConsensus.readings_eq _ parent fixed moved _
    (reading_action input mol single e c node data agreement admissible supported reached real current
      historyFixed covered cfg calibrated cube depth reflected)
    i j (nonparent i (List.mem_toFinset.mpr memberI)) (nonparent j (List.mem_toFinset.mpr memberJ))

include agreement admissible supported single reached real current historyFixed covered calibrated in
/-- Consensus equals any actually eligible reading, including its possible refusal. -/
theorem consensus_eq_reading (branch : TiedRootBranch input data.target)
    (cube : (slotAction input mol e c node data) ^ 3 = 1)
    (nontrivial : slotAction input mol e c node data ≠ 1)
    (depth : Nat) (reflected : Bool) (i : Fin 4)
    (member : i ∈ eligibleSlots input mol single c node data) :
    consensus ((eligibleSlots input mol single c node data).map
      (generatedReading input mol c node data depth reflected)) =
        generatedReading input mol c node data depth reflected i := by
  have same := eligible_readings_equal input mol single e c node data agreement admissible supported
    reached real current historyFixed covered cfg calibrated branch cube nontrivial depth reflected i
  cases readAt : generatedReading input mol c node data depth reflected i with
  | none =>
      cases result : consensus ((eligibleSlots input mol single c node data).map
          (generatedReading input mol c node data depth reflected)) with
      | none => rfl
      | some value =>
          have all := ((consensus_eq_some_iff _ _).mp result).2
          have impossible := all _ (List.mem_map.mpr ⟨i, member, rfl⟩)
          rw [readAt] at impossible
          cases impossible
  | some value =>
      apply (consensus_eq_some_iff _ _).mpr
      refine ⟨?_, ?_⟩
      · intro empty
        have present : generatedReading input mol c node data depth reflected i ∈
            (eligibleSlots input mol single c node data).map
              (generatedReading input mol c node data depth reflected) :=
          List.mem_map.mpr ⟨i, member, rfl⟩
        rw [empty] at present
        cases present
      · intro entry entryMem
        obtain ⟨j, jMem, rfl⟩ := List.mem_map.mp entryMem
        exact (same j member jMem).trans readAt

include agreement admissible supported single reached real current historyFixed covered calibrated in
/-- An actual refused step at this covered occurrence has an eligible marked-key tie.
The successful-readings-disagree alternative is excluded by derived covariance. -/
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
  obtain ⟨_, _, failure⟩ := (step_none_iff input mol single cfg c calibrated node data
    agreement admissible supported depth ctx reflected).mp refused
  rcases failure with ⟨slot, member, tie⟩ | ⟨i, memberI, j, memberJ, a, b, first, second, different⟩
  · exact ⟨slot, member, (generatedReading_none_iff input mol single cfg c calibrated node data
      agreement admissible supported depth reflected slot).mpr tie, tie⟩
  · have same := eligible_readings_equal input mol single e c node data agreement admissible
      supported reached real current historyFixed covered cfg calibrated branch cube nontrivial
      depth reflected i j memberI memberJ
    rw [first, second, Option.some.injEq] at same
    exact False.elim (different same.symm)

end
end TetraStereo.OneCenter.LocalizedChemicalRingCoveredThreeCycleConsensus

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredThreeCycleConsensus.reading_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredThreeCycleConsensus.eligible_readings_equal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredThreeCycleConsensus.consensus_eq_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredThreeCycleConsensus.refusal_has_failed_eligible
