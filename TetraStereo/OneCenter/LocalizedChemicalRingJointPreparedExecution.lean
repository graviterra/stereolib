import TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextFacts
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Actual execution on the prepared joint-context state

All frame, sorting and fact-insertion failures are eliminated from the concrete prepared step.
Its alternatives are an injective joint-key order read from coordinates, or consensus of the
eligible extended-context readings. Each extension uses its own generated child state.
On calibrated coordinates, a fallback refuses exactly when its actual keys are noninjective.
These are execution results, not a proof that the generated labels have physical meaning.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingPreparedContextRecursion LocalizedChemicalRingPreparedContextFacts
open LocalizedChemicalRingJointMarkerOperations LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointMarkerFrameExecution
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt rank observedGeometry)
open LocalizedChemicalRingCompletenessMarked (enumeration strict_iff_injective)
open LocalizedChemicalRingCompletenessStrict (consistent_of_gt_or_eq)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedRetainedOrdinaryRanking (adjacentBy_key_consistent keyOrder_pairwise)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)

/-- The actual same-context child facts, starting from the empty incoming state. -/
def generated (depth : Nat) (geom : Geometry) (node : RawMolecule.CanonicalBranchNode)
    (references : List input.Atom) : OccurrenceAuxState :=
  childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) geom [] node
    (references.map Fin.val)

variable (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (depth : Nat) (geom : Geometry)
  (references : List input.Atom)

abbrev keys := slotKeys input mol single c node data
  (generated input mol depth geom node references) references

/-- One actual fallback, indexed by a certified frame slot. -/
def fallback (slot : Fin 4) : Option RS :=
  evaluateFallback? mol (jointOperations input mol) geom [] node (references.map Fin.val)
    (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) geom [] node)
    (referenceAt input mol c node data slot).val

include agreement admissible supported in
/-- An extended reading uses precisely the facts generated under that extended context. -/
theorem fallback_eq (slot : Fin 4) :
    fallback input mol c node data depth geom references slot =
      if Function.Injective (keys input mol single c node data depth geom
          (references ++ [referenceAt input mol c node data slot])) then
        readback? geom (enumeration input c (rank input mol c node data
          (keys input mol single c node data depth geom
            (references ++ [referenceAt input mol c node data slot]))))
      else none := by
  unfold fallback
  rw [preparedStep_fallback_uses_generated_children mol (jointOperations input mol)
    admissible.1.1 (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 depth geom node (references.map Fin.val)]
  simpa only [keys, generated, List.map_append, List.map_cons, List.map_nil] using
    markedReadingJoint?_eq input mol single c node data
      (generated input mol depth geom node (references ++ [referenceAt input mol c node data slot]))
      (references ++ [referenceAt input mol c node data slot]) geom
      (referenceAt input mol c node data slot).val

/-- The raw call in the actual prepared descriptor and facts recursion. -/
def step : Option RS :=
  rawStepPrepared? (jointOperations input mol) mol geom [] (references.map Fin.val) node
    (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth) geom [] node)

/-- The actual descriptor compares raw results, each generated using its own geometry. -/
theorem descriptor_eq :
    preparedDescriptor? mol (jointOperations input mol) depth geom [] (references.map Fin.val) node =
      caseFromMirror? (step input mol node depth geom references)
        (step input mol node depth (mirror geom) references) := rfl

/-- Descriptor refusal retains which raw geometry failed. -/
theorem descriptor_none_iff :
    preparedDescriptor? mol (jointOperations input mol) depth geom [] (references.map Fin.val) node = none ↔
      step input mol node depth geom references = none ∨
      step input mol node depth (mirror geom) references = none := by
  rw [descriptor_eq, LocalizedChemicalRingCompletenessMarked.caseFromMirror?_eq_none_iff]

include agreement admissible supported in
/-- Concrete execution with no assumed successful sort, frame, or fact insertion. -/
theorem step_eq :
    step input mol node depth geom references =
      if Function.Injective (keys input mol single c node data depth geom references) then
        readback? geom (enumeration input c
          (rank input mol c node data (keys input mol single c node data depth geom references)))
      else consensus ((selectedSlots input mol single c node data
          (generated input mol depth geom node references) references).map
        (fallback input mol c node data depth geom references)) := by
  unfold step
  rw [preparedStep_compares_on_generated_children mol (jointOperations input mol)
    admissible.1.1 (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 depth geom node (references.map Fin.val) data.atoms data.rawFrame]
  change comparisonAt? _ _ _ _ _ _ _ _ (generated input mol depth geom node references) = _
  unfold comparisonAt?
  simp only [jointOperations]
  rw [contextOrder?_eq input mol single c node data
    (generated input mol depth geom node references) references]
  dsimp only
  have consistentAdj : consistent (slotAdjacent input mol single c node data
      (generated input mol depth geom node references) references) = true :=
    consistent_of_gt_or_eq _ (adjacentBy_key_consistent compare
      refined_compare_lt_iff refined_compare_eq_iff _ _ (keyOrder_pairwise _ _))
  have good : ¬ (¬ data.atoms.Nodup ∨ consistent (slotAdjacent input mol single c node data
      (generated input mol depth geom node references) references) = false) := by
    simp [data.nodup, consistentAdj]
  rw [if_neg good]
  by_cases inj : Function.Injective (keys input mol single c node data depth geom references)
  · rw [if_pos ((strict_iff_injective compare refined_compare_lt_iff
      refined_compare_eq_iff _).mpr inj), if_pos inj]
    rw [LocalizedChemicalRingInheritedRefusalCases.ranked_eq input mol c node data
      (keys input mol single c node data depth geom references)]
    rfl
  · rw [if_neg (fun h => inj ((strict_iff_injective compare refined_compare_lt_iff
      refined_compare_eq_iff _).mp h)), if_neg inj]
    rw [eligible_eq input mol single c node data
      (generated input mol depth geom node references) references, List.map_map]
    rfl

variable (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
  (reflected : Bool)

include agreement admissible supported calibrated in
/-- On calibrated geometry, refusal of an actual fallback is exactly a tie of its actual keys. -/
theorem fallback_none_iff (slot : Fin 4) :
    fallback input mol c node data depth (observedGeometry input reflected) references slot = none ↔
      ¬ Function.Injective (keys input mol single c node data depth (observedGeometry input reflected)
        (references ++ [referenceAt input mol c node data slot])) := by
  rw [fallback_eq input mol agreement admissible supported single c node data depth]
  obtain ⟨value, computed⟩ := LocalizedChemicalRingInheritedRefusalCases.readback_some
    input cfg c calibrated reflected (rank input mol c node data
      (keys input mol single c node data depth (observedGeometry input reflected)
        (references ++ [referenceAt input mol c node data slot])))
  by_cases inj : Function.Injective (keys input mol single c node data depth
      (observedGeometry input reflected) (references ++ [referenceAt input mol c node data slot]))
  · simp [inj, computed]
  · simp [inj]

include agreement admissible supported calibrated in
/-- A prepared raw refusal has a noninjective current-context key partition. Consensus failure
is still allowed; no assertion that an individual fallback must fail is made here. -/
theorem step_none_noninjective
    (refused : step input mol node depth (observedGeometry input reflected) references = none) :
    ¬ Function.Injective (keys input mol single c node data depth
      (observedGeometry input reflected) references) := by
  intro inj
  rw [step_eq input mol agreement admissible supported single c node data depth,
    if_pos inj] at refused
  obtain ⟨value, computed⟩ := LocalizedChemicalRingInheritedRefusalCases.readback_some
    input cfg c calibrated reflected (rank input mol c node data
      (keys input mol single c node data depth (observedGeometry input reflected) references))
  rw [computed] at refused
  cases refused

include agreement admissible supported calibrated in
/-- A descriptor refusal gives an actual same-context tie on at least one of its two geometries.
This does not silently transfer a reflected failure to the unreflected generated state. -/
theorem descriptor_none_noninjective
    (refused : preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) []
      (references.map Fin.val) node = none) :
    ∃ reflected : Bool, ¬ Function.Injective (keys input mol single c node data depth
      (observedGeometry input reflected) references) := by
  rcases (descriptor_none_iff input mol node depth (inputGeometry input) references).mp refused with h | h
  · exact ⟨false, step_none_noninjective input mol agreement admissible supported single c node data
      depth references cfg calibrated false h⟩
  · exact ⟨true, step_none_noninjective input mol agreement admissible supported single c node data
      depth references cfg calibrated true h⟩

include agreement admissible supported calibrated in
/-- Once covariance has established that every selected reading agrees, a refusal supplies
an individually failed reading. The agreement hypothesis is explicit and must be proved by
the physical symmetry argument; existence of an arbitrary even automorphism is insufficient. -/
theorem step_none_failed_of_equal_readings
    (refused : step input mol node depth (observedGeometry input reflected) references = none)
    (equal : ∀ a ∈ selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references) references,
      ∀ b ∈ selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references) references,
      fallback input mol c node data depth (observedGeometry input reflected) references a =
        fallback input mol c node data depth (observedGeometry input reflected) references b) :
    ∃ slot ∈ selectedSlots input mol single c node data
        (generated input mol depth (observedGeometry input reflected) node references) references,
      fallback input mol c node data depth (observedGeometry input reflected) references slot = none := by
  have notInj := step_none_noninjective input mol agreement admissible supported single c node data
    depth references cfg calibrated reflected refused
  have nonempty := selectedSlots_nonempty input mol single c node data
    (generated input mol depth (observedGeometry input reflected) node references) references notInj
  obtain ⟨slot, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  cases found : fallback input mol c node data depth (observedGeometry input reflected) references slot with
  | none => exact ⟨slot, member, found⟩
  | some value =>
      have all : ∀ other ∈ selectedSlots input mol single c node data
          (generated input mol depth (observedGeometry input reflected) node references) references,
          fallback input mol c node data depth (observedGeometry input reflected) references other =
            some value := by
        intro other present
        exact (equal other present slot member).trans found
      have success := LocalizedChemicalRingCompletenessMarked.consensus_map_const _ nonempty _ value all
      rw [step_eq input mol agreement admissible supported single c node data depth,
        if_neg notInj, success] at refused
      cases refused

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.fallback_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.step_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.fallback_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.step_none_noninjective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.descriptor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.descriptor_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.descriptor_none_noninjective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.step_none_failed_of_equal_readings
