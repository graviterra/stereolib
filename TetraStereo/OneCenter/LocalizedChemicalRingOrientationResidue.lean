import TetraStereo.OneCenter.LocalizedChemicalRingOrientationContexts
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Sharpening the residue: labelled consensus determines the eligible single-reference readings

At an occurrence whose no-context descriptor succeeds, both consensus readings (original and
reflected geometry) are `some`, so every ELIGIBLE single-reference reading equals the consensus
reading (`consensus_eq_some_iff`); hence the single-reference descriptor for an eligible reference
equals the no-context descriptor (`descriptor_ctx_eligible`). A strict ordinary order ignores the
context altogether (`descriptor_ctx_strict`). Consequently consensus label symmetry already gives
adjacent label symmetry at every labelled occurrence for its eligible frame references
(`adjacent_of_consensus_labelled`), eligibility being transported by the accepted covariance.

The adjacent family therefore remains open only in two exceptional situations:
* a frame reference `m` that is NOT eligible at a tied occurrence (its own position is strict while
  other positions tie; the inherited `m` then breaks those ties as a third-party reference);
* an occurrence whose no-context consensus REFUSES while the inherited single reference reads a
  letter.
Everything else in `Symmetric` is determined by the consensus family. This is a statement about the
actual immediate-frame step; no desired output or symmetry is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingOrientationResidue

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingCompletenessMarked (caseFromMirror?_eq_none_iff)
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingOrientationContexts
open LocalizedMarkedOperationEvaluator (Operations markedReading? underWith)
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors (reached_atom_valid)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? consensus appendFacts? mirror
  caseFromMirror? eligibleOf strict consistent)

section Step

variable (mol : RawMolecule) (ops : Operations)

theorem rawStep_ctx_strict (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (under : Nat → OccurrenceAuxState) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary state node = some (sorted, adjacent)) (strictH : strict adjacent = true) :
    LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state ctx node under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state none node under := by
  simp [LocalizedMarkedOperationEvaluator.rawStep?, frame, ordered, strictH]

theorem rawStep_none_consensus (geom : Geometry) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (under : Nat → OccurrenceAuxState) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary state node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (consistentOrder : consistent adjacent = true) (tied : strict adjacent = false) :
    LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state none node under =
      consensus ((eligibleOf atoms sorted adjacent).map fun r =>
        (appendFacts? state (under r)).bind fun temp => markedReading? mol ops geom temp node r) := by
  simp [LocalizedMarkedOperationEvaluator.rawStep?, frame, ordered, nodup, consistentOrder, tied]

/-- An eligible single-reference reading equals a successful consensus. -/
theorem rawStep_eligible_of_consensus (geom : Geometry) (state : OccurrenceAuxState) (m : Nat)
    (node : RawMolecule.CanonicalBranchNode) (under : Nat → OccurrenceAuxState) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary state node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (consistentOrder : consistent adjacent = true) (tied : strict adjacent = false)
    (present : m ∈ atoms) (eligible : m ∈ eligibleOf atoms sorted adjacent) (L : RS)
    (success : LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state none node under = some L) :
    LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state (some m) node under = some L := by
  rw [rawStep_none_consensus mol ops geom state node under atoms sorted adjacent frame ordered nodup
    consistentOrder tied] at success
  rw [rawStep_ctx_adjacent mol ops geom state m node under atoms sorted adjacent frame ordered nodup
    consistentOrder tied present]
  exact ((consensus_eq_some_iff _ _).mp success).2 _ (List.mem_map_of_mem eligible)

/-- A strict ordinary order makes the generated descriptor context-independent. -/
theorem descriptor_ctx_strict (depth : Nat) (geom : Geometry) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary [] node = some (sorted, adjacent)) (strictH : strict adjacent = true) :
    LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] ctx node =
      LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] none node := by
  unfold LocalizedMarkedOperationEvaluator.descriptor? LocalizedMarkedOperationEvaluator.descriptorWith?
    LocalizedMarkedOperationEvaluator.rawWith?
  rw [rawStep_ctx_strict mol ops geom [] ctx node _ atoms sorted adjacent frame ordered strictH,
    rawStep_ctx_strict mol ops (mirror geom) [] ctx node _ atoms sorted adjacent frame ordered strictH]

/-- **A labelled no-context descriptor determines every eligible single-reference descriptor.** -/
theorem descriptor_ctx_eligible (depth : Nat) (geom : Geometry) (m : Nat)
    (node : RawMolecule.CanonicalBranchNode) (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary [] node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (consistentOrder : consistent adjacent = true) (tied : strict adjacent = false)
    (present : m ∈ atoms) (eligible : m ∈ eligibleOf atoms sorted adjacent)
    (x : LocalizedTetrahedralRSPseudoDescriptor)
    (label : LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] none node = some x) :
    LocalizedMarkedOperationEvaluator.descriptor? mol ops depth geom [] (some m) node = some x := by
  unfold LocalizedMarkedOperationEvaluator.descriptor? LocalizedMarkedOperationEvaluator.descriptorWith?
    LocalizedMarkedOperationEvaluator.rawWith? at label ⊢
  cases original : LocalizedMarkedOperationEvaluator.rawStep? mol ops geom [] none node
      (underWith mol ops geom [] node (LocalizedMarkedOperationEvaluator.facts mol ops depth)) with
  | none =>
      rw [original] at label
      cases label
  | some a =>
      cases reflected : LocalizedMarkedOperationEvaluator.rawStep? mol ops (mirror geom) [] none node
          (underWith mol ops (mirror geom) [] node (LocalizedMarkedOperationEvaluator.facts mol ops depth))
          with
      | none =>
          rw [original, reflected] at label
          cases label
      | some b =>
          rw [original, reflected] at label
          rw [rawStep_eligible_of_consensus mol ops geom [] m node _ atoms sorted adjacent frame ordered
            nodup consistentOrder tied present eligible a original,
            rawStep_eligible_of_consensus mol ops (mirror geom) [] m node _ atoms sorted adjacent frame
            ordered nodup consistentOrder tied present eligible b reflected]
          exact label

end Step

/-! ## Consensus symmetry gives adjacent symmetry at labelled occurrences -/

section Transport

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)
  (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)

include agreement admissible supported single atomsPres in
/-- At a reached occurrence with a labelled no-context descriptor, consensus symmetry yields the
adjacent (single-reference) symmetry for every eligible frame reference. -/
theorem adjacent_of_consensus_labelled (g : Geometry)
    (consensusSym : ConsensusSymmetric input mol e g) (depth : Nat)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (ordered : (sparseOperations input mol).ordinary [] node = some (sorted, adjacent))
    (nodup : atoms.Nodup) (consistentOrder : consistent adjacent = true)
    (tied : strict adjacent = false) (m : Nat) (present : m ∈ atoms)
    (eligible : m ∈ eligibleOf atoms sorted adjacent) (x : LocalizedTetrahedralRSPseudoDescriptor)
    (label : LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
      none node = some x) :
    LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some (relabelOf input (e : Equiv.Perm input.Atom) m))
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      LocalizedMarkedOperationEvaluator.descriptor? mol (sparseOperations input mol) depth g []
        (some m) node := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  have valid := reached_atom_valid mol wellFormed node reached
  obtain ⟨atoms', frame', perm⟩ := frameAtoms_map_some sym wellFormed unique rawSingle node atoms
    frame valid
  have rel := cov.ordinary node reached atoms atoms' frame frame'
  rw [ordered] at rel
  cases ordered' : (sparseOperations input mol).ordinary [] (mapNode (relabelOf input
      (e : Equiv.Perm input.Atom)) node) with
  | none => rw [ordered', ordinaryRel_none_some] at rel; exact rel.elim
  | some result' =>
      obtain ⟨sorted', adjacent'⟩ := result'
      rw [ordered', ordinaryRel_some_some] at rel
      obtain ⟨consistentEq, strictEq, _, eligiblePerm⟩ := rel
      have nodup' : atoms'.Nodup :=
        perm.nodup_iff.mpr (nodup.map sym.injective)
      have present' : relabelOf input (e : Equiv.Perm input.Atom) m ∈ atoms' :=
        perm.mem_iff.mpr (List.mem_map_of_mem present)
      have eligible' : relabelOf input (e : Equiv.Perm input.Atom) m ∈
          eligibleOf atoms' sorted' adjacent' :=
        eligiblePerm.mem_iff.mpr (List.mem_map_of_mem eligible)
      have label' := consensusSym depth node reached
      rw [label] at label'
      rw [descriptor_ctx_eligible mol _ depth g m node atoms sorted adjacent frame ordered nodup
        consistentOrder tied present eligible x label,
        descriptor_ctx_eligible mol _ depth g _ _ atoms' sorted' adjacent' frame' ordered' nodup'
        (consistentEq.trans consistentOrder) (strictEq.trans tied) present' eligible' x label']

end Transport

end TetraStereo.OneCenter.LocalizedChemicalRingOrientationResidue

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationResidue.rawStep_eligible_of_consensus
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationResidue.descriptor_ctx_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationResidue.descriptor_ctx_eligible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrientationResidue.adjacent_of_consensus_labelled
