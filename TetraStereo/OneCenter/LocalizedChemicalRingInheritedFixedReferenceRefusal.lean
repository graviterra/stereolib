import TetraStereo.OneCenter.LocalizedChemicalRingFixedOccurrenceRefusal
import TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
A proper molecular symmetry fixing a reached occurrence's history and an inherited
reference forces that reference's actual generated reading to refuse if a frame atom moves.
The reference can be distant. Actual child-fact invariance is derived from physical signs,
the recursive evaluator's covariance, and history fixation; it is not a supplied premise.
This applies to the inherited-fallback evaluator at arbitrary occurrence depth, not only roots.
It does not imply refusal of the local fallback consensus or the final descriptor.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingInheritedFixedReferenceRefusal

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingResidualReadingTransport (mapNode_eq_of_history_fixed)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry generated markedKeys)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedDetectedFrames (detected_frame)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedOperationEvaluator (underWith)
open LocalizedGenericMarkedRecalculation (frameAtomsOf appendFacts? mirror)
open LocalizedPhysicalMarkedDistantReference (inheritedRead?)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (proper : ∀ d : input.detectedMultiCenterMolecule.Center,
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (reached : Reached mol node) (real : node.provenance = .realAtom)
  (current : node.atom = c.1.val)
  (historyFixed : ∀ atom ∈ node.history,
    relabelOf input (e : Equiv.Perm input.Atom) atom = atom)
  (reference : input.Atom) (referenceFixed : (e : Equiv.Perm input.Atom) reference = reference)

include agreement admissible supported single calibrated proper reached current historyFixed referenceFixed

/-- The actual generated forest for this inherited reference is invariant under the
symmetry, up to order. No supplied state, label correspondence or oddness is needed. -/
theorem generated_invariant (depth : Nat) (reflected : Bool) :
    (generated input mol node depth reflected reference.val).Perm
      ((generated input mol node depth reflected reference.val).map
        (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))) := by
  have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
    input mol agreement admissible supported e
  have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
    input mol agreement admissible supported single e
  have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
  have mapped := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1
    admissible.1.2 rawSingle cov
  have fixedNode := mapNode_eq_of_history_fixed mol _ node reached historyFixed
  have fixedMark : relabelOf input (e : Equiv.Perm input.Atom) reference.val = reference.val := by
    rw [relabelOf_val, referenceFixed]
  have below := LocalizedChemicalRingResidualOrientationStep.underWith_eq_of_residual_signs
    input mol agreement admissible supported single cfg e calibrated [] node c.1 current.symm
    (by simp) (by simp) reached (fun d _ _ => proper d)
    (sparseOperations input mol) LocalizedChemicalRingInheritedFallback.rawStep?
    (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations input mol))
    depth [] reference.val
  have same : underWith mol (sparseOperations input mol)
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (observedGeometry input reflected))
      [] node (factsWith LocalizedChemicalRingInheritedFallback.rawStep? mol
        (sparseOperations input mol) depth) reference.val =
    generated input mol node depth reflected reference.val := by
    cases reflected with
    | false => exact below.1
    | true => simpa only [observedGeometry, mirror_pullback] using below.2
  have perm := underWith_map LocalizedChemicalRingInheritedFallback.rawStep? sym
    admissible.1.1 admissible.1.2 rawSingle cov mapped depth
    (observedGeometry input reflected) node reached reference.val
  rw [fixedNode, fixedMark, same] at perm
  exact perm

include real in
/-- A nontrivial proper symmetry fixing the history and inherited reference prevents a
strict marked order of the actual generated facts, hence that inherited reading refuses. -/
theorem inheritedReading_none
    (moved : ∃ atom ∈ frameAtomsOf (occurrenceLigandCursors mol node),
      relabelOf input (e : Equiv.Perm input.Atom) atom ≠ atom)
    (depth : Nat) (reflected : Bool) :
    inheritedRead? mol (sparseOperations input mol) (observedGeometry input reflected) [] node
      (generated input mol node depth reflected) reference.val = none := by
  have invariant := generated_invariant input mol agreement admissible supported single cfg e
    calibrated proper c node reached current historyFixed reference referenceFixed depth reflected
  have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
    input mol agreement admissible supported single e
  have frame := detected_frame mol input agreement admissible supported single c node reached real current
  have fixedNode := mapNode_eq_of_history_fixed mol _ node reached historyFixed
  have fixedMark : relabelOf input (e : Equiv.Perm input.Atom) reference.val = reference.val := by
    rw [relabelOf_val, referenceFixed]
  unfold inheritedRead?
  rw [appendFacts_nil_eq]
  split_ifs with unique
  · exact LocalizedChemicalRingFixedOccurrenceRefusal.markedReading_none_of_fixed mol
      (sparseOperations input mol) _ cov node reached _ frame fixedNode reference.val fixedMark
      (generated input mol node depth reflected reference.val) invariant unique moved
      (observedGeometry input reflected)
  · rfl

include real in
/-- The refused actual inherited reading gives a distinct pair of equal actual marked
keys, retaining the generated reference state and occurrence frame. -/
theorem actual_marked_key_tie (data : OccurrenceData input mol c node)
    (moved : ∃ atom ∈ frameAtomsOf (occurrenceLigandCursors mol node),
      relabelOf input (e : Equiv.Perm input.Atom) atom ≠ atom)
    (depth : Nat) (reflected : Bool) :
    ∃ left right : Fin 4, left ≠ right ∧
      markedKeys input mol single c node data
        (generated input mol node depth reflected reference.val) reference left =
      markedKeys input mol single c node data
        (generated input mol node depth reflected reference.val) reference right := by
  apply (LocalizedChemicalRingInheritedReferenceTie.inheritedReading_none_iff input mol
    agreement admissible supported single cfg c (calibrated c) node data depth reflected reference).mp
  exact inheritedReading_none input mol agreement admissible supported single cfg e calibrated proper
    c node reached real current historyFixed reference referenceFixed moved depth reflected

end TetraStereo.OneCenter.LocalizedChemicalRingInheritedFixedReferenceRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFixedReferenceRefusal.generated_invariant
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFixedReferenceRefusal.inheritedReading_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFixedReferenceRefusal.actual_marked_key_tie
