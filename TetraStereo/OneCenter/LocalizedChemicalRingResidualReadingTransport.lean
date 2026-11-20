import TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie
import TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep
import TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
Reading covariance at a reached non-root occurrence, retaining its actual history and call
depth. Proper signs at OTHER centers in the remaining residual component derive the needed
descendant-state equality. Each reference uses its own actually generated forest.

The candidate corollary supplies all step and callback contracts. It assumes neither reader
agreement nor successful insertion, sorting or labels. The physical residual sign hypothesis
is the explicit induction hypothesis; this module does not construct correcting symmetries.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingResidualOrientationStep
open LocalizedChemicalRingInheritedRefusalCases (observedGeometry generated)
open LocalizedChemicalRingWitnessExecution (generated_parent)
open LocalizedMarkedUncappedOperations (generated_of_reachedFrom)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedDetectedFrames (detected_frame)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedOperationEvaluator (markedReading? underWith)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedPhysicalMarkedDistantReference (inheritedRead?)
open LocalizedGenericMarkedRecalculation (frameAtoms? frameAtomsOf appendFacts? readback? mirror readback_mirror)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- A reached node's atom and parent are determined by its history, so pointwise history
fixation fixes the entire raw occurrence, including the original-root parent convention. -/
theorem mapNode_eq_of_history_fixed (mol : RawMolecule) (σ : Nat → Nat) (node : Node)
    (reached : Reached mol node) (fixed : ∀ atom ∈ node.history, σ atom = atom) :
    mapNode σ node = node := by
  obtain ⟨root, _, path⟩ := reached
  have produced := generated_of_reachedFrom mol root node path
  have head := produced.history_head
  have atomFixed := fixed node.atom (List.mem_of_head?_eq_some head)
  have parentHistory := generated_parent produced
  have parentFixed : σ node.parent = node.parent := by
    cases next : node.history.tail.head? with
    | none =>
        rw [next, Option.getD_none] at parentHistory
        simpa only [← parentHistory] using atomFixed
    | some atom =>
        rw [next, Option.getD_some] at parentHistory
        rw [← parentHistory]
        exact fixed atom (List.mem_of_mem_tail (List.mem_of_head?_eq_some next))
  have history : node.history.map σ = node.history := by
    calc
      node.history.map σ = node.history.map id :=
        List.map_congr_left (fun atom member => fixed atom member)
      _ = node.history := List.map_id node.history
  cases node
  simp_all only [mapNode]

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (c : input.detectedMultiCenterMolecule.Center) (node : Node)
  (reached : Reached mol node) (real : node.provenance = .realAtom)
  (current : node.atom = c.1.val)
  (historyFixed : ∀ atom ∈ node.history,
    relabelOf input (e : Equiv.Perm input.Atom) atom = atom)
  (B : List input.Atom) (outside : c.1 ∉ B)
  (carried : ∀ atom ∈ B, atom.val ∈ node.history)
  (proper : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph B c.1 d.1 → d.1 ≠ c.1 →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1)

/-- Actual generated reading for a generic shared-recursion step. -/
noncomputable def readingAt (step : Step) (depth : Nat) (reflected : Bool) (reference : input.Atom) :
    Option RS :=
  inheritedRead? mol (sparseOperations input mol) (observedGeometry input reflected) [] node
    (underWith mol (sparseOperations input mol) (observedGeometry input reflected) [] node
      (factsWith step mol (sparseOperations input mol) depth)) reference.val

include agreement admissible supported single calibrated reached current in
/-- The same local sign transports readbacks under both the original and mirrored geometry. -/
theorem frame_readback_flip (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (reflected : Bool) (L : List Nat) (subset : ∀ x ∈ L, x ∈ atoms) :
    readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
        (observedGeometry input reflected)) L =
      flipBy (relativeSign input.detectedMultiCenterMolecule cfg e c)
        (readback? (observedGeometry input reflected) L) := by
  have original := readback_pullback_frame input mol agreement admissible supported single
    cfg e calibrated c node current reached atoms frame L subset
  cases reflected with
  | false => exact original
  | true =>
      change readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
        (mirror (inputGeometry input))) L =
          flipBy (relativeSign input.detectedMultiCenterMolecule cfg e c)
            (readback? (mirror (inputGeometry input)) L)
      rw [← mirror_pullback, readback_mirror, readback_mirror, original, flipBy_map_swap]

include agreement admissible supported single calibrated reached real current historyFixed
  outside carried proper in
/-- Actual reading transport, with descendant-state equality derived from finite residual
properness. No root-address, involution, state-match or successful-reading premise is used. -/
theorem inheritedReading_transport (step : Step)
    (stepMap : StepMap step mol (sparseOperations input mol)
      (relabelOf input (e : Equiv.Perm input.Atom)))
    (stepCongr : StepCongr step mol (sparseOperations input mol))
    (depth : Nat) (reflected : Bool) (reference : input.Atom) :
    readingAt input mol node step depth reflected ((e : Equiv.Perm input.Atom) reference) =
      flipBy (relativeSign input.detectedMultiCenterMolecule cfg e c)
        (readingAt input mol node step depth reflected reference) := by
  have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
    input mol agreement admissible supported e
  have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
    input mol agreement admissible supported single e
  have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
  have fixedNode := mapNode_eq_of_history_fixed mol _ node reached historyFixed
  have frame := detected_frame mol input agreement admissible supported single c node reached real current
  have frame' : frameAtoms? mol
      (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
        some (frameAtomsOf (occurrenceLigandCursors mol node)) := by
    rw [fixedNode]
    exact frame
  have below := underWith_eq_of_residual_signs input mol agreement admissible supported single
    cfg e calibrated B node c.1 current.symm outside carried reached proper
    (sparseOperations input mol) step stepCongr depth [] reference.val
  have same : underWith mol (sparseOperations input mol)
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (observedGeometry input reflected))
      [] node (factsWith step mol (sparseOperations input mol) depth) reference.val =
    underWith mol (sparseOperations input mol) (observedGeometry input reflected)
      [] node (factsWith step mol (sparseOperations input mol) depth) reference.val := by
    cases reflected
    · exact below.1
    · exact below.2
  have perm := underWith_map step sym admissible.1.1 admissible.1.2 rawSingle cov
    stepMap depth (observedGeometry input reflected) node reached reference.val
  rw [fixedNode, same] at perm
  have transported := evaluate_map sym cov node reached _ _ frame frame'
    (underWith mol (sparseOperations input mol) (observedGeometry input reflected) [] node
      (factsWith step mol (sparseOperations input mol) depth) reference.val)
    (underWith mol (sparseOperations input mol) (observedGeometry input reflected) [] node
      (factsWith step mol (sparseOperations input mol) depth)
        (relabelOf input (e : Equiv.Perm input.Atom) reference.val))
    perm reference.val (observedGeometry input reflected)
  rw [fixedNode, relabelOf_val] at transported
  calc
    readingAt input mol node step depth reflected ((e : Equiv.Perm input.Atom) reference) =
        ((appendFacts? [] (underWith mol (sparseOperations input mol)
          (observedGeometry input reflected) [] node
          (factsWith step mol (sparseOperations input mol) depth) reference.val)).bind fun temp =>
            markedReading? mol (sparseOperations input mol)
              (pullback (relabelOf input (e : Equiv.Perm input.Atom))
                (observedGeometry input reflected)) temp node reference.val) := transported
    _ = _ := evaluate_flip mol (sparseOperations input mol)
      (relativeSign input.detectedMultiCenterMolecule cfg e c)
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (observedGeometry input reflected))
      (observedGeometry input reflected) node _ frame
      (frame_readback_flip input mol agreement admissible supported single cfg e calibrated c node
        reached current _ frame reflected)
      [] (underWith mol (sparseOperations input mol) (observedGeometry input reflected) [] node
        (factsWith step mol (sparseOperations input mol) depth)) reference.val

include agreement admissible supported single calibrated reached real current historyFixed
  outside carried proper in
/-- The actual isolated candidate supplies its own covariance and frame-congruence laws.
All inherited/local references and both geometry sides are included. -/
theorem candidate_reading_transport (depth : Nat) (reflected : Bool) (reference : input.Atom) :
    inheritedRead? mol (sparseOperations input mol) (observedGeometry input reflected) [] node
        (generated input mol node depth reflected) ((e : Equiv.Perm input.Atom) reference).val =
      if relativeSign input.detectedMultiCenterMolecule cfg e c = 1 then
        inheritedRead? mol (sparseOperations input mol) (observedGeometry input reflected) [] node
          (generated input mol node depth reflected) reference.val
      else (inheritedRead? mol (sparseOperations input mol) (observedGeometry input reflected) [] node
          (generated input mol node depth reflected) reference.val).map RS.swap := by
  have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
    input mol agreement admissible supported e
  have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
    input mol agreement admissible supported single e
  have mapped := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single) cov
  exact inheritedReading_transport input mol agreement admissible supported single cfg e calibrated
    c node reached real current historyFixed B outside carried proper
    LocalizedChemicalRingInheritedFallback.rawStep? mapped
    (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations input mol))
    depth reflected reference

end TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport.mapNode_eq_of_history_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport.frame_readback_flip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport.inheritedReading_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport.candidate_reading_transport
