import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation
import TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
Actual inherited readings at a reached occurrence whose history contains every detected
center transform by the physical sign at that occurrence. Descendant readback agreement
is derived from history coverage. Only the source and image frames need calibration;
no physical signs at other centers, generated-state agreement or reading success are assumed.
This is a terminal step for physical reconstruction, not full ring completeness.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCoveredReadingTransport

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingCoveredPathOrientation LocalizedChemicalRingWitnessExecution
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedChemicalRingResidualReadingTransport (mapNode_eq_of_history_fixed readingAt)
open LocalizedChemicalRingInheritedRefusalCases (observedGeometry generated)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedDetectedFrames (detected_frame)
open LocalizedMarkedOperationEvaluator (Operations underWith mem_tiedChildren_actual)
open LocalizedGenericMarkedRecalculation (frameAtoms? frameAtomsOf mirror readback? readback_mirror
  appendFacts? flatMap_congr_mem)
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
  (c : input.detectedMultiCenterMolecule.Center)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
  (imageCalibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg
    (input.detectedMultiCenterMolecule.centerPerm e c))
  (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
  (real : node.provenance = .realAtom) (current : node.atom = c.1.val)
  (historyFixed : ∀ atom ∈ node.history, relabelOf input (e : Equiv.Perm input.Atom) atom = atom)
  (covered : ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val ∈ node.history)

include agreement admissible supported single reached covered in
/-- Both geometry-side descendant forests agree because no real descendant can revisit
a detected center. This holds for every continuation with the frame-congruence law. -/
theorem underWith_eq_of_covered (ops : Operations) (step : Step)
    (stepCongr : StepCongr step mol ops) (depth : Nat) (state : OccurrenceAuxState)
    (reflected : Bool) (reference : Nat) :
    underWith mol ops
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (observedGeometry input reflected))
        state node (factsWith step mol ops depth) reference =
      underWith mol ops (observedGeometry input reflected) state node
        (factsWith step mol ops depth) reference := by
  have agree := agreeOn_of_covered input mol agreement admissible supported single e node reached covered
  have closed : ∀ parent child, StrictDescendant mol node parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol node child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  have atSide : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (observedGeometry input reflected))
      (observedGeometry input reflected) := by
    cases reflected with
    | false => exact agree
    | true => simpa only [observedGeometry, mirror_pullback] using agree.mirror
  unfold underWith
  apply flatMap_congr_mem
  intro child member
  exact factsWith_congr step (StrictDescendant mol node) closed stepCongr depth _ _ atSide
    state (some reference) child ⟨child, mem_tiedChildren_actual mol ops state node child member, .refl⟩

include agreement admissible supported single calibrated imageCalibrated reached real current
  historyFixed covered in
/-- Actual reference covariance with descendant-state equality derived from coverage. -/
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
  have same := underWith_eq_of_covered input mol agreement admissible supported single e
    node reached covered (sparseOperations input mol) step stepCongr depth [] reflected reference.val
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
  have frameFlip : ∀ L, (∀ x ∈ L, x ∈ frameAtomsOf (occurrenceLigandCursors mol node)) →
      readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
        (observedGeometry input reflected)) L =
        flipBy (relativeSign input.detectedMultiCenterMolecule cfg e c)
          (readback? (observedGeometry input reflected) L) := by
    intro L subset
    have original := readback_pullback_local input mol agreement admissible supported single cfg e c
      calibrated imageCalibrated node current reached _ frame L subset
    cases reflected with
    | false => exact original
    | true =>
        change readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
          (mirror (inputGeometry input))) L =
          flipBy (relativeSign input.detectedMultiCenterMolecule cfg e c)
            (readback? (mirror (inputGeometry input)) L)
        rw [← mirror_pullback, readback_mirror, readback_mirror, original, flipBy_map_swap]
  exact transported.trans (evaluate_flip mol (sparseOperations input mol)
    (relativeSign input.detectedMultiCenterMolecule cfg e c)
    (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (observedGeometry input reflected))
    (observedGeometry input reflected) node _ frame frameFlip
    [] (underWith mol (sparseOperations input mol) (observedGeometry input reflected) [] node
      (factsWith step mol (sparseOperations input mol) depth)) reference.val)

include agreement admissible supported single calibrated imageCalibrated reached real current
  historyFixed covered in
/-- The actual inherited-fallback recursion supplies its own map and congruence laws. -/
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
  exact inheritedReading_transport input mol agreement admissible supported single cfg e c
    calibrated imageCalibrated node reached real current historyFixed covered
    LocalizedChemicalRingInheritedFallback.rawStep? mapped
    (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations input mol))
    depth reflected reference

end TetraStereo.OneCenter.LocalizedChemicalRingCoveredReadingTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredReadingTransport.underWith_eq_of_covered
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredReadingTransport.inheritedReading_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredReadingTransport.candidate_reading_transport
