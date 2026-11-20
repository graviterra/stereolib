import TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Finite residual physical signs control every actual prepared child state. This includes
ring duplicates and all inherited lists. At the current frame, calibration supplies the
remaining sign, so two successful equal labels force properness. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedResidualDecoder

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingResidualOrientationStep (agreeOn_strictDescendants)
open LocalizedChemicalRingJointPreparedGeometryCongruence (preparedFacts_congr)
open LocalizedChemicalRingJointPreparedGeometryFlip (preparedDescriptor_flip)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations)
open LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (frameAtoms? mirror flatMap_congr_mem)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
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
  (B : List input.Atom) (source : RawMolecule.CanonicalBranchNode)
  (entry : input.Atom) (entryEq : entry.val = source.atom) (outside : entry ∉ B)
  (carried : ∀ atom ∈ B, atom.val ∈ source.history) (sourceReached : Reached mol source)
  (proper : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph B entry d.1 → d.1 ≠ entry →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1)


include agreement admissible supported single calibrated entryEq outside carried sourceReached proper in
/-- Actual child continuations agree at every reference context, on each geometry side. -/
theorem childrenUnder_eq_of_residual_signs (ops : MultiOperations) (depth : Nat)
    (state : OccurrenceAuxState) (M : List Nat) :
    childrenUnder mol (preparedFacts mol ops depth)
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input))
        state source M =
      childrenUnder mol (preparedFacts mol ops depth) (inputGeometry input) state source M ∧
    childrenUnder mol (preparedFacts mol ops depth)
        (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)))
        state source M =
      childrenUnder mol (preparedFacts mol ops depth) (mirror (inputGeometry input)) state source M := by
  have agree := agreeOn_strictDescendants input mol agreement admissible supported single cfg e
    calibrated B source entry entryEq outside carried sourceReached proper
  have closed : ∀ parent child, StrictDescendant mol source parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol source child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  constructor
  · unfold childrenUnder
    exact flatMap_congr_mem _ _ _ fun child member =>
      preparedFacts_congr mol ops (StrictDescendant mol source) closed depth _ _ agree
        state M child ⟨child, member, .refl⟩
  · unfold childrenUnder
    exact flatMap_congr_mem _ _ _ fun child member =>
      preparedFacts_congr mol ops (StrictDescendant mol source) closed depth _ _ agree.mirror
        state M child ⟨child, member, .refl⟩

include agreement admissible supported single calibrated entryEq outside carried sourceReached proper in
/-- The actual prepared descriptor transforms by the current physical sign; descendant
state equality is derived from finite residual properness, at every context. -/
theorem descriptor_flip_of_residual_signs (ops : MultiOperations)
    (d : input.detectedMultiCenterMolecule.Center) (atomEq : source.atom = d.1.val)
    (atoms : List Nat) (frame : frameAtoms? mol source = some atoms)
    (depth : Nat) (state : OccurrenceAuxState) (M : List Nat) :
    preparedDescriptor? mol ops depth
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input))
        state M source =
      flipDescriptorBy (relativeSign input.detectedMultiCenterMolecule cfg e d)
        (preparedDescriptor? mol ops depth (inputGeometry input) state M source) := by
  have below := childrenUnder_eq_of_residual_signs input mol agreement admissible supported single
    cfg e calibrated B source entry entryEq outside carried sourceReached proper ops depth state
  exact preparedDescriptor_flip mol ops (relativeSign input.detectedMultiCenterMolecule cfg e d)
    _ _ depth source atoms frame
    (readback_pullback_frame input mol agreement admissible supported single cfg e calibrated
      d source atomEq sourceReached atoms frame)
    state M (fun L => (below L).1) (fun L => (below L).2)

include agreement admissible supported single calibrated entryEq outside carried sourceReached proper in
/-- Successful identical actual labels imply a proper physical sign at this center. -/
theorem relativeSign_eq_one_of_residual_signs (ops : MultiOperations)
    (d : input.detectedMultiCenterMolecule.Center) (atomEq : source.atom = d.1.val)
    (atoms : List Nat) (frame : frameAtoms? mol source = some atoms)
    (depth : Nat) (state : OccurrenceAuxState) (M : List Nat)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (original : preparedDescriptor? mol ops depth (inputGeometry input) state M source = some label)
    (pulled : preparedDescriptor? mol ops depth
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state M source =
        some label) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have flip := descriptor_flip_of_residual_signs input mol agreement admissible supported single
    cfg e calibrated B source entry entryEq outside carried sourceReached proper ops d atomEq
    atoms frame depth state M
  rw [original, pulled] at flip
  exact flipDescriptorBy_some_eq _ (relativeSign_eq_one_or_neg_one _ cfg e d) label flip.symm

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedResidualDecoder

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedResidualDecoder.childrenUnder_eq_of_residual_signs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedResidualDecoder.descriptor_flip_of_residual_signs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedResidualDecoder.relativeSign_eq_one_of_residual_signs
