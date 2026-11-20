import TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
Actual refusal under an inherited reference supplies a tie under THAT reference, even when
the reference is distant and not locally eligible. Its generated facts, call depth, geometry
side and full occurrence history are retained. No reference is replaced by a fallback mark.

This strengthens the refusal diagnosis, not the parity conclusion: a reconstructed symmetry
fixing the inherited reference may still induce an even three-cycle on outward ligands.
Physical correction existence and properness at other centers are not claimed here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingCompletenessMarked (strict_iff_injective caseFromMirror?_eq_none_iff)
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedOperationEvaluator (markedReading?)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedPhysicalMarkedDistantReference (inheritedRead?)
open LocalizedGenericMarkedRecalculation (appendFacts? strict readback?)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (c : input.detectedMultiCenterMolecule.Center)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
  (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)

include agreement admissible supported calibrated in
/-- Arbitrary in-range inherited reference, with actual generated insertion and marked
sorting success derived. It need not occur in the current frame or eligible population. -/
theorem inheritedReading_none_iff (depth : Nat) (reflected : Bool) (reference : input.Atom) :
    inheritedRead? mol (sparseOperations input mol) (observedGeometry input reflected) [] node
        (generated input mol node depth reflected) reference.val = none ↔
      ∃ left right : Fin 4, left ≠ right ∧
        markedKeys input mol single c node data
          (generated input mol node depth reflected reference.val) reference left =
        markedKeys input mol single c node data
          (generated input mol node depth reflected reference.val) reference right := by
  have extension := LocalizedChemicalRingCompletenessGeneratedFacts.extension_succeeds
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
    admissible.1.1 (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 depth (observedGeometry input reflected) node reference.val
  change appendFacts? [] (generated input mol node depth reflected reference.val) =
    some (generated input mol node depth reflected reference.val) at extension
  unfold inheritedRead?
  change ((appendFacts? [] (generated input mol node depth reflected reference.val)).bind
    fun temp => markedReading? mol (sparseOperations input mol) (observedGeometry input reflected)
      temp node reference.val) = none ↔ _
  rw [extension, Option.bind_some, marked_reading_eq input mol single c node data]
  let keys := markedKeys input mol single c node data
    (generated input mol node depth reflected reference.val) reference
  by_cases injective : Function.Injective keys
  · obtain ⟨value, success⟩ := readback_some input cfg c calibrated reflected
      (rank input mol c node data keys)
    rw [if_pos injective, success]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨a, b, ne, eq⟩
      exact False.elim (ne (injective eq))
  · rw [if_neg injective]
    constructor
    · intro _
      obtain ⟨a, b, eq, ne⟩ := Function.not_injective_iff.mp injective
      exact ⟨a, b, ne, eq⟩
    · intro _; rfl

include agreement admissible supported single calibrated data in
/-- A refused candidate step cannot have a successful original inherited reading:
the distant policy would use it, and the candidate preserves every such success. -/
theorem inheritedReading_none_of_step_none
    (depth : Nat) (reflected : Bool) (reference : input.Atom)
    (refused : LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input reflected) [] (some reference.val) node
      (generated input mol node depth reflected) = none) :
    inheritedRead? mol (sparseOperations input mol) (observedGeometry input reflected) [] node
      (generated input mol node depth reflected) reference.val = none := by
  have notInj := ((step_none_iff input mol single cfg c calibrated node data
    agreement admissible supported depth (some reference.val) reflected).mp refused).1
  have notStrict : ¬ strict (adjacent input mol single c node data) = true := by
    rw [strict_iff_injective compare completeLigandRule5Key_compare_lt_iff
      completeLigandRule5Key_compare_eq_iff]
    exact notInj
  have tied : strict (adjacent input mol single c node data) = false := by
    cases h : strict (adjacent input mol single c node data) with
    | false => rfl
    | true => exact False.elim (notStrict h)
  cases read : inheritedRead? mol (sparseOperations input mol) (observedGeometry input reflected)
      [] node (generated input mol node depth reflected) reference.val with
  | none => rfl
  | some value =>
      have oldSuccess := LocalizedPhysicalMarkedDistantReference.rawStep_inherited_success
        mol (sparseOperations input mol) (observedGeometry input reflected) [] node
        (generated input mol node depth reflected) data.atoms
        ((order input mol single c node data).map data.read.index)
        (adjacent input mol single c node data) reference.val value data.rawFrame
        (ordinary_eq input mol single c node data) data.nodup
        (consistent_eq input mol single c node data) tied read
      have actual := LocalizedChemicalRingInheritedFallback.rawStep_preserves_some
        mol (sparseOperations input mol) (observedGeometry input reflected) [] (some reference.val)
        node (generated input mol node depth reflected) value oldSuccess
      rw [refused] at actual
      cases actual

include agreement admissible supported calibrated in
/-- The original reference and its actual generated state supply the distinct marked-key tie. -/
theorem step_none_original_reference_tie
    (depth : Nat) (reflected : Bool) (reference : input.Atom)
    (refused : LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input reflected) [] (some reference.val) node
      (generated input mol node depth reflected) = none) :
    ∃ left right : Fin 4, left ≠ right ∧
      markedKeys input mol single c node data
        (generated input mol node depth reflected reference.val) reference left =
      markedKeys input mol single c node data
        (generated input mol node depth reflected reference.val) reference right :=
  (inheritedReading_none_iff input mol agreement admissible supported single cfg c calibrated
    node data depth reflected reference).mp
      (inheritedReading_none_of_step_none input mol agreement admissible supported single cfg c
        calibrated node data depth reflected reference refused)

include agreement admissible supported calibrated in
/-- Descriptor refusal selects an actual failing geometry side and retains the original
inherited reference throughout the resulting comparison witness. -/
theorem descriptor_none_original_reference_tie
    (depth : Nat) (reference : input.Atom)
    (refused : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] (some reference.val) node = none) :
    ∃ (reflected : Bool) (left right : Fin 4),
      LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
        (observedGeometry input reflected) [] (some reference.val) node
        (generated input mol node depth reflected) = none ∧ left ≠ right ∧
      markedKeys input mol single c node data
        (generated input mol node depth reflected reference.val) reference left =
      markedKeys input mol single c node data
        (generated input mol node depth reflected reference.val) reference right := by
  unfold LocalizedChemicalRingInheritedFallback.descriptor? descriptorWith at refused
  rw [caseFromMirror?_eq_none_iff] at refused
  change LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input false) [] (some reference.val) node
      (generated input mol node depth false) = none ∨
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input true) [] (some reference.val) node
      (generated input mol node depth true) = none at refused
  rcases refused with original | mirrored
  · obtain ⟨left, right, ne, tie⟩ := step_none_original_reference_tie input mol agreement
      admissible supported single cfg c calibrated node data depth false reference original
    exact ⟨false, left, right, original, ne, tie⟩
  · obtain ⟨left, right, ne, tie⟩ := step_none_original_reference_tie input mol agreement
      admissible supported single cfg c calibrated node data depth true reference mirrored
    exact ⟨true, left, right, mirrored, ne, tie⟩

include agreement admissible supported calibrated in
/-- Actual-input facade: every carrier/frame/reindex datum is constructed from the reached
real detected occurrence. No selected local reference, key tie or callback success is supplied. -/
theorem reached_descriptor_original_reference_tie
    (reached : Reached mol node) (real : node.provenance = .realAtom)
    (current : node.atom = c.1.val) (depth : Nat) (reference : input.Atom)
    (refused : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] (some reference.val) node = none) :
    ∃ (actual : OccurrenceData input mol c node) (reflected : Bool) (left right : Fin 4),
      LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
        (observedGeometry input reflected) [] (some reference.val) node
        (generated input mol node depth reflected) = none ∧ left ≠ right ∧
      markedKeys input mol single c node actual
        (generated input mol node depth reflected reference.val) reference left =
      markedKeys input mol single c node actual
        (generated input mol node depth reflected reference.val) reference right := by
  obtain ⟨actual⟩ := occurrenceData_exists input mol agreement admissible supported single c node
    reached real current
  obtain ⟨side, left, right, refused, ne, tie⟩ := descriptor_none_original_reference_tie input mol
    agreement admissible supported single cfg c calibrated node actual depth reference refused
  exact ⟨actual, side, left, right, refused, ne, tie⟩

end TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie.inheritedReading_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie.inheritedReading_none_of_step_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie.step_none_original_reference_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie.descriptor_none_original_reference_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedReferenceTie.reached_descriptor_original_reference_tie
