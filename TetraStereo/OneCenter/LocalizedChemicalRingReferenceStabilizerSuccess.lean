import TetraStereo.OneCenter.LocalizedChemicalRingSelectedRefusalWitness
import TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Finite graph rigidity can certify an alternate occurrence's actual descriptor success
without evaluating the whole carrier or generated state. A refused call would reconstruct
a history/reference-fixing automorphism moving two actual outward attachments. A trivial
reference stabilizer rules this out. The finite rigidity hypothesis is independent of
coordinates, generated labels and comparisons; it still must be proved for an input.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceStabilizerSuccess

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (c : input.detectedMultiCenterMolecule.Center)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
  (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
  (branch : TiedRootBranch input data.target) (depth : Nat) (reference : input.Atom)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (rigid : ∀ e : input.detectedMultiCenterMolecule.Aut,
    (∀ atom ∈ node.history, relabelOf input (e : Equiv.Perm input.Atom) atom = atom) →
    (e : Equiv.Perm input.Atom) reference = reference → e = 1)

include agreement admissible supported single calibrated branch charge rigid in
/-- Actual generated descriptor success from the finite graph's history/reference
stabilizer. No key injectivity, selected-reference, or successful-label premise is supplied. -/
theorem descriptor_ne_none :
    LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] (some reference.val) node ≠ none := by
  intro refused
  obtain ⟨side, left, right, a, b, _, different, ⟨w⟩⟩ := selected_refusal_matched_symmetry
    input mol agreement admissible supported single cfg c calibrated node data branch depth
    reference charge refused
  have fixed : ∀ atom ∈ node.history,
      relabelOf input (w.symmetry : Equiv.Perm input.Atom) atom = atom := by
    intro value member
    have correspondence := LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found
    rw [← correspondence.history] at member
    obtain ⟨atom, present, valueEq⟩ := List.mem_map.mp member
    rw [← valueEq, relabelOf_val, w.fixedHistory atom present]
  have trivial := rigid w.symmetry fixed w.fixedReference
  have same := w.entry
  rw [trivial] at same
  exact different same

include agreement admissible supported single calibrated branch charge rigid in
theorem descriptor_exists :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] (some reference.val) node = some value := by
  cases result : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] (some reference.val) node with
  | none => exact False.elim (descriptor_ne_none input mol agreement admissible supported single
      cfg c calibrated node data branch depth reference charge rigid result)
  | some value => exact ⟨value, rfl⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceStabilizerSuccess

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceStabilizerSuccess.descriptor_ne_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceStabilizerSuccess.descriptor_exists
