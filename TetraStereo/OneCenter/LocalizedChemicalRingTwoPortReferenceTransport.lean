import TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection
import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
The exceptional reference orbit of an odd correction is visible at its earlier selector:
its four-slot action is exactly a transposition, its physical sign there is negative,
and the exchanged references have equal ACTUAL ordinary keys and are both eligible.

This identifies the remaining two-reference comparison; it does not equate the two
generated descendant states. Eligibility at the selector alone does not imply agreement
of descriptors computed under its two references at a deeper occurrence.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingTwoPortReferenceTransport

open LocalizedPhysicalMarkedParityCompleteness
open LocalizedChemicalRingFinalEntryCorrection
open LocalizedChemicalRingMovedSlotEligibility
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSelectedParentEligibility
open LocalizedChemicalRingPhysicalSense (relabelOf)
open LocalizedMarkedReachableConfigurations (Reached)

/-- One fixed slot and a genuine two-cycle leave no other nontrivial slot action. -/
theorem two_port_is_transposition (p : Equiv.Perm (Fin 4)) (entry reference : Fin 4)
    (fixed : p entry = entry) (changed : p reference ≠ reference)
    (twice : p (p reference) = reference) : p = Equiv.swap reference (p reference) := by
  have finite : ∀ (q : Equiv.Perm (Fin 4)) (a r : Fin 4), q a = a → q r ≠ r →
      q (q r) = r → q = Equiv.swap r (q r) := by decide +kernel
  exact finite p entry reference fixed changed twice

theorem two_port_odd (p : Equiv.Perm (Fin 4)) (entry reference : Fin 4)
    (fixed : p entry = entry) (changed : p reference ≠ reference)
    (twice : p (p reference) = reference) : permHandedness p = -1 := by
  have shape := two_port_is_transposition p entry reference fixed changed twice
  unfold permHandedness
  rw [shape, Equiv.Perm.sign_swap (Ne.symm changed)]
  norm_num

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The parity at the selector follows from actual neighbor transport, not an assumed
relation between the signs at the selector and the later corrected center. -/
theorem selector_odd (m : MultiCenterMolecule V) (g : m.Aut) (selector : m.Center)
    (entry : Fin 4) (fixed : m.centerPerm g selector = selector)
    (entryFixed : (g : Equiv.Perm V) (m.ligandAtomAt selector entry) =
      m.ligandAtomAt selector entry)
    (reference : V) (adjacent : m.mol.Adj selector.1 reference)
    (changed : (g : Equiv.Perm V) reference ≠ reference)
    (twice : (g : Equiv.Perm V) ((g : Equiv.Perm V) reference) = reference) :
    permHandedness (m.ligandPermAt g selector) = -1 := by
  obtain ⟨r, atReference⟩ := m.ligandAtomAt_surjective selector reference adjacent
  have image (i : Fin 4) :
      m.ligandAtomAt selector (m.ligandPermAt g selector i) =
        (g : Equiv.Perm V) (m.ligandAtomAt selector i) := by
    simpa only [fixed] using m.ligandAtomAt_ligandPermAt g selector i
  have moved : m.ligandPermAt g selector r ≠ r := by
    intro same
    have h := image r
    rw [same, atReference] at h
    exact changed h.symm
  have squared : m.ligandPermAt g selector (m.ligandPermAt g selector r) = r := by
    apply m.ligandAtomAt_injective selector
    rw [image, image, atReference, twice]
  exact two_port_odd _ entry r (slot_fixed m g selector entry fixed entryFixed) moved squared

theorem selector_negative (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (selector : m.Center) (entry : Fin 4)
    (fixed : m.centerPerm g selector = selector)
    (entryFixed : (g : Equiv.Perm V) (m.ligandAtomAt selector entry) =
      m.ligandAtomAt selector entry)
    (reference : V) (adjacent : m.mol.Adj selector.1 reference)
    (changed : (g : Equiv.Perm V) reference ≠ reference)
    (twice : (g : Equiv.Perm V) ((g : Equiv.Perm V) reference) = reference) :
    relativeSign m cfg g selector = -1 := by
  have odd := selector_odd m g selector entry fixed entryFixed reference adjacent changed twice
  have square := permHandedness_mul_self (cfg selector)
  unfold relativeSign transportedSign
  rw [fixed, odd]
  change permHandedness (cfg selector) * -1 * permHandedness (cfg selector) = -1
  nlinarith

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (g : input.detectedMultiCenterMolecule.Aut)
  (selector : input.detectedMultiCenterMolecule.Center)
  (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol selector node)
  (reached : Reached mol node)
  (historyFixed : ∀ atom ∈ node.history,
    relabelOf input (g : Equiv.Perm input.Atom) atom = atom)

include agreement admissible supported reached historyFixed in
/-- The exchanged references tie in the actual selector keys; both actual eligibility
memberships are consequences. No supplied key equality or selection premise occurs. -/
theorem actual_reference_pair (reference : input.Atom)
    (adjacent : input.moleculeGraph.Adj selector.1 reference)
    (changed : (g : Equiv.Perm input.Atom) reference ≠ reference) :
    ∃ i j : Fin 4, i ≠ j ∧
      referenceAt input mol selector node data i = reference ∧
      referenceAt input mol selector node data j = (g : Equiv.Perm input.Atom) reference ∧
      ordinaryKeys input mol single selector node data i =
        ordinaryKeys input mol single selector node data j ∧
      i ∈ eligibleSlots input mol single selector node data ∧
      j ∈ eligibleSlots input mol single selector node data := by
  obtain ⟨p, images, keys⟩ := actual_slot_key_action input mol agreement admissible supported single
    g selector node data reached historyFixed
  obtain ⟨r, atReference⟩ := input.detectedMultiCenterMolecule.ligandAtomAt_surjective
    selector reference adjacent
  let i := data.ligandOf.symm r
  have first : referenceAt input mol selector node data i = reference := by
    simp only [referenceAt, i, Equiv.apply_symm_apply, atReference]
  have second : referenceAt input mol selector node data (p i) =
      (g : Equiv.Perm input.Atom) reference := by rw [images, first]
  have different : p i ≠ i := by
    intro same
    rw [same, first] at second
    exact changed second.symm
  exact ⟨i, p i, different.symm, first, second, (keys i).symm,
    (eligible_iff_other input mol single selector node data i).mpr ⟨p i, different, keys i⟩,
    (eligible_iff_other input mol single selector node data (p i)).mpr
      ⟨i, different.symm, (keys i).symm⟩⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingTwoPortReferenceTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPortReferenceTransport.two_port_is_transposition
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPortReferenceTransport.two_port_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPortReferenceTransport.selector_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPortReferenceTransport.selector_negative
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoPortReferenceTransport.actual_reference_pair
