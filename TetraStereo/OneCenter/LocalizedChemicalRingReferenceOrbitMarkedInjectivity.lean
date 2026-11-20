import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSeparationCertificate
import TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
All four actual marked root keys are distinct in the explicit reference-30 snapshot.
A tie reconstructs a reference-fixing molecular symmetry. Isotope preservation and
fixation of both O18 atoms leave only the O16 arm pair, which the accepted covering
observation separates. No strict ordering, auxiliary labels, or slot identities are
assumed. Root readback and full reference consensus are separate consumers.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedInjectivity

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitSeparationCertificate
open LocalizedChemicalRingReferenceOrbitStabilizer LocalizedChemicalRingInheritedRefusalCases
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedChemicalRingDefaultMarkerLayout LocalizedChemicalRingFrameReadback

noncomputable section
open scoped Classical

private def slotAtom (i : Fin 4) : Fin 46 :=
  referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData i

private theorem slotAtom_injective : Function.Injective slotAtom := by
  intro i j same
  apply rootData.ligandOf.injective
  exact physical.ligandAtomAt_injective rootCenter same

private theorem slotAtom_neighbor (i : Fin 4) : graph.Adj 0 (slotAtom i) :=
  physical.ligandAtomAt_adj rootCenter (rootData.ligandOf i)

private theorem root_neighbors (a : Fin 46) :
    graph.Adj 0 a → a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31 := by
  fin_cases a <;> decide +kernel

private theorem remaining_pair (a b : Fin 46)
    (first : a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31)
    (second : b = 28 ∨ b = 29 ∨ b = 30 ∨ b = 31)
    (different : a ≠ b) (mass : graph.atomMass a = graph.atomMass b)
    (fix30 : a = 30 → b = 30) (fix31 : a = 31 → b = 31) :
    (a = 28 ∧ b = 29) ∨ (a = 29 ∧ b = 28) := by
  revert different mass fix30 fix31
  rcases first with rfl | rfl | rfl | rfl <;>
    rcases second with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem root_history : rootData.target.1.node.history = [(0 : Fin 46)] := by
  apply List.map_injective_iff.mpr Fin.val_injective
  exact (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ rootData.found).history

private theorem root_address : rootData.target.1.address = [] := by
  have address := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceAddress
  rw [address]
  simp [CertifiedLocalizedCIPInput.canonicalAddress, root_history]

private abbrev rootUnit : DetectedOccurrence graph :=
  ⟨certified.molecularFrameUnit rootData.target.1, rootData.detected⟩

private theorem slot_current (i : Fin 4) :
    ((frames certified single_bonded rootSnapshot rootData.target rootData.real rootUnit rfl).frame.cursorAt i).occurrence.1.node.current? = some (slotAtom i) := by
  have frameEq :
      (frames certified single_bonded rootSnapshot rootData.target rootData.real rootUnit rfl).frame =
        rootData.frame :=
    Option.some.inj ((frames certified single_bonded rootSnapshot rootData.target rootData.real
      rootUnit rfl).frameComputed.symm.trans rootData.frameExec)
  have mapped : (((frames certified single_bonded rootSnapshot rootData.target rootData.real
      rootUnit rfl).frame.cursorAt i).occurrence.1.node.current?).map Fin.val =
        some (slotAtom i).val := by
    change atomAt certified _ i = some (slotAtom i).val
    rw [frameEq]
    exact rootData.atomAt_eq i
  cases found : ((frames certified single_bonded rootSnapshot rootData.target rootData.real
      rootUnit rfl).frame.cursorAt i).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some a =>
      simp only [found, Option.map_some, Option.some.injEq] at mapped
      exact congrArg some (Fin.ext mapped)

/-- Injectivity is derived from actual key reconstruction, isotope restrictions and
the independent physical covering observation, not assumed as a sorting premise. -/
theorem root_markedKeys_injective : Function.Injective
    (markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
      rootSnapshot reference) := by
  intro i j tied
  by_cases same : slotAtom i = slotAtom j
  · exact slotAtom_injective same
  obtain ⟨π, aut, _, entry, referenceFixed⟩ :=
    actual_root_default_tie_reference_fixed_aut certified single_bonded rootSnapshot rootData.target
      rootData.real rootUnit rfl root_address reference i j tied (slotAtom i) (slotAtom j)
      (slot_current i) (slot_current j) ⟨0, constant_charge⟩
  let e : graph.Aut := ⟨π, aut⟩
  have fixed30 : π (30 : Fin 46) = (30 : Fin 46) := referenceFixed
  have fixed31 : π (31 : Fin 46) = (31 : Fin 46) := by
    apply fixed_of_signature graph e [30] 31
    · intro a present
      have same : a = (30 : Fin 46) := List.mem_singleton.mp present
      simpa only [same] using fixed30
    · unfold SignatureUnique
      decide +kernel
  have mass : graph.atomMass (slotAtom i) = graph.atomMass (slotAtom j) := by
    rw [← entry]
    exact (MoleculeGraph.Aut.atomMass_eq (m := graph) e (slotAtom i)).symm
  have firstFixed : slotAtom i = 30 → slotAtom j = 30 := by
    intro at30
    rw [at30, fixed30] at entry
    exact entry.symm
  have secondFixed : slotAtom i = 31 → slotAtom j = 31 := by
    intro at31
    rw [at31, fixed31] at entry
    exact entry.symm
  have pairCases := remaining_pair (slotAtom i) (slotAtom j)
    (root_neighbors _ (slotAtom_neighbor i)) (root_neighbors _ (slotAtom_neighbor j))
    same mass firstFixed secondFixed
  rcases pairCases with pair | pair
  · have left : i = leftSlot := slotAtom_injective (pair.1.trans slot_atoms.1.symm)
    have right : j = rightSlot := slotAtom_injective (pair.2.trans slot_atoms.2.symm)
    exact False.elim (root_keys_separate (by simpa only [left, right] using tied))
  · have right : i = rightSlot := slotAtom_injective (pair.1.trans slot_atoms.2.symm)
    have left : j = leftSlot := slotAtom_injective (pair.2.trans slot_atoms.1.symm)
    exact False.elim (root_keys_separate (by simpa only [left, right] using tied.symm))

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedInjectivity

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMarkedInjectivity.root_markedKeys_injective
