import TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
The final entry correction needs physical signs only on the source branch. A correction
fixing the root and its source entry preserves that domain, including when branches share
a ring component. No inherited-reference fixation is needed after the final correction.

These composition lemmas retain the physical properness of the correction away from the
entry as an explicit premise. They do not construct that correction from a refused reading.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingFinalEntryCorrection

open RootedTetrahedralBranchSymmetry LocalizedPhysicalMarkedParityCompleteness
open LocalizedChemicalRingRankedCorrectionTransport

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fixing the actual attachment atom fixes its frame slot; no branch-disjointness
hypothesis is required. -/
theorem slot_fixed (m : MultiCenterMolecule V) (g : m.Aut) (root : m.Center)
    (i : Fin 4) (rootFixed : m.centerPerm g root = root)
    (entryFixed : (g : Equiv.Perm V) (m.ligandAtomAt root i) = m.ligandAtomAt root i) :
    m.ligandPermAt g root i = i := by
  apply m.ligandAtomAt_injective root
  simpa only [rootFixed, entryFixed] using m.ligandAtomAt_ligandPermAt g root i

/-- The ranked correction invariant can be restricted to the source branch. It does not
require the initial reconstruction to be proper on the image branch or at other centers. -/
theorem proper_higher_branch_compose (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (root : m.Center) (i : Fin 4) (rank : V → Nat) (bound : Nat) (e g : m.Aut)
    (rootFixed : m.centerPerm g root = root) (slotFixed : m.ligandPermAt g root i = i)
    (lowFixed : ∀ x, rank x ≤ bound → (g : Equiv.Perm V) x = x)
    (before : ∀ d : m.Center, LigandBranchReaches m root i d.1 →
      bound < rank d.1 → relativeSign m cfg e d = 1)
    (corrected : ∀ d : m.Center, LigandBranchReaches m root i d.1 →
      bound < rank d.1 → relativeSign m cfg g d = 1) :
    ∀ d : m.Center, LigandBranchReaches m root i d.1 →
      bound < rank d.1 → relativeSign m cfg (e * g) d = 1 := by
  intro d member later
  rw [relativeSign_mul, corrected d member later, mul_one]
  exact before (m.centerPerm g d) (ligandBranchReaches_map m rootFixed slotFixed member)
    (higher_image rank bound g lowFixed d.1 later)

/-- Once all other source-branch signs are proper, an odd entry-fixing correction cancels
the remaining negative sign. The result is the independent physical `ProperTransport`.
In particular the correction may move the former inherited reference. -/
theorem properTransport_of_final_entry_correction
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (root entry : m.Center)
    (i j : Fin 4) (atEntry : entry.1 = m.ligandAtomAt root i) (e g : m.Aut)
    (rootE : m.centerPerm e root = root) (sent : m.ligandPermAt e root i = j)
    (rootG : m.centerPerm g root = root)
    (entryG : (g : Equiv.Perm V) entry.1 = entry.1)
    (before : ∀ d : m.Center, LigandBranchReaches m root i d.1 → d ≠ entry →
      relativeSign m cfg e d = 1)
    (corrected : ∀ d : m.Center, LigandBranchReaches m root i d.1 → d ≠ entry →
      relativeSign m cfg g d = 1)
    (negativeE : relativeSign m cfg e entry = -1)
    (negativeG : relativeSign m cfg g entry = -1) : ProperTransport m cfg root i j := by
  have fixedEntry : m.centerPerm g entry = entry := Subtype.ext entryG
  have fixedSlot : m.ligandPermAt g root i = i :=
    slot_fixed m g root i rootG (by simpa only [atEntry] using entryG)
  refine ⟨e * g, ?_, ?_, ?_⟩
  · rw [centerPerm_mul_apply, rootG, rootE]
  · rw [m.ligandPermAt_mul, rootG]
    change m.ligandPermAt e root (m.ligandPermAt g root i) = j
    rw [fixedSlot, sent]
  · intro d member
    have proper : relativeSign m cfg (e * g) d = 1 := by
      by_cases same : d = entry
      · subst d
        exact correct_current m cfg e g entry entryG negativeE negativeG
      · have imageMember : LigandBranchReaches m root i (m.centerPerm g d).1 :=
          ligandBranchReaches_map m rootG fixedSlot member
        have imageNe : m.centerPerm g d ≠ entry := by
          intro sameImage
          exact same ((m.centerPerm g).injective (sameImage.trans fixedEntry.symm))
        rw [relativeSign_mul, before _ imageMember imageNe, corrected d member same, one_mul]
    exact (relativeSign_eq_iff m cfg (e * g) d 1).mp proper

end
end TetraStereo.OneCenter.LocalizedChemicalRingFinalEntryCorrection

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFinalEntryCorrection.slot_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFinalEntryCorrection.proper_higher_branch_compose
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFinalEntryCorrection.properTransport_of_final_entry_correction
