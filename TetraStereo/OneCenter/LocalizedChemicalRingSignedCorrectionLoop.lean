import TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport
import TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A descending finite correction argument for either physical sense. It separates the
termination/composition argument from the actual-label decoder: the caller must construct
an odd local correction at each highest center of the wrong sense. The negative-sense case
will consume mirror-normalized actual executions; this algebra alone is not that bridge. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSignedCorrectionLoop

open RetainedCoherentSymmetry
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedChemicalRingRankedCorrectionTransport (relativeSign_mul higher_image)
open LocalizedChemicalRingComponentExchangeProperness (inComponent_map)

noncomputable section
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  (m : MultiCenterMolecule V) (cfg : m.Configuration)
  (B references : List V) (entry : V) (rank : V → Nat)

/-- A local odd correction preserves the boundary, all references, the entry and every
earlier atom. Its physical signs at later source centers are proper. -/
def LocalRepair (d : m.Center) (g : m.Aut) : Prop :=
  (∀ atom ∈ B, (g : Equiv.Perm V) atom = atom) ∧
  (∀ atom, rank atom ≤ rank d.1 → (g : Equiv.Perm V) atom = atom) ∧
  (∀ atom ∈ references, (g : Equiv.Perm V) atom = atom) ∧
  (g : Equiv.Perm V) entry = entry ∧
  relativeSign m cfg g d = -1 ∧
  ∀ other : m.Center, InComponent m.mol B entry other.1 → rank d.1 < rank other.1 →
    relativeSign m cfg g other = 1

variable (injective : Function.Injective rank) (seed : m.Aut) (sense : ℝ)
  (unitSense : sense = 1 ∨ sense = -1)

/-- The remaining chemistry-specific producer. It is needed only at a highest wrong-sense
center, with all lower atoms still fixed. No termination hypothesis occurs in this contract. -/
def Repairable : Prop :=
  ∀ (correction : m.Aut) (d : m.Center),
    (∀ atom ∈ B, (correction : Equiv.Perm V) atom = atom) →
    (∀ atom, rank atom ≤ rank d.1 → (correction : Equiv.Perm V) atom = atom) →
    (∀ atom ∈ references, (correction : Equiv.Perm V) atom = atom) →
    (correction : Equiv.Perm V) entry = entry →
    InComponent m.mol B entry d.1 →
    relativeSign m cfg (seed * correction) d ≠ sense →
    (∀ other : m.Center, InComponent m.mol B entry other.1 → rank d.1 < rank other.1 →
      relativeSign m cfg (seed * correction) other = sense) →
    ∃ g, LocalRepair m cfg B references entry rank d g

include injective unitSense in
private theorem loop (repairable : Repairable m cfg B references entry rank seed sense) :
    ∀ (bound : Nat) (correction : m.Aut),
      (∀ atom ∈ B, (correction : Equiv.Perm V) atom = atom) →
      (∀ atom, rank atom < bound → (correction : Equiv.Perm V) atom = atom) →
      (∀ atom ∈ references, (correction : Equiv.Perm V) atom = atom) →
      (correction : Equiv.Perm V) entry = entry →
      (∀ d : m.Center, InComponent m.mol B entry d.1 → bound ≤ rank d.1 →
        relativeSign m cfg (seed * correction) d = sense) →
      ∃ final : m.Aut,
        (∀ atom ∈ B, (final : Equiv.Perm V) atom = atom) ∧
        (∀ atom ∈ references, (final : Equiv.Perm V) atom = atom) ∧
        (final : Equiv.Perm V) entry = entry ∧
        ∀ d : m.Center, InComponent m.mol B entry d.1 →
          relativeSign m cfg (seed * final) d = sense := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
    intro correction boundary low fixedReferences fixedEntry high
    by_cases done : ∀ d : m.Center, InComponent m.mol B entry d.1 →
        relativeSign m cfg (seed * correction) d = sense
    · exact ⟨correction, boundary, fixedReferences, fixedEntry, done⟩
    let bad := Finset.univ.filter fun d : m.Center =>
      InComponent m.mol B entry d.1 ∧ relativeSign m cfg (seed * correction) d ≠ sense
    have nonempty : bad.Nonempty := by
      push_neg at done
      obtain ⟨d, member, wrong⟩ := done
      exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, member, wrong⟩⟩
    obtain ⟨d, badD, maximal⟩ := bad.exists_max_image (fun d => rank d.1) nonempty
    obtain ⟨member, wrong⟩ := (Finset.mem_filter.mp badD).2
    have pending : rank d.1 < bound := by
      by_contra later
      exact wrong (high d member (Nat.le_of_not_gt later))
    have maximalSense : ∀ other : m.Center, InComponent m.mol B entry other.1 →
        rank d.1 < rank other.1 → relativeSign m cfg (seed * correction) other = sense := by
      intro other present later
      by_contra wrongOther
      have upper := maximal other
        (Finset.mem_filter.mpr ⟨Finset.mem_univ other, present, wrongOther⟩)
      omega
    obtain ⟨g, gBoundary, gLow, gReferences, gEntry, gNegative, gHigh⟩ :=
      repairable correction d boundary (fun atom earlier => low atom (earlier.trans_lt pending))
        fixedReferences fixedEntry member wrong maximalSense
    have before : relativeSign m cfg (seed * correction) d = -sense := by
      rcases unitSense with unitSense | unitSense
      · have sign := (relativeSign_eq_one_or_neg_one m cfg (seed * correction) d).resolve_left
          (by simpa only [unitSense] using wrong)
        simpa only [unitSense] using sign
      · have sign := (relativeSign_eq_one_or_neg_one m cfg (seed * correction) d).resolve_right
          (by simpa only [unitSense] using wrong)
        simpa only [unitSense, neg_neg] using sign
    apply ih (rank d.1) pending (correction * g)
    · intro atom present
      change (correction : Equiv.Perm V) ((g : Equiv.Perm V) atom) = atom
      rw [gBoundary atom present, boundary atom present]
    · intro atom earlier
      change (correction : Equiv.Perm V) ((g : Equiv.Perm V) atom) = atom
      rw [gLow atom earlier.le, low atom (earlier.trans pending)]
    · intro atom present
      change (correction : Equiv.Perm V) ((g : Equiv.Perm V) atom) = atom
      rw [gReferences atom present, fixedReferences atom present]
    · change (correction : Equiv.Perm V) ((g : Equiv.Perm V) entry) = entry
      rw [gEntry, fixedEntry]
    · intro other present later
      rw [← mul_assoc]
      by_cases same : other = d
      · subst other
        rw [relativeSign_mul,
          (show m.centerPerm g d = d from Subtype.ext (gLow d.1 le_rfl)), before, gNegative]
        ring
      · have strict : rank d.1 < rank other.1 := by
          apply Nat.lt_of_le_of_ne later
          intro equal
          exact same (Subtype.ext (injective equal).symm)
        let graphAut : m.mol.Aut := ⟨g, MultiCenterMolecule.Aut.mem_molAut m g⟩
        have moved := inComponent_map m.mol B graphAut gBoundary present
        have entryFixed : (graphAut : Equiv.Perm V) entry = entry := gEntry
        rw [entryFixed] at moved
        rw [relativeSign_mul, gHigh other present strict, mul_one]
        exact maximalSense (m.centerPerm g other) moved
          (higher_image rank (rank d.1) g gLow other.1 strict)

include injective unitSense in
/-- Finite local repairs construct one map of the requested proper or mirror sense.
All boundary/reference identities and the specified entry image survive the construction. -/
theorem exists_signed_source_map
    (repairable : Repairable m cfg B references entry rank seed sense)
    (seedBoundary : ∀ atom ∈ B, (seed : Equiv.Perm V) atom = atom)
    (seedReferences : ∀ atom ∈ references, (seed : Equiv.Perm V) atom = atom)
    (image : V) (seedEntry : (seed : Equiv.Perm V) entry = image) :
    ∃ final : m.Aut,
      (∀ atom ∈ B, (final : Equiv.Perm V) atom = atom) ∧
      (∀ atom ∈ references, (final : Equiv.Perm V) atom = atom) ∧
      (final : Equiv.Perm V) entry = image ∧
      ∀ d : m.Center, InComponent m.mol B entry d.1 → relativeSign m cfg final d = sense := by
  obtain ⟨correction, boundary, fixedReferences, fixedEntry, signs⟩ :=
    loop m cfg B references entry rank injective seed sense unitSense repairable
      (Finset.univ.sup rank + 1) 1 (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
      (fun d _ later => absurd (Finset.le_sup (f := rank) (Finset.mem_univ d.1)) (by omega))
  refine ⟨seed * correction, ?_, ?_, ?_, signs⟩
  · intro atom present
    change (seed : Equiv.Perm V) ((correction : Equiv.Perm V) atom) = atom
    rw [boundary atom present, seedBoundary atom present]
  · intro atom present
    change (seed : Equiv.Perm V) ((correction : Equiv.Perm V) atom) = atom
    rw [fixedReferences atom present, seedReferences atom present]
  · change (seed : Equiv.Perm V) ((correction : Equiv.Perm V) entry) = image
    rw [fixedEntry, seedEntry]

end
end TetraStereo.OneCenter.LocalizedChemicalRingSignedCorrectionLoop

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSignedCorrectionLoop.exists_signed_source_map
