import TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness
import TetraStereo.OneCenter.LocalizedChemicalRingFinalEntryCorrection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
An odd local correction fixing the original degree-four root and its selected attachment
has only one unresolved reference orbit: a swap of two other root neighbors. In the other
cases its cube fixes the inherited root-neighbor reference, retains the negative local
sign, and preserves the correction's support and already-proved physical properness.

This uses degree four only at the actual root. No bound on other molecular degrees is
introduced. The two-port alternative is retained: odd powers of that same automorphism
still move the reference, and even powers lose its negative sign at the fixed current
center. Construction of a suitable odd correction remains a separate chemical obligation.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection

open RetainedCoherentSymmetry LocalizedPhysicalMarkedParityCompleteness
open LocalizedChemicalRingRankedCorrectionTransport
open LocalizedChemicalRingComponentExchangeProperness
open LocalizedChemicalRingFinalEntryCorrection

/-- With one of four slots fixed, a reference is fixed by the cube or lies in a two-cycle. -/
theorem fixed_slot_reference_dichotomy (p : Equiv.Perm (Fin 4)) (entry reference : Fin 4)
    (fixed : p entry = entry) :
    p (p (p reference)) = reference ∨
      (p reference ≠ reference ∧ p (p reference) = reference) := by
  have finite : ∀ (p : Equiv.Perm (Fin 4)) (entry reference : Fin 4), p entry = entry →
      p (p (p reference)) = reference ∨
        (p reference ≠ reference ∧ p (p reference) = reference) := by decide +kernel
  exact finite p entry reference fixed

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def cube (m : MultiCenterMolecule V) (g : m.Aut) : m.Aut := (g * g) * g

theorem cube_apply (m : MultiCenterMolecule V) (g : m.Aut) (x : V) :
    (cube m g : Equiv.Perm V) x =
      (g : Equiv.Perm V) ((g : Equiv.Perm V) ((g : Equiv.Perm V) x)) := rfl

theorem cube_fixed (m : MultiCenterMolecule V) (g : m.Aut) (x : V)
    (fixed : (g : Equiv.Perm V) x = x) : (cube m g : Equiv.Perm V) x = x := by
  rw [cube_apply, fixed, fixed, fixed]

/-- The finite slot result applies to the actual root's physical neighbor inventory. -/
theorem root_reference_dichotomy (m : MultiCenterMolecule V) (g : m.Aut)
    (root : m.Center) (entry : Fin 4)
    (rootFixed : m.centerPerm g root = root)
    (entryFixed : (g : Equiv.Perm V) (m.ligandAtomAt root entry) = m.ligandAtomAt root entry)
    (reference : V) (adjacent : m.mol.Adj root.1 reference) :
    (cube m g : Equiv.Perm V) reference = reference ∨
      ((g : Equiv.Perm V) reference ≠ reference ∧
        (g : Equiv.Perm V) ((g : Equiv.Perm V) reference) = reference) := by
  obtain ⟨j, atReference⟩ := m.ligandAtomAt_surjective root reference adjacent
  have entrySlot := slot_fixed m g root entry rootFixed entryFixed
  have image (i : Fin 4) :
      (g : Equiv.Perm V) (m.ligandAtomAt root i) =
        m.ligandAtomAt root (m.ligandPermAt g root i) := by
    have h := m.ligandAtomAt_ligandPermAt g root i
    rw [rootFixed] at h
    exact h.symm
  rcases fixed_slot_reference_dichotomy (m.ligandPermAt g root) entry j entrySlot with
    fixed | ⟨changed, twice⟩
  · left
    rw [cube_apply, ← atReference, image, image, image, fixed]
  · right
    constructor
    · intro same
      apply changed
      apply m.ligandAtomAt_injective root
      rw [← image, atReference, same]
    · rw [← atReference, image, image, twice]

/-- At a fixed center the relative sign is multiplicative under every power. -/
theorem relativeSign_pow_fixed (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (current : m.Center) (fixed : m.centerPerm g current = current) (n : Nat) :
    relativeSign m cfg (g ^ n) current = (relativeSign m cfg g current) ^ n := by
  induction n with
  | zero => simp only [pow_zero, relativeSign_one]
  | succ n ih => simp only [pow_succ, relativeSign_mul, fixed, ih]

theorem cube_negative (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (current : m.Center) (fixed : m.centerPerm g current = current)
    (negative : relativeSign m cfg g current = -1) :
    relativeSign m cfg (cube m g) current = -1 := by
  simp only [cube, relativeSign_mul, fixed, negative]
  norm_num

private theorem cube_proper_on (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (P : m.Center → Prop)
    (stable : ∀ c, P c → P (m.centerPerm g c))
    (proper : ∀ c, P c → relativeSign m cfg g c = 1) :
    ∀ c, P c → relativeSign m cfg (cube m g) c = 1 := by
  intro c member
  have first := stable c member
  have second := stable (m.centerPerm g c) first
  rw [cube, relativeSign_mul, relativeSign_mul,
    proper c member, proper _ first, proper _ second]
  norm_num

/-- The residual physical domain is invariant because the whole boundary and current
center are fixed. Thus no new properness premise is needed for the cube's image centers. -/
theorem cube_proper_residual (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (B : List V) (current : m.Center)
    (boundary : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (fixed : m.centerPerm g current = current)
    (proper : ∀ c : m.Center, InComponent m.mol B current.1 c.1 → c ≠ current →
      relativeSign m cfg g c = 1) :
    ∀ c : m.Center, InComponent m.mol B current.1 c.1 → c ≠ current →
      relativeSign m cfg (cube m g) c = 1 := by
  let graphAut : m.mol.Aut := ⟨g, MultiCenterMolecule.Aut.mem_molAut m g⟩
  have fixedAtom : (g : Equiv.Perm V) current.1 = current.1 := congrArg Subtype.val fixed
  have stable : ∀ c : m.Center,
      InComponent m.mol B current.1 c.1 ∧ c ≠ current →
      InComponent m.mol B current.1 (m.centerPerm g c).1 ∧ m.centerPerm g c ≠ current := by
    intro c member
    constructor
    · have h := inComponent_map m.mol B graphAut boundary member.1
      change InComponent m.mol B ((g : Equiv.Perm V) current.1)
        ((g : Equiv.Perm V) c.1) at h
      simpa only [fixedAtom] using h
    · intro same
      exact member.2 ((m.centerPerm g).injective (same.trans fixed.symm))
  intro c member different
  exact cube_proper_on m cfg g _ stable (fun d h => proper d h.1 h.2) c ⟨member, different⟩

/-- Low-rank fixation keeps higher centers in the same rank domain; their already-proved
proper signs are therefore preserved by cubing the correction. -/
theorem cube_proper_higher (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (rank : V → Nat) (bound : Nat)
    (lowFixed : ∀ x, rank x ≤ bound → (g : Equiv.Perm V) x = x)
    (proper : ∀ c : m.Center, bound < rank c.1 → relativeSign m cfg g c = 1) :
    ∀ c : m.Center, bound < rank c.1 → relativeSign m cfg (cube m g) c = 1 := by
  apply cube_proper_on m cfg g (fun c => bound < rank c.1)
  · intro c later
    exact higher_image rank bound g lowFixed c.1 later
  · exact proper

private theorem pow_apply_succ (m : MultiCenterMolecule V) (g : m.Aut) (n : Nat) (x : V) :
    ((g ^ (n + 1) : m.Aut) : Equiv.Perm V) x =
      (g : Equiv.Perm V) (((g ^ n : m.Aut) : Equiv.Perm V) x) := by
  rw [pow_succ']
  rfl

/-- A two-port swap is a genuine exception: every odd power of THIS correction still
moves the inherited reference. This makes no claim about other automorphisms. -/
theorem two_port_odd_power_moves (m : MultiCenterMolecule V) (g : m.Aut) (reference : V)
    (changed : (g : Equiv.Perm V) reference ≠ reference)
    (twice : (g : Equiv.Perm V) ((g : Equiv.Perm V) reference) = reference) (n : Nat) :
    ((g ^ (2 * n + 1) : m.Aut) : Equiv.Perm V) reference ≠ reference := by
  have value : ∀ k : Nat, ((g ^ (2 * k + 1) : m.Aut) : Equiv.Perm V) reference =
      (g : Equiv.Perm V) reference := by
    intro k
    induction k with
    | zero => simp only [Nat.mul_zero, Nat.zero_add, pow_one]
    | succ k ih =>
        rw [show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 by omega,
          pow_apply_succ, pow_apply_succ, ih, twice]
  rw [value]
  exact changed

/-- Even powers cannot retain the negative current sign required to correct a bad
orientation. Together with the preceding theorem this rules out a power-only repair of
the exceptional two-port case. -/
theorem even_power_positive (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (current : m.Center) (fixed : m.centerPerm g current = current)
    (negative : relativeSign m cfg g current = -1) (n : Nat) :
    relativeSign m cfg (g ^ (2 * n)) current = 1 := by
  rw [relativeSign_pow_fixed m cfg g current fixed, negative, pow_mul]
  norm_num

/-- Physical correction endpoint. Either the explicit cube fixes the inherited
reference and retains every needed local/support invariant, or that reference is
actually swapped with another root neighbor by the original correction. The latter
alternative is not discarded or labeled chemically impossible. -/
theorem odd_cube_correction_or_two_port (m : MultiCenterMolecule V)
    (cfg : m.Configuration) (g : m.Aut) (root current : m.Center) (entry : Fin 4)
    (rootFixed : m.centerPerm g root = root)
    (entryFixed : (g : Equiv.Perm V) (m.ligandAtomAt root entry) = m.ligandAtomAt root entry)
    (currentFixed : m.centerPerm g current = current)
    (reference : V) (referenceAdjacent : m.mol.Adj root.1 reference)
    (B : List V) (left right : V) (rank : V → Nat) (bound : Nat)
    (boundary : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (support : ∀ x, ¬ InComponent m.mol (B ++ [current.1]) left x →
      ¬ InComponent m.mol (B ++ [current.1]) right x → (g : Equiv.Perm V) x = x)
    (lowFixed : ∀ x, rank x ≤ bound → (g : Equiv.Perm V) x = x)
    (negative : relativeSign m cfg g current = -1)
    (proper : ∀ c : m.Center, InComponent m.mol B current.1 c.1 → c ≠ current →
      relativeSign m cfg g c = 1) :
    ((cube m g : Equiv.Perm V) reference = reference ∧
      m.centerPerm (cube m g) root = root ∧
      m.centerPerm (cube m g) current = current ∧
      (cube m g : Equiv.Perm V) (m.ligandAtomAt root entry) = m.ligandAtomAt root entry ∧
      (∀ x ∈ B, (cube m g : Equiv.Perm V) x = x) ∧
      (∀ x, ¬ InComponent m.mol (B ++ [current.1]) left x →
        ¬ InComponent m.mol (B ++ [current.1]) right x → (cube m g : Equiv.Perm V) x = x) ∧
      (∀ x, rank x ≤ bound → (cube m g : Equiv.Perm V) x = x) ∧
      relativeSign m cfg (cube m g) current = -1 ∧
      (∀ c : m.Center, InComponent m.mol B current.1 c.1 → c ≠ current →
        relativeSign m cfg (cube m g) c = 1)) ∨
      ((g : Equiv.Perm V) reference ≠ reference ∧
        (g : Equiv.Perm V) ((g : Equiv.Perm V) reference) = reference) := by
  rcases root_reference_dichotomy m g root entry rootFixed entryFixed reference referenceAdjacent
    with fixed | swapped
  · left
    refine ⟨fixed, Subtype.ext (cube_fixed m g root.1 (congrArg Subtype.val rootFixed)),
      Subtype.ext (cube_fixed m g current.1 (congrArg Subtype.val currentFixed)),
      cube_fixed m g _ entryFixed, ?_, ?_, ?_, cube_negative m cfg g current currentFixed negative,
      cube_proper_residual m cfg g B current boundary currentFixed proper⟩
    · exact fun x member => cube_fixed m g x (boundary x member)
    · exact fun x outsideL outsideR => cube_fixed m g x (support x outsideL outsideR)
    · exact fun x earlier => cube_fixed m g x (lowFixed x earlier)
  · exact Or.inr swapped

end
end TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.fixed_slot_reference_dichotomy
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.cube
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.cube_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.cube_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.root_reference_dichotomy
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.relativeSign_pow_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.cube_negative
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.cube_proper_residual
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.cube_proper_higher
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.two_port_odd_power_moves
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.even_power_positive
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddPowerReferenceCorrection.odd_cube_correction_or_two_port
