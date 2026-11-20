import TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedReconstruction
import TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
An exchanged residual component cannot change a non-boundary center outside its support:
all four physical neighbors are fixed as well. For a ranked witness, every already-later
center lies outside the newly deleted path prefix. Therefore properness only needs to be
proved inside the exchanged components; it extends to all later centers outside the original
boundary. Boundary atom fixation alone is never used to claim frame fixation.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport

open RetainedCoherentSymmetry BoundaryComponentReconstruction
open LocalizedChemicalRingPrefixRankedReconstruction
open LocalizedPhysicalMarkedParityCompleteness

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fixing a center and its actual neighbors fixes its chosen local frame. -/
theorem frame_fixed (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center)
    (fixed : (e : Equiv.Perm V) c.1 = c.1)
    (neighbors : ∀ x, m.mol.Adj c.1 x → (e : Equiv.Perm V) x = x) :
    m.centerPerm e c = c ∧ m.ligandPermAt e c = 1 := by
  have center : m.centerPerm e c = c := Subtype.ext fixed
  refine ⟨center, ?_⟩
  apply Equiv.ext
  intro i
  apply m.ligandAtomAt_injective c
  have moved := m.ligandAtomAt_ligandPermAt e c i
  rw [center, neighbors _ (m.ligandAtomAt_adj c i)] at moved
  exact moved

theorem relativeSign_of_frame_fixed (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (c : m.Center)
    (fixed : (e : Equiv.Perm V) c.1 = c.1)
    (neighbors : ∀ x, m.mol.Adj c.1 x → (e : Equiv.Perm V) x = x) :
    relativeSign m cfg e c = 1 := by
  obtain ⟨center, frame⟩ := frame_fixed m e c fixed neighbors
  simpa only [relativeSign, transportedSign, center, frame, permHandedness_one, mul_one]
    using permHandedness_mul_self (cfg c)

/-- The graph itself excludes a neighbor in an exchanged component when its center is
outside both components and outside the deleted boundary. -/
theorem outside_neighbors_fixed (m : MoleculeGraph V) (B : List V) (a b : V)
    (π : Equiv.Perm V)
    (boundary : ∀ x ∈ B, π x = x)
    (support : ∀ x, ¬ InComponent m B a x → ¬ InComponent m B b x → π x = x)
    (center : V) (outside : center ∉ B)
    (notLeft : ¬ InComponent m B a center) (notRight : ¬ InComponent m B b center) :
    ∀ x, m.Adj center x → π x = x := by
  intro x adjacent
  by_cases deleted : x ∈ B
  · exact boundary x deleted
  · apply support x
    · intro member
      apply notLeft
      exact ⟨member.1, member.2.trans
        (show (residualGraph m B).Adj x center from
          ⟨deleted, outside, m.adj_symm.mp adjacent⟩).reachable⟩
    · intro member
      apply notRight
      exact ⟨member.1, member.2.trans
        (show (residualGraph m B).Adj x center from
          ⟨deleted, outside, m.adj_symm.mp adjacent⟩).reachable⟩

/-- Physical properness outside the two exchanged components is derived, not assumed. -/
theorem relativeSign_outside (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (B : List V) (a b : V)
    (boundary : ∀ x ∈ B, (e : Equiv.Perm V) x = x)
    (support : ∀ x, ¬ InComponent m.mol B a x → ¬ InComponent m.mol B b x →
      (e : Equiv.Perm V) x = x)
    (c : m.Center) (outside : c.1 ∉ B)
    (notLeft : ¬ InComponent m.mol B a c.1) (notRight : ¬ InComponent m.mol B b c.1) :
    relativeSign m cfg e c = 1 :=
  relativeSign_of_frame_fixed m cfg e c (support c.1 notLeft notRight)
    (outside_neighbors_fixed m.mol B a b e boundary support c.1 outside notLeft notRight)

/-- The actual component-exchange construction has exactly the support used above. -/
theorem exchange_support {m : MoleculeGraph V} {B : List V} {a b : V}
    (iso : BoundaryComponentIso m B B a b) (ha : a ∉ B) (hb : b ∉ B) :
    (∀ x ∈ B, componentExchangePerm iso ha hb x = x) ∧
      (∀ x, ¬ InComponent m B a x → ¬ InComponent m B b x →
        componentExchangePerm iso ha hb x = x) := by
  constructor
  · intro x member
    exact exchange_of_none iso (fun h => inComponent_not_mem m h member)
      (fun h => inComponent_not_mem m h member)
  · intro x left right
    exact exchange_of_none iso left right

/-- Local properness inside the two affected components suffices for ALL later centers.
Earlier prefix centers may change now and are deliberately left for later correction. -/
theorem relativeSign_later_of_components (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (B path : List V) (rank : V → Nat) (current a b : V)
    (prefixLower : ∀ x ∈ path.dropLast, rank x < rank current)
    (boundary : ∀ x ∈ B ++ path.dropLast, (e : Equiv.Perm V) x = x)
    (support : ∀ x, ¬ InComponent m.mol (B ++ path.dropLast) a x →
      ¬ InComponent m.mol (B ++ path.dropLast) b x → (e : Equiv.Perm V) x = x)
    (inside : ∀ c : m.Center, rank current < rank c.1 →
      (InComponent m.mol (B ++ path.dropLast) a c.1 ∨
        InComponent m.mol (B ++ path.dropLast) b c.1) → relativeSign m cfg e c = 1) :
    ∀ c : m.Center, c.1 ∉ B → rank current < rank c.1 → relativeSign m cfg e c = 1 := by
  intro c outside later
  by_cases left : InComponent m.mol (B ++ path.dropLast) a c.1
  · exact inside c later (Or.inl left)
  · by_cases right : InComponent m.mol (B ++ path.dropLast) b c.1
    · exact inside c later (Or.inr right)
    · exact relativeSign_outside m cfg e (B ++ path.dropLast) a b boundary support c
        (outside_extended_boundary_of_rank prefixLower outside (Nat.le_of_lt later)) left right

end
end TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport.frame_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport.relativeSign_of_frame_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport.outside_neighbors_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport.relativeSign_outside
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport.exchange_support
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport.relativeSign_later_of_components
