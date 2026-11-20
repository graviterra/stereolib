import TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport

open RetainedCoherentSymmetry
open LocalizedChemicalRingRankedReconstruction
open LocalizedPhysicalMarkedParityCompleteness

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A child component below the current witness contains only later-ranked vertices. -/
theorem child_component_higher (m : MoleculeGraph V) (B : List V) (rank : V → Nat)
    (current child : V) (outside : current ∉ B) (edge : m.Adj current child)
    (ordered : ∀ x, InComponent m B current x → x ≠ current → rank current < rank x)
    (x : V) (member : InComponent m (B ++ [current]) child x) : rank current < rank x := by
  have childOutside : child ∉ B := fun h => member.1 (List.mem_append_left _ h)
  have weakened := component_weaken
    (show B ⊆ B ++ [current] from fun _ h => List.mem_append_left _ h) member
  have start : (residualGraph m B).Adj current child := ⟨outside, childOutside, edge⟩
  apply ordered x ⟨outside, start.reachable.trans weakened.2⟩
  intro same
  exact inComponent_not_mem m member (by simp [same])



theorem support_fixes_low (m : MoleculeGraph V) (B : List V) (rank : V → Nat)
    (current left right : V) (outside : current ∉ B)
    (edgeL : m.Adj current left) (edgeR : m.Adj current right)
    (ordered : ∀ x, InComponent m B current x → x ≠ current → rank current < rank x)
    (π : Equiv.Perm V)
    (support : ∀ x, ¬ InComponent m (B ++ [current]) left x →
      ¬ InComponent m (B ++ [current]) right x → π x = x) :
    ∀ x, rank x ≤ rank current → π x = x := by
  intro x earlier
  apply support x
  · intro member
    have := child_component_higher m B rank current left outside edgeL ordered x member
    omega
  · intro member
    have := child_component_higher m B rank current right outside edgeR ordered x member
    omega

omit [Fintype V] [DecidableEq V] in
theorem witness_member_rank_le (rank : V → Nat) (path : List V) (nonempty : path ≠ [])
    (current : V) (terminal : path.getLast nonempty = current)
    (prefixLower : ∀ x ∈ path.dropLast, rank x < rank current) :
    ∀ x ∈ path, rank x ≤ rank current := by
  intro x member
  have split := List.dropLast_append_getLast nonempty
  rw [← split] at member
  rcases List.mem_append.mp member with earlier | last
  · exact Nat.le_of_lt (prefixLower x earlier)
  · have same : x = current := (List.mem_singleton.mp last).trans terminal
    rw [same]

omit [Fintype V] [DecidableEq V] in


theorem pending_witness_image (rank : V → Nat) (bound : Nat)
    (e correction : Equiv.Perm V)
    (lowFixed : ∀ x, rank x ≤ bound → correction x = x)
    (path : List V) (nonempty : path ≠ []) (current : V)
    (terminal : path.getLast nonempty = current)
    (prefixLower : ∀ x ∈ path.dropLast, rank x < rank current)
    (pending : rank current ≤ bound) :
    path.map (e * correction) = path.map e := by
  apply List.map_congr_left
  intro x member
  change e (correction x) = e x
  rw [lowFixed x ((witness_member_rank_le rank path nonempty current terminal prefixLower x member).trans pending)]

omit [Fintype V] [DecidableEq V] in
theorem higher_image (rank : V → Nat) (bound : Nat) (correction : Equiv.Perm V)
    (lowFixed : ∀ x, rank x ≤ bound → correction x = x)
    (x : V) (later : bound < rank x) : bound < rank (correction x) := by
  by_contra no
  have fixed := lowFixed (correction x) (Nat.le_of_not_gt no)
  have same : correction x = x := correction.injective fixed
  rw [same] at no
  exact no later

/-- Physical relative signs compose at the transported center, with the actual ligand
permutations. This is the orientation invariant used by right-side corrections. -/
theorem relativeSign_mul (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e correction : m.Aut) (c : m.Center) :
    relativeSign m cfg (e * correction) c =
      relativeSign m cfg e (m.centerPerm correction c) * relativeSign m cfg correction c := by
  have centers : m.centerPerm (e * correction) c =
      m.centerPerm e (m.centerPerm correction c) := by
    simpa only [MultiCenterMolecule.centerPermHom] using
      congrArg (fun p => p c) (m.centerPermHom.map_mul e correction)
  have square : m.configurationSign cfg (m.centerPerm correction c) *
      m.configurationSign cfg (m.centerPerm correction c) = 1 := permHandedness_mul_self _
  unfold relativeSign transportedSign
  rw [m.ligandPermAt_mul, centers, permHandedness_mul]
  calc
    _ = (m.configurationSign cfg (m.centerPerm correction c) *
        m.configurationSign cfg (m.centerPerm correction c)) *
        (m.configurationSign cfg c *
          (permHandedness (m.ligandPermAt e (m.centerPerm correction c)) *
            permHandedness (m.ligandPermAt correction c)) *
          m.configurationSign cfg (m.centerPerm e (m.centerPerm correction c))) := by rw [square, one_mul]
    _ = _ := by ring

/-- A correction proper above the current rank preserves the proper signs already proved
there. No rank-invariance hypothesis on the original reconstructed symmetry is required. -/
theorem proper_higher_compose (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (rank : V → Nat) (bound : Nat) (e correction : m.Aut)
    (lowFixed : ∀ x, rank x ≤ bound → (correction : Equiv.Perm V) x = x)
    (before : ∀ c : m.Center, bound < rank c.1 → relativeSign m cfg e c = 1)
    (corrected : ∀ c : m.Center, bound < rank c.1 → relativeSign m cfg correction c = 1) :
    ∀ c : m.Center, bound < rank c.1 → relativeSign m cfg (e * correction) c = 1 := by
  intro c later
  rw [relativeSign_mul, corrected c later, mul_one]
  exact before (m.centerPerm correction c) (higher_image rank bound correction lowFixed c.1 later)

/-- Two negative signs cancel at the center being corrected; its atom is fixed. -/
theorem correct_current (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e correction : m.Aut) (c : m.Center)
    (fixed : (correction : Equiv.Perm V) c.1 = c.1)
    (before : relativeSign m cfg e c = -1)
    (negative : relativeSign m cfg correction c = -1) :
    relativeSign m cfg (e * correction) c = 1 := by
  rw [relativeSign_mul, (show m.centerPerm correction c = c from Subtype.ext fixed), before, negative]
  norm_num

end
end TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport.child_component_higher
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport.support_fixes_low
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport.witness_member_rank_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport.pending_witness_image
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport.higher_image
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport.relativeSign_mul
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport.proper_higher_compose
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport.correct_current
