import TetraStereo.OneCenter.DeclarativeCIPBoundaryComponentReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# One color-preserving molecular automorphism from residual observations

The existing component reconstruction supplies one realizing path per source atom. If the
residual path equivalence preserves an arbitrary terminal color, those witnesses make its
constructed component map preserve that color. The inverse map then preserves it on the target
component, so the same component-exchange automorphism preserves it globally.

The singleton reference color gives a reference-fixing automorphism. No endpoint consistency,
descent of every path, acyclicity, or preselected molecular automorphism is required. The premise
is still a full residual path equivalence with color readback: deriving it from actual promoted
key equality, and deriving physical frame parity from generated stereo facts, are separate steps.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction

open RetainedCoherentSymmetry BoundaryComponentReconstruction

noncomputable section
open scoped Classical

variable {V C : Type*} [Fintype V] [DecidableEq V]
  {m : MoleculeGraph V} {Bs Bt B : List V} {a b : V}

/-- An observation on the terminal atom, preserved by the full residual path equivalence. -/
def TerminalColorPreserved (e : ResidualPathTreeEquiv m Bs Bt a b) (color : V → C) : Prop :=
  ∀ p : {p : List V // ResidualObsPath m Bs a p},
    color (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty) =
      color (pathTerminal p.1 p.2.nonempty)

/-- One realizing path per atom suffices for color preservation by the reconstructed map. -/
theorem witnessed_color_eq (e : ResidualPathTreeEquiv m Bs Bt a b)
    (W : WitnessedBoundaryComponentIso e) (color : V → C)
    (preserved : TerminalColorPreserved e color) (x : V) (hx : InComponent m Bs a x) :
    color (W.iso.toFun x) = color x := by
  obtain ⟨p, terminal, image⟩ := W.witnessPath x hx
  have imageTerminal : pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty =
      W.iso.toFun (pathTerminal p.1 p.2.nonempty) := by
    simp only [pathTerminal, image, List.getLast_map]
  have same := preserved p
  rw [imageTerminal, terminal] at same
  exact same

/-- The inverse uses the same reconstructed component map, not a second chosen witness. -/
theorem witnessed_inv_color_eq (e : ResidualPathTreeEquiv m Bs Bt a b)
    (W : WitnessedBoundaryComponentIso e) (color : V → C)
    (preserved : TerminalColorPreserved e color) (x : V) (hx : InComponent m Bt b x) :
    color (W.iso.invFun x) = color x := by
  have same := witnessed_color_eq e W color preserved (W.iso.invFun x) (W.iso.maps_inv x hx)
  rw [W.iso.right_inv x hx] at same
  exact same.symm

/-- The component exchange preserves the color both for coincident and disjoint components. -/
theorem componentExchange_color_eq (e : ResidualPathTreeEquiv m B B a b)
    (W : WitnessedBoundaryComponentIso e) (color : V → C)
    (preserved : TerminalColorPreserved e color) (x : V) :
    color (componentExchange W.iso x) = color x := by
  by_cases source : InComponent m B a x
  · rw [exchange_of_a W.iso source]
    exact witnessed_color_eq e W color preserved x source
  · by_cases target : InComponent m B b x
    · rw [exchange_of_b W.iso source target]
      exact witnessed_inv_color_eq e W color preserved x target
    · rw [exchange_of_none W.iso source target]

/-- A full residual equivalence preserving terminal colors constructs one globally
color-preserving molecular automorphism. It fixes the boundary, moves the entry, is the identity
off the two components, and retains the source witness paths of the same reconstruction. -/
theorem exists_color_preserving_automorphism (e : ResidualPathTreeEquiv m B B a b)
    (ha : a ∉ B) (color : V → C) (preserved : TerminalColorPreserved e color) :
    ∃ π : Equiv.Perm V, m.IsAutomorphism π ∧ (∀ z ∈ B, π z = z) ∧ π a = b ∧
      (∀ z, color (π z) = color z) ∧
      (∀ x, ¬ InComponent m B a x → ¬ InComponent m B b x → π x = x) ∧
      ∀ x, InComponent m B a x → ∃ p : {p : List V // ResidualObsPath m B a p},
        pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map π := by
  let W := witnessedBoundaryComponentIso e ha
  have hb : b ∉ B := target_root_outside e ha
  refine ⟨componentExchangePerm W.iso ha hb,
    componentExchangePerm_isAutomorphism W.iso ha hb, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [componentExchangePerm_apply]
    exact exchange_of_none W.iso (fun h => inComponent_not_mem m h hz)
      (fun h => inComponent_not_mem m h hz)
  · rw [componentExchangePerm_apply, exchange_of_a W.iso (inComponent_self m ha)]
    exact W.iso.entry
  · intro z
    rw [componentExchangePerm_apply]
    exact componentExchange_color_eq e W color preserved z
  · intro x source target
    rw [componentExchangePerm_apply, exchange_of_none W.iso source target]
  · intro x hx
    obtain ⟨p, terminal, image⟩ := W.witnessPath x hx
    refine ⟨p, terminal, ?_⟩
    rw [image]
    apply List.map_congr_left
    intro u hu
    rw [componentExchangePerm_apply, exchange_of_a W.iso (obsPath_mem_inComponent p.2 hu)]

/-- The natural-valued membership bit used to identify one promoted reference atom. -/
def referenceColor (reference atom : V) : Nat := if atom = reference then 1 else 0

/-- Preserving the reference-membership observation constructs an automorphism fixing that
reference, whether it lies in the boundary, either residual component, or neither component. -/
theorem exists_reference_fixed_automorphism (e : ResidualPathTreeEquiv m B B a b)
    (ha : a ∉ B) (reference : V)
    (preserved : TerminalColorPreserved e (referenceColor reference)) :
    ∃ π : Equiv.Perm V, m.IsAutomorphism π ∧ (∀ z ∈ B, π z = z) ∧ π a = b ∧
      π reference = reference ∧
      (∀ x, ¬ InComponent m B a x → ¬ InComponent m B b x → π x = x) ∧
      ∀ x, InComponent m B a x → ∃ p : {p : List V // ResidualObsPath m B a p},
        pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map π := by
  obtain ⟨π, aut, boundary, entry, colors, outside, witnesses⟩ :=
    exists_color_preserving_automorphism e ha (referenceColor reference) preserved
  refine ⟨π, aut, boundary, entry, ?_, outside, witnesses⟩
  by_contra different
  have same := colors reference
  simp [referenceColor, different] at same

end

end TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction.TerminalColorPreserved
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction.witnessed_color_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction.witnessed_inv_color_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction.componentExchange_color_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction.exists_color_preserving_automorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction.referenceColor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction.exists_reference_fixed_automorphism
