import TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
A supported correction with negative physical sign at an earlier FIXED boundary center
must move one of that center's actual neighbors inside its support. The resulting edge
enters a residual component and supplies a simple shortcut to the current center through
an outward attachment. Every interior vertex avoids the entire old deleted boundary.

This is structural evidence for an alternate occurrence path. It does not supply a
successful label, preserve an old global path correspondence, retain every later prefix
vertex, or assert that the shortcut visits the inherited reference.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingBoundaryOrientationShortcut

open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction
open LocalizedChemicalRingComponentOrientationSupport
open LocalizedPhysicalMarkedParityCompleteness

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An improper map fixing a center must move an actual neighbor of that center. -/
theorem moved_neighbor_of_not_proper (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (d : m.Center) (fixed : (g : Equiv.Perm V) d.1 = d.1)
    (improper : relativeSign m cfg g d ≠ 1) :
    ∃ x, m.mol.Adj d.1 x ∧ (g : Equiv.Perm V) x ≠ x := by
  by_contra missing
  apply improper
  apply relativeSign_of_frame_fixed m cfg g d fixed
  intro x adjacent
  by_contra moved
  exact missing ⟨x, adjacent, moved⟩

/-- Support, rather than boundary fixation alone, locates the moved neighbor in an
affected residual component. -/
theorem boundary_moved_neighbor (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (B : List V) (a b : V)
    (boundary : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (support : ∀ x, ¬ InComponent m.mol B a x → ¬ InComponent m.mol B b x →
      (g : Equiv.Perm V) x = x)
    (d : m.Center) (member : d.1 ∈ B) (negative : relativeSign m cfg g d = -1) :
    ∃ x, m.mol.Adj d.1 x ∧ (g : Equiv.Perm V) x ≠ x ∧
      (InComponent m.mol B a x ∨ InComponent m.mol B b x) := by
  have improper : relativeSign m cfg g d ≠ 1 := by rw [negative]; norm_num
  obtain ⟨x, adjacent, moved⟩ := moved_neighbor_of_not_proper m cfg g d
    (boundary d.1 member) improper
  refine ⟨x, adjacent, moved, ?_⟩
  by_cases left : InComponent m.mol B a x
  · exact Or.inl left
  · right
    by_contra right
    exact moved (support x left right)

private theorem residual_walk_chain {m : MoleculeGraph V} {B : List V} {x y : V}
    (walk : (residualGraph m B).Walk x y) : BondedChain m walk.support := by
  induction walk with
  | nil => trivial
  | cons edge tail ih =>
      change BondedChain m (_ :: tail.support)
      rw [tail.support_eq_cons] at ih ⊢
      exact ⟨edge.2.2, ih⟩

/-- Residual reachability supplies a simple path in the reverse direction, retaining
the boundary avoidance needed by the actual source-path construction. -/
theorem residual_path_to_attachment (m : MoleculeGraph V) (B : List V) (a x : V)
    (member : InComponent m B a x) :
    ∃ p : {p : List V // ResidualObsPath m B x p}, pathTerminal p.1 p.2.nonempty = a := by
  apply member.2.symm.elim_path
  intro path
  have outside : x ∉ B := inComponent_not_mem m member
  have valid : ResidualObsPath m B x path.1.support :=
    { nonempty := path.1.support_ne_nil
      head := by
        rw [List.head?_eq_some_head path.1.support_ne_nil, path.1.head_support]
      nodup := path.nodup_support
      outside := walk_support_outside path.1 outside
      chain := residual_walk_chain path.1 }
  exact ⟨⟨path.1.support, valid⟩, path.1.getLast_support⟩

private theorem chain_snoc (m : MoleculeGraph V) :
    ∀ (p : List V) (nonempty : p ≠ []) (z : V), BondedChain m p →
      m.Adj (pathTerminal p nonempty) z → BondedChain m (p ++ [z])
  | [], nonempty, _, _, _ => False.elim (nonempty rfl)
  | [x], _, _, _, edge => ⟨edge, trivial⟩
  | x :: y :: rest, _, z, chain, edge => by
      refine ⟨chain.1, chain_snoc m (y :: rest) (by simp) z chain.2 ?_⟩
      simpa only [pathTerminal_cons_ne x (y :: rest) (by simp)] using edge

/-- Joining the two boundary edges to the residual interior gives a simple bonded
path. Only its endpoints belong to the old boundary. -/
theorem shortcut_of_component (m : MoleculeGraph V) (B : List V) (d c a x : V)
    (oldD : d ∈ B) (oldC : c ∈ B) (distinct : d ≠ c)
    (first : m.Adj d x) (last : m.Adj a c) (member : InComponent m B a x) :
    ∃ p : {p : List V // ResidualObsPath m B x p},
      pathTerminal p.1 p.2.nonempty = a ∧
      (d :: (p.1 ++ [c])).Nodup ∧ BondedChain m (d :: (p.1 ++ [c])) := by
  obtain ⟨p, terminal⟩ := residual_path_to_attachment m B a x member
  have avoidD : d ∉ p.1 := fun present => p.2.outside d present oldD
  have avoidC : c ∉ p.1 := fun present => p.2.outside c present oldC
  have middleNodup : (p.1 ++ [c]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨p.2.nodup, by simp, ?_⟩
    intro u present v singleton equal
    have atC : v = c := by simpa using singleton
    exact avoidC ((equal.trans atC) ▸ present)
  have allNodup : (d :: (p.1 ++ [c])).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, middleNodup⟩
    simpa only [List.mem_append, List.mem_singleton, not_or] using And.intro avoidD distinct
  have tailChain : BondedChain m (p.1 ++ [c]) :=
    chain_snoc m p.1 p.2.nonempty c p.2.chain (by simpa only [terminal] using last)
  refine ⟨p, terminal, allNodup, ?_⟩
  obtain ⟨vertices, valid⟩ := p
  cases vertices with
  | nil => exact False.elim (valid.nonempty rfl)
  | cons y rest =>
      have atX : y = x := Option.some.inj valid.head
      subst y
      exact ⟨first, tailChain⟩

/-- A negative earlier boundary center has a simple alternate route into the current
center through one of the supported outward attachments. The moved first neighbor and
the exact residual interior are retained for subsequent occurrence realization. -/
theorem boundary_negative_shortcut (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (g : m.Aut) (B : List V) (a b c : V)
    (boundary : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (support : ∀ x, ¬ InComponent m.mol B a x → ¬ InComponent m.mol B b x →
      (g : Equiv.Perm V) x = x)
    (current : c ∈ B) (leftEdge : m.mol.Adj a c) (rightEdge : m.mol.Adj b c)
    (d : m.Center) (earlier : d.1 ∈ B) (distinct : d.1 ≠ c)
    (negative : relativeSign m cfg g d = -1) :
    ∃ x y, m.mol.Adj d.1 x ∧ (g : Equiv.Perm V) x ≠ x ∧ (y = a ∨ y = b) ∧
      ∃ p : {p : List V // ResidualObsPath m.mol B x p},
        pathTerminal p.1 p.2.nonempty = y ∧ m.mol.Adj y c ∧
        (d.1 :: (p.1 ++ [c])).Nodup ∧ BondedChain m.mol (d.1 :: (p.1 ++ [c])) := by
  obtain ⟨x, first, moved, component⟩ :=
    boundary_moved_neighbor m cfg g B a b boundary support d earlier negative
  rcases component with left | right
  · obtain ⟨p, terminal, nodup, chain⟩ :=
      shortcut_of_component m.mol B d.1 c a x earlier current distinct first leftEdge left
    exact ⟨x, a, first, moved, Or.inl rfl, p, terminal, leftEdge, nodup, chain⟩
  · obtain ⟨p, terminal, nodup, chain⟩ :=
      shortcut_of_component m.mol B d.1 c b x earlier current distinct first rightEdge right
    exact ⟨x, b, first, moved, Or.inr rfl, p, terminal, rightEdge, nodup, chain⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingBoundaryOrientationShortcut

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryOrientationShortcut.moved_neighbor_of_not_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryOrientationShortcut.boundary_moved_neighbor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryOrientationShortcut.residual_path_to_attachment
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryOrientationShortcut.shortcut_of_component
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingBoundaryOrientationShortcut.boundary_negative_shortcut
