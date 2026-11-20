import TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport
import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Properness on one residual component suffices for the inverse exchange of two components.
For distinct components the exchange is involutive, so the physical sign cocycle derives
the target signs. When the components coincide there is no additional target population.

A corrected automorphism can first be restricted to its source component and then extended
by the inverse on the target. The new automorphism agrees with the original on every source
center and all its neighbors. No target sign, graph simplicity, or orientation at the deleted
boundary is assumed. This module does not construct the initial source-proper correction.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness

open RetainedCoherentSymmetry BoundaryComponentReconstruction
open LocalizedPhysicalMarkedParityCompleteness
open LocalizedChemicalRingRankedCorrectionTransport
open LocalizedChemicalRingComponentOrientationSupport
open RootedTetrahedralBranchSymmetry

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A local physical sign depends only on the center and its four actual neighbors. -/
theorem relativeSign_congr (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e f : m.Aut) (c : m.Center)
    (atCenter : (e : Equiv.Perm V) c.1 = (f : Equiv.Perm V) c.1)
    (atNeighbors : ∀ x, m.mol.Adj c.1 x → (e : Equiv.Perm V) x = (f : Equiv.Perm V) x) :
    relativeSign m cfg e c = relativeSign m cfg f c := by
  have centers : m.centerPerm e c = m.centerPerm f c := Subtype.ext atCenter
  have frames : m.ligandPermAt e c = m.ligandPermAt f c := by
    apply Equiv.ext
    intro i
    apply m.ligandAtomAt_injective (m.centerPerm f c)
    have first := m.ligandAtomAt_ligandPermAt e c i
    rw [centers, atNeighbors _ (m.ligandAtomAt_adj c i)] at first
    exact first.trans (m.ligandAtomAt_ligandPermAt f c i).symm
  unfold relativeSign transportedSign
  rw [centers, frames]

theorem relativeSign_one (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    relativeSign m cfg (1 : m.Aut) c = 1 := by
  simpa only [relativeSign, transportedSign, centerPerm_one_apply,
    MultiCenterMolecule.ligandPermAt_one, permHandedness_one, mul_one]
    using permHandedness_mul_self (cfg c)

/-- Distinct-component exchange uses an isomorphism and its inverse, hence squares to one. -/
theorem exchange_involutive (m : MoleculeGraph V) (B : List V) (a b : V)
    (iso : BoundaryComponentIso m B B a b) (ha : a ∉ B) (hb : b ∉ B)
    (disjoint : ∀ x, ¬ (InComponent m B a x ∧ InComponent m B b x)) :
    Function.Involutive (componentExchangePerm iso ha hb) := by
  intro x
  change componentExchange iso (componentExchange iso x) = x
  by_cases left : InComponent m B a x
  · have right := iso.maps_to x left
    rw [exchange_of_a iso left,
      exchange_of_b iso (fun h => disjoint _ ⟨h, right⟩) right]
    exact iso.left_inv x left
  · by_cases right : InComponent m B b x
    · have source := iso.maps_inv x right
      rw [exchange_of_b iso left right, exchange_of_a iso source]
      exact iso.right_inv x right
    · rw [exchange_of_none iso left right, exchange_of_none iso left right]

/-- No target properness premise is needed for the actual inverse exchange. -/
theorem exchange_source_proper_union (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (B : List V) (a b : V) (iso : BoundaryComponentIso m.mol B B a b)
    (ha : a ∉ B) (hb : b ∉ B) (e : m.Aut)
    (actual : (e : Equiv.Perm V) = componentExchangePerm iso ha hb)
    (sourceProper : ∀ c : m.Center, InComponent m.mol B a c.1 → relativeSign m cfg e c = 1) :
    ∀ c : m.Center, InComponent m.mol B a c.1 ∨ InComponent m.mol B b c.1 →
      relativeSign m cfg e c = 1 := by
  intro c member
  rcases member with left | right
  · exact sourceProper c left
  · rcases inComponent_same_or_disjoint ha hb with same | disjoint
    · exact sourceProper c ((same c.1).mpr right)
    · have square : e * e = 1 := by
        apply Subtype.ext
        apply Equiv.ext
        intro x
        change (e : Equiv.Perm V) ((e : Equiv.Perm V) x) = x
        rw [actual]
        exact exchange_involutive m.mol B a b iso ha hb disjoint x
      have image : InComponent m.mol B a (m.centerPerm e c).1 := by
        change InComponent m.mol B a ((e : Equiv.Perm V) c.1)
        rw [actual, componentExchangePerm_apply,
          exchange_of_b iso (fun h => disjoint _ ⟨h, right⟩) right]
        exact iso.maps_inv c.1 right
      have product := relativeSign_mul m cfg e e c
      rw [square, relativeSign_one, sourceProper _ image, one_mul] at product
      exact product.symm

/-- Pointwise boundary fixation transports the entire residual connected component. -/
theorem inComponent_map (m : MoleculeGraph V) (B : List V) (e : m.Aut)
    (fixed : ∀ x ∈ B, (e : Equiv.Perm V) x = x) {a x : V}
    (member : InComponent m B a x) :
    InComponent m B ((e : Equiv.Perm V) a) ((e : Equiv.Perm V) x) := by
  have outside {y : V} (hy : y ∉ B) : (e : Equiv.Perm V) y ∉ B := by
    intro image
    have same : (e : Equiv.Perm V) y = y := (e : Equiv.Perm V).injective (fixed _ image)
    exact hy (same ▸ image)
  let f : residualGraph m B →g residualGraph m B :=
    { toFun := (e : Equiv.Perm V)
      map_rel' := by
        intro x y h
        exact ⟨outside h.1, outside h.2.1,
          (MoleculeGraph.Aut.adj_iff m e x y).mpr h.2.2⟩ }
  exact ⟨outside member.1, member.2.map f⟩

/-- Restrict an actual automorphism to one boundary-preserving component isomorphism. -/
def restrictAut (m : MultiCenterMolecule V) (B : List V) (a b : V) (g : m.Aut)
    (fixed : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (entry : (g : Equiv.Perm V) a = b) : BoundaryComponentIso m.mol B B a b := by
  let graphAut : m.mol.Aut := ⟨g, MultiCenterMolecule.Aut.mem_molAut m g⟩
  have inverseFixed : ∀ x ∈ B, ((g : Equiv.Perm V)⁻¹) x = x := by
    intro x member
    apply (g : Equiv.Perm V).injective
    simpa using (fixed x member).symm
  have inverseEntry : ((g : Equiv.Perm V)⁻¹) b = a := by
    rw [← entry]
    exact (g : Equiv.Perm V).symm_apply_apply a
  refine
    { len_eq := rfl
      toFun := (g : Equiv.Perm V)
      invFun := fun x => (g : Equiv.Perm V).symm x
      left_inv := fun x _ => (g : Equiv.Perm V).symm_apply_apply x
      right_inv := fun x _ => (g : Equiv.Perm V).apply_symm_apply x
      maps_to := ?_
      maps_inv := ?_
      entry := entry
      inv_entry := inverseEntry
      atomZ_eq := fun x _ => MoleculeGraph.Aut.atomZ_eq m.mol graphAut x
      atomMass_eq := fun x _ => MoleculeGraph.Aut.atomMass_eq m.mol graphAut x
      formalCharge_eq := fun x _ => MoleculeGraph.Aut.formalCharge_eq m.mol graphAut x
      bond_eq := fun x y _ _ => MoleculeGraph.Aut.bond_eq m.mol graphAut x y
      boundary_eq := ?_ }
  · intro x member
    have mapped := inComponent_map m.mol B graphAut fixed member
    change InComponent m.mol B ((g : Equiv.Perm V) a) ((g : Equiv.Perm V) x) at mapped
    simpa only [entry] using mapped
  · intro x member
    have mapped := inComponent_map m.mol B graphAut⁻¹ inverseFixed member
    change InComponent m.mol B (((g : Equiv.Perm V)⁻¹) b) (((g : Equiv.Perm V)⁻¹) x) at mapped
    simpa only [inverseEntry] using mapped
  · intro x _ i hi
    have bond := MoleculeGraph.Aut.bond_eq m.mol graphAut x (B.get ⟨i, hi⟩)
    change m.mol.bond ((g : Equiv.Perm V) x) ((g : Equiv.Perm V) (B.get ⟨i, hi⟩)) =
      m.mol.bond x (B.get ⟨i, hi⟩) at bond
    rw [fixed _ (List.get_mem B ⟨i, hi⟩)] at bond
    exact bond

/-- Rebuild an exchange after correcting its source map. Center preservation is derived
from the original automorphism and its inverse on the two respective components. -/
def reextendedAut (m : MultiCenterMolecule V) (B : List V) (a b : V) (g : m.Aut)
    (fixed : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (entry : (g : Equiv.Perm V) a = b) (ha : a ∉ B) (hb : b ∉ B) : m.Aut := by
  let iso := restrictAut m B a b g fixed entry
  refine ⟨componentExchangePerm iso ha hb,
    componentExchangePerm_isAutomorphism iso ha hb, ?_⟩
  intro x
  change x ∈ m.centers ↔ componentExchange iso x ∈ m.centers
  by_cases left : InComponent m.mol B a x
  · rw [exchange_of_a iso left]
    exact MultiCenterMolecule.Aut.mem_centers_iff m g x
  · by_cases right : InComponent m.mol B b x
    · rw [exchange_of_b iso left right]
      exact MultiCenterMolecule.Aut.mem_centers_iff m g⁻¹ x
    · rw [exchange_of_none iso left right]

theorem reextended_eq_source (m : MultiCenterMolecule V) (B : List V) (a b : V) (g : m.Aut)
    (fixed : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (entry : (g : Equiv.Perm V) a = b) (ha : a ∉ B) (hb : b ∉ B)
    (x : V) (member : InComponent m.mol B a x) :
    (reextendedAut m B a b g fixed entry ha hb : Equiv.Perm V) x = (g : Equiv.Perm V) x :=
  exchange_of_a (restrictAut m B a b g fixed entry) member

/-- Every fixed atom of the source-corrected automorphism remains fixed, including any
inherited reference. This is stronger than boundary fixation alone. -/
theorem reextended_preserves_fixed (m : MultiCenterMolecule V) (B : List V) (a b : V) (g : m.Aut)
    (fixed : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (entry : (g : Equiv.Perm V) a = b) (ha : a ∉ B) (hb : b ∉ B)
    (x : V) (fixesX : (g : Equiv.Perm V) x = x) :
    (reextendedAut m B a b g fixed entry ha hb : Equiv.Perm V) x = x := by
  let iso := restrictAut m B a b g fixed entry
  change componentExchange iso x = x
  by_cases left : InComponent m.mol B a x
  · exact (exchange_of_a iso left).trans fixesX
  · by_cases right : InComponent m.mol B b x
    · rw [exchange_of_b iso left right]
      change ((g : Equiv.Perm V)⁻¹) x = x
      apply (g : Equiv.Perm V).injective
      simpa using fixesX.symm
    · exact exchange_of_none iso left right

theorem reextended_support (m : MultiCenterMolecule V) (B : List V) (a b : V) (g : m.Aut)
    (fixed : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (entry : (g : Equiv.Perm V) a = b) (ha : a ∉ B) (hb : b ∉ B) :
    (∀ x ∈ B, (reextendedAut m B a b g fixed entry ha hb : Equiv.Perm V) x = x) ∧
    (∀ x, ¬ InComponent m.mol B a x → ¬ InComponent m.mol B b x →
      (reextendedAut m B a b g fixed entry ha hb : Equiv.Perm V) x = x) :=
  exchange_support (restrictAut m B a b g fixed entry) ha hb

/-- The source center's entire physical frame is retained. Boundary neighbors are fixed;
all other neighbors belong to its source residual component. -/
theorem reextended_relativeSign_source (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (B : List V) (a b : V) (g : m.Aut)
    (fixed : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (entry : (g : Equiv.Perm V) a = b) (ha : a ∉ B) (hb : b ∉ B)
    (c : m.Center) (member : InComponent m.mol B a c.1) :
    relativeSign m cfg (reextendedAut m B a b g fixed entry ha hb) c = relativeSign m cfg g c := by
  apply relativeSign_congr
  · exact reextended_eq_source m B a b g fixed entry ha hb c.1 member
  · intro x adjacent
    by_cases boundary : x ∈ B
    · exact (reextended_preserves_fixed m B a b g fixed entry ha hb x (fixed x boundary)).trans
        (fixed x boundary).symm
    · exact reextended_eq_source m B a b g fixed entry ha hb x
        (inComponent_of_bond_pos member boundary adjacent)

/-- Re-extension turns actual source properness into properness on both affected components.
Nothing is assumed about the original automorphism's target-side physical signs. -/
theorem reextended_proper_union (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (B : List V) (a b : V) (g : m.Aut)
    (fixed : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (entry : (g : Equiv.Perm V) a = b) (ha : a ∉ B) (hb : b ∉ B)
    (sourceProper : ∀ c : m.Center, InComponent m.mol B a c.1 → relativeSign m cfg g c = 1) :
    ∀ c : m.Center, InComponent m.mol B a c.1 ∨ InComponent m.mol B b c.1 →
      relativeSign m cfg (reextendedAut m B a b g fixed entry ha hb) c = 1 := by
  apply exchange_source_proper_union m cfg B a b (restrictAut m B a b g fixed entry) ha hb
    (reextendedAut m B a b g fixed entry ha hb) rfl
  intro c member
  exact (reextended_relativeSign_source m cfg B a b g fixed entry ha hb c member).trans
    (sourceProper c member)

/-- At the deleted current center, two retained neighboring fixes and a moved attachment
derive local oddness of this SAME re-extension. The boundary center is not included in the
source/target properness conclusions above. -/
theorem reextended_local_odd (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (B : List V) (a b : V) (g : m.Aut)
    (fixed : ∀ x ∈ B, (g : Equiv.Perm V) x = x)
    (entry : (g : Equiv.Perm V) a = b) (ha : a ∉ B) (hb : b ∉ B)
    (c : m.Center) (boundary : c.1 ∈ B)
    (parent reference : V) (different : parent ≠ reference)
    (parentAdjacent : m.mol.Adj c.1 parent) (referenceAdjacent : m.mol.Adj c.1 reference)
    (parentFixed : (g : Equiv.Perm V) parent = parent)
    (referenceFixed : (g : Equiv.Perm V) reference = reference)
    (attachment : m.mol.Adj c.1 a) (distinct : a ≠ b) :
    m.centerPerm (reextendedAut m B a b g fixed entry ha hb) c = c ∧
      permHandedness (m.ligandPermAt (reextendedAut m B a b g fixed entry ha hb) c) = -1 ∧
      relativeSign m cfg (reextendedAut m B a b g fixed entry ha hb) c = -1 := by
  have moved : (reextendedAut m B a b g fixed entry ha hb : Equiv.Perm V) a = b :=
    (reextended_eq_source m B a b g fixed entry ha hb a (inComponent_self m.mol ha)).trans entry
  obtain ⟨center, odd⟩ := LocalizedChemicalRingTwoFixedNeighbors.local_odd_of_two_fixed_neighbors
    m (reextendedAut m B a b g fixed entry ha hb) c
    (reextended_preserves_fixed m B a b g fixed entry ha hb c.1 (fixed c.1 boundary))
    parent reference different parentAdjacent referenceAdjacent
    (reextended_preserves_fixed m B a b g fixed entry ha hb parent parentFixed)
    (reextended_preserves_fixed m B a b g fixed entry ha hb reference referenceFixed)
    ⟨a, attachment, by rw [moved]; exact Ne.symm distinct⟩
  refine ⟨center, odd, ?_⟩
  unfold relativeSign transportedSign
  rw [center, odd]
  have square : m.configurationSign cfg c * m.configurationSign cfg c = 1 :=
    permHandedness_mul_self (cfg c)
  nlinarith

end
end TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.relativeSign_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.relativeSign_one
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.exchange_involutive
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.exchange_source_proper_union
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.inComponent_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.restrictAut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.reextendedAut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.reextended_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.reextended_preserves_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.reextended_support
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.reextended_relativeSign_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.reextended_proper_union
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness.reextended_local_odd
