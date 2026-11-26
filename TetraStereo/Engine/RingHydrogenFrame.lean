import TetraStereo.Engine.RingHydrogenCompletion
import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation

set_option autoImplicit false
namespace TetraStereo.Engine.RingHydrogenCompletion
open OneCenter RationalTetrahedralPermutation CertifiedLocalizedCIPInput

theorem normSq_pos {a : Point} (h : a ≠ zeroVector) : 0 < normSq a := by
  obtain ⟨x, y, z⟩ := a
  have hx := mul_self_nonneg x
  have hy := mul_self_nonneg y
  have hz := mul_self_nonneg z
  show 0 < x * x + y * y + z * z
  rcases lt_or_eq_of_le (add_nonneg (add_nonneg hx hy) hz) with positive | zero
  · exact positive
  · exfalso
    apply h
    have x0 : x = 0 := mul_self_eq_zero.mp (by linarith)
    have y0 : y = 0 := mul_self_eq_zero.mp (by linarith)
    have z0 : z = 0 := mul_self_eq_zero.mp (by linarith)
    subst x0 y0 z0
    rfl

/-- The upper completion is the in-plane generated position plus the cross normal. -/
theorem pairPlus_eq_opposite_add (c p1 p2 : Point) :
    pairPlus c p1 p2 = vadd (opposite c [p1, p2]) (vcross (vsub p1 c) (vsub p2 c)) := by
  simp only [pairPlus, opposite, List.foldl_cons, List.foldl_nil, vadd, vsub, vcross]
  congr 1 <;> ring

/-- The lower completion is the in-plane generated position minus the cross normal. -/
theorem pairMinus_eq_opposite_sub (c p1 p2 : Point) :
    pairMinus c p1 p2 = vsub (opposite c [p1, p2]) (vcross (vsub p1 c) (vsub p2 c)) := by
  simp only [pairMinus, opposite, List.foldl_cons, List.foldl_nil, vadd, vsub, vcross]
  congr 1 <;> ring

/-- The in-plane generated position has no hand against the two retained neighbours. -/
theorem orientedVolume_opposite_pair (c p1 p2 : Point) :
    CartesianPoint3.orientedVolume p1 p2 (opposite c [p1, p2]) c = 0 := by
  simp only [CartesianPoint3.orientedVolume, opposite, List.foldl_cons, List.foldl_nil, vadd, vsub]
  ring

theorem orientedVolume_pairPlus (c p1 p2 : Point) :
    CartesianPoint3.orientedVolume p1 p2 (pairPlus c p1 p2) c =
      normSq (vcross (vsub p1 c) (vsub p2 c)) := by
  simp only [CartesianPoint3.orientedVolume, pairPlus, normSq, vdot, vadd, vsub, vcross]
  ring

theorem orientedVolume_pairMinus (c p1 p2 : Point) :
    CartesianPoint3.orientedVolume p1 p2 (pairMinus c p1 p2) c =
      -normSq (vcross (vsub p1 c) (vsub p2 c)) := by
  simp only [CartesianPoint3.orientedVolume, pairMinus, normSq, vdot, vsub, vcross]
  ring

private def scalePoint (k : ℚ) (p : Point) : Point := ⟨k*p.x,k*p.y,k*p.z⟩

/-- Affine coordinates of the central atom in the explicit ligand frame. The
coefficient of the third ligand is the remaining weight. -/
def ligandCombination (p₁ p₂ p₃ h : Point) (a b w : ℚ) : Point :=
  vadd p₃ (vadd (scalePoint a (vsub p₁ p₃))
    (vadd (scalePoint b (vsub p₂ p₃)) (scalePoint w (vsub h p₃))))

/-- When the hydrogen has positive barycentric weight, its explicit position and the
inferred position give the same descriptor in every ligand order, including zero
volume. A center inside its ligand tetrahedron has positive weight at every vertex. -/
theorem single_descriptor_of_positive_weight (p₁ p₂ p₃ h : Point)
    (a b w : ℚ) (hw : 0 < w) (π : Equiv.Perm (Fin 4)) :
    let c := ligandCombination p₁ p₂ p₃ h a b w
    descriptorOfOrientedVolume? (permutedOrientedVolume p₁ p₂ p₃ (single c [p₁,p₂,p₃]) π) =
      descriptorOfOrientedVolume? (permutedOrientedVolume p₁ p₂ p₃ h π) := by
  let c := ligandCombination p₁ p₂ p₃ h a b w
  have base : CartesianPoint3.orientedVolume p₁ p₂ p₃ c = w * CartesianPoint3.orientedVolume p₁ p₂ p₃ h := by
    simp only [c,ligandCombination,scalePoint,vadd,vsub,CartesianPoint3.orientedVolume]
    ring
  have volume : permutedOrientedVolume p₁ p₂ p₃ (single c [p₁,p₂,p₃]) π =
      (4 * w) * permutedOrientedVolume p₁ p₂ p₃ h π := by
    rw [permutedOrientedVolume_eq_if_permutationIsEven,permutedOrientedVolume_eq_if_permutationIsEven,
      orientedVolume_single_three,base]
    split <;> ring
  change descriptorOfOrientedVolume? (permutedOrientedVolume _ _ _ (single c _) _) = _
  rw [volume]
  have positive : 0 < 4 * w := by positivity
  simp [descriptorOfOrientedVolume?,mul_neg_iff,positive,not_lt_of_ge positive.le,mul_pos_iff_of_pos_left positive]

/-- At a pyramidal site with two retained bonds, the generated single hydrogen
lies in their plane. The coordinate readback therefore has no hand. -/
theorem pyramidal_single_none (c p q : Point) :
    descriptorOfPriorityOrderedPoints? [p,q,single c [p,q],c] = none := by
  exact (descriptorOfOrientedVolume?_eq_none_iff _).mpr (orientedVolume_opposite_pair c p q)

/-- Any two noncollinear retained bonds admit explicit hydrogen positions of both
hands. No descriptor inferred only from these three retained points agrees with all
nondegenerate placements of the omitted hydrogen. -/
theorem pyramidal_erasure_loses_hand (c p q : Point)
    (noncollinear : 0 < normSq (vcross (vsub p c) (vsub q c))) :
    ∀ predicted : Option RS, ∃ h : Point,
      descriptorOfPriorityOrderedPoints? [p,q,h,c] ≠ none ∧
      descriptorOfPriorityOrderedPoints? [p,q,h,c] ≠ predicted := by
  have s : descriptorOfPriorityOrderedPoints? [p,q,pairPlus c p q,c] = some .S :=
    (descriptorOfOrientedVolume?_eq_some_S_iff _).mpr ((orientedVolume_pairPlus c p q) ▸ noncollinear)
  have r : descriptorOfPriorityOrderedPoints? [p,q,pairMinus c p q,c] = some .R :=
    (descriptorOfOrientedVolume?_eq_some_R_iff _).mpr ((orientedVolume_pairMinus c p q) ▸ neg_neg_of_pos noncollinear)
  intro predicted
  by_cases same : predicted = some .S
  · exact ⟨pairMinus c p q, by simp [r], by simp [r,same]⟩
  · exact ⟨pairPlus c p q, by simp [s], by rw [s]; exact Ne.symm same⟩

/-- Every nondegenerate explicit P–H position has one of the two generated readings
in all permutations of its local frame. The same choice serves every occurrence’s
ligand order. -/
theorem explicit_pyramidal_represented (c p q h : Point)
    (hn : vcross (vsub p c) (vsub q c) ≠ zeroVector)
    (hv : CartesianPoint3.orientedVolume p q h c ≠ 0) :
    ∃ representative ∈ [pairPlus c p q, pairMinus c p q], ∀ π : Equiv.Perm (Fin 4),
      descriptorOfOrientedVolume? (permutedOrientedVolume p q representative c π) =
        descriptorOfOrientedVolume? (permutedOrientedVolume p q h c π) := by
  have n := normSq_pos hn
  rcases lt_or_gt_of_ne hv with negative | positive
  · refine ⟨pairMinus c p q,by simp,fun π => ?_⟩
    rw [permutedOrientedVolume_eq_if_permutationIsEven,permutedOrientedVolume_eq_if_permutationIsEven,
      orientedVolume_pairMinus]
    split <;> simp [descriptorOfOrientedVolume?,n,negative,not_lt_of_ge n.le,not_lt_of_ge negative.le]
  · refine ⟨pairPlus c p q,by simp,fun π => ?_⟩
    rw [permutedOrientedVolume_eq_if_permutationIsEven,permutedOrientedVolume_eq_if_permutationIsEven,
      orientedVolume_pairPlus]
    split <;> simp [descriptorOfOrientedVolume?,n,positive,not_lt_of_ge n.le,not_lt_of_ge positive.le]

end TetraStereo.Engine.RingHydrogenCompletion
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.single_descriptor_of_positive_weight
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.pyramidal_erasure_loses_hand
assert_kernel_only TetraStereo.Engine.RingHydrogenCompletion.explicit_pyramidal_represented
