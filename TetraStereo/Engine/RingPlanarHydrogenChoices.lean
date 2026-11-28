import Batteries.Tactic.OpenPrivate
import TetraStereo.Engine.RingHydrogenFrame

/-! Geometry of one omitted tetrahedral hydrogen with three fixed neighbours.
The raw coordinate admission test and the stronger condition that the central
atom lie inside the explicit ligand tetrahedron have different consequences
when the central atom lies in the retained neighbours' plane. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPlanarHydrogenChoices
open OneCenter CertifiedLocalizedCIPInput RationalTetrahedralPermutation
open RingHydrogenCompletion
open CartesianPoint3 (orientedVolume)
open private scalePoint from TetraStereo.Engine.RingHydrogenFrame

def normal (p q r : Point) := vcross (vsub q p) (vsub r p)

/-- Moving the hydrogen along the negative normal increases its oriented
volume by the displacement coefficient times the squared normal length. -/
theorem volume_offset (p q r h : Point) (t : ℚ) :
    orientedVolume p q r (vsub h (scalePoint t (normal p q r))) =
      orientedVolume p q r h + t * normSq (normal p q r) := by
  simp only [orientedVolume,normal,scalePoint,normSq,vdot,vsub,vcross]
  ring

/-- An explicitly placed hydrogen attaining the specified signed volume.
The reference position is the current single-hydrogen construction. -/
def atVolume (c p q r : Point) (v : ℚ) : Point :=
  let h := single c [p,q,r]
  vsub h (scalePoint ((v - orientedVolume p q r h) / normSq (normal p q r)) (normal p q r))

theorem volume_at (c p q r : Point) (noncollinear : normal p q r ≠ zeroVector) (v : ℚ) :
    orientedVolume p q r (atVolume c p q r v) = v := by
  unfold atVolume
  rw [volume_offset,div_mul_cancel₀ _ (normSq_pos noncollinear).ne']
  ring

/-- The two explicit representatives give the two ordered-frame hands. -/
theorem two_hands (c p q r : Point) (noncollinear : normal p q r ≠ zeroVector) :
    descriptorOfPriorityOrderedPoints? [p,q,r,atVolume c p q r (-1)] = some .R ∧
    descriptorOfPriorityOrderedPoints? [p,q,r,atVolume c p q r 1] = some .S := by
  simp [descriptorOfPriorityOrderedPoints?,volume_at c p q r noncollinear]

/-- Every nondegenerate fourth position is represented in every priority
ordering by the same choice of one of the two explicit hydrogens. -/
theorem all_orders (c p q r h : Point) (noncollinear : normal p q r ≠ zeroVector)
    (offPlane : orientedVolume p q r h ≠ 0) :
    ∃ v ∈ ([-1,1] : List ℚ), ∀ π : Equiv.Perm (Fin 4),
      descriptorOfOrientedVolume? (permutedOrientedVolume p q r (atVolume c p q r v) π) =
      descriptorOfOrientedVolume? (permutedOrientedVolume p q r h π) := by
  rcases lt_or_gt_of_ne offPlane with neg | pos
  · refine ⟨-1,by simp,fun π => ?_⟩
    rw [permutedOrientedVolume_eq_if_permutationIsEven,permutedOrientedVolume_eq_if_permutationIsEven,
      volume_at c p q r noncollinear]
    split <;> simp [descriptorOfOrientedVolume?,neg,not_lt_of_ge neg.le]
  · refine ⟨1,by simp,fun π => ?_⟩
    rw [permutedOrientedVolume_eq_if_permutationIsEven,permutedOrientedVolume_eq_if_permutationIsEven,
      volume_at c p q r noncollinear]
    split <;> simp [descriptorOfOrientedVolume?,pos,not_lt_of_ge pos.le]

/-- The existing single position gives no hand exactly when the center
is coplanar with the three retained neighbours, for every ligand ordering. -/
theorem single_none_iff (c p q r : Point) (π : Equiv.Perm (Fin 4)) :
    descriptorOfOrientedVolume? (permutedOrientedVolume p q r (single c [p,q,r]) π) = none ↔
      orientedVolume p q r c = 0 := by
  rw [descriptorOfOrientedVolume?_eq_none_iff,permutedOrientedVolume_eq_if_permutationIsEven,
    orientedVolume_single_three]
  split <;> simp

/-- A written isotope with mass number at least two never activates the
equivalent ordinary-hydrogen placement branch. -/
theorem isotope_not_ordinary (m : RawMolecule) (j mass : Nat) (a : AtomSpec)
    (atom : m.atoms[j]? = some a) (label : a.isotope? = some mass) (heavy : 2 ≤ mass) :
    ordinaryHydrogenVertex m j = false := by
  have ne : mass ≠ 1 := by omega
  simp [ordinaryHydrogenVertex,atom,label,ne]

/-- Current raw placement when a site has one omitted hydrogen and none
of its written neighbours is an equivalent ordinary H. A written deuterium
therefore cannot trigger the equivalent-hydrogen normal displacement. -/
theorem raw_single (m : RawMolecule) (g : SpatialConfiguration) (a : Nat) (c p q r : Point)
    (center : g.positions[a]? = some c)
    (neighbours : (neighbors m a).mapM (fun j => g.positions[j]?) = some [p,q,r])
    (noOrdinary : (m.writtenNeighbors a).any (ordinaryHydrogenVertex m) = false) :
    placeAt? m g (a,1) = some [single c [p,q,r]] := by
  simp [placeAt?,center,neighbours,noOrdinary,placed,place]

/-- Positive barycentric weight for H rules out a nondegenerate completion
of a coplanar center. Raw four-ligand coordinate admission alone does not
impose this condition on the central atom. -/
theorem zero_weight_of_flat_center (p q r h : Point) (a b w : ℚ)
    (flat : orientedVolume p q r (ligandCombination p q r h a b w) = 0)
    (offPlane : orientedVolume p q r h ≠ 0) : w = 0 := by
  have law : orientedVolume p q r (ligandCombination p q r h a b w) =
      w * orientedVolume p q r h := by
    simp only [orientedVolume,ligandCombination,scalePoint,vadd,vsub]
    ring
  exact (mul_eq_zero.mp (law.symm.trans flat)).resolve_right offPlane

end TetraStereo.Engine.RingPlanarHydrogenChoices

assert_kernel_only TetraStereo.Engine.RingPlanarHydrogenChoices.volume_at
assert_kernel_only TetraStereo.Engine.RingPlanarHydrogenChoices.two_hands
assert_kernel_only TetraStereo.Engine.RingPlanarHydrogenChoices.all_orders
assert_kernel_only TetraStereo.Engine.RingPlanarHydrogenChoices.single_none_iff
assert_kernel_only TetraStereo.Engine.RingPlanarHydrogenChoices.raw_single
assert_kernel_only TetraStereo.Engine.RingPlanarHydrogenChoices.zero_weight_of_flat_center
