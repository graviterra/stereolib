import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open Rule6HandednessSemantics RationalTetrahedralPermutation

/-- Nondegenerate molecular coordinates supply a descriptor for every genuine ligand order.
Neither a successful geometry computation nor its handedness is a premise.

Source profile: the upstream corrected calibration is used throughout.  `R` is the negative
affine determinant and `S` the positive one; the Cartesian written parity is
negative volume ↔ `clockwise`, positive volume ↔ `anticlockwise` (IUPAC P-9, standard
right-handed frame `x` right, `y` up, `z` toward the viewer).  The symbolic
`RawMolecule.descriptorOfParity` is unchanged. -/
theorem rationalTetrahedralDescriptor_exists_of_permutation
    (point : Fin 4 → CartesianPoint3) (order : List (Fin 4))
    (permutation : order.Perm (List.finRange 4))
    (nonzero : CartesianPoint3.orientedVolume (point 0) (point 1) (point 2) (point 3) ≠ 0) :
    ∃ raw, RationalTetrahedralDescriptor (order.map point) raw := by
  have positionsPermutation : (order.map Fin.val).Perm (List.range 4) := by
    simpa using permutation.map Fin.val
  let ordering := finFourEquivOfPermutationList (order.map Fin.val) positionsPermutation
  have positionsEq : finFourPermutationList ordering = order.map Fin.val :=
    finFourPermutationList_equivOfPermutationList _ positionsPermutation
  have orderEq : order = [ordering 0, ordering 1, ordering 2, ordering 3] := by
    apply List.map_injective_iff.mpr Fin.val_injective
    change order.map Fin.val = finFourPermutationList ordering
    exact positionsEq.symm
  have pointEq : pointVector (point 0) (point 1) (point 2) (point 3) = point := by
    funext i
    fin_cases i <;> rfl
  have reordered : permutedPoints (point 0) (point 1) (point 2) (point 3) ordering =
      order.map point := by
    rw [orderEq]
    simp only [permutedPoints, pointEq, List.map_cons, List.map_nil]
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · -- Negative written-order volume is the `clockwise` carrier in the calibrated convention.
    refine ⟨RawMolecule.descriptorOfParity .clockwise
      (RawMolecule.permutationIsEven (finFourPermutationList ordering)), ?_⟩
    rw [← reordered]
    exact rationalTetrahedralDescriptor_permutedPoints _ _ _ _ ordering .clockwise negative
  · -- Positive written-order volume is the `anticlockwise` carrier.
    refine ⟨RawMolecule.descriptorOfParity .anticlockwise
      (RawMolecule.permutationIsEven (finFourPermutationList ordering)), ?_⟩
    rw [← reordered]
    exact rationalTetrahedralDescriptor_permutedPoints _ _ _ _ ordering .anticlockwise positive

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
